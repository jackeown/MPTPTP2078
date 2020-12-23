%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:42 EST 2020

% Result     : Theorem 13.85s
% Output     : CNFRefutation 13.97s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 411 expanded)
%              Number of leaves         :   24 ( 154 expanded)
%              Depth                    :   15
%              Number of atoms          :  257 (1846 expanded)
%              Number of equality atoms :    1 (  32 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => ! [D] :
                    ( v1_relat_1(D)
                   => ( ( r1_tarski(A,B)
                        & r1_tarski(C,D) )
                     => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_28,plain,(
    ~ r1_tarski(k5_relat_1('#skF_9','#skF_11'),k5_relat_1('#skF_10','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [A_117,B_118] :
      ( v1_relat_1(k5_relat_1(A_117,B_118))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_1,B_11] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),A_1)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    ! [C_137,D_138,B_139,A_140] :
      ( r2_hidden(k4_tarski(C_137,D_138),B_139)
      | ~ r2_hidden(k4_tarski(C_137,D_138),A_140)
      | ~ r1_tarski(A_140,B_139)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    ! [A_1,B_11,B_139] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),B_139)
      | ~ r1_tarski(A_1,B_139)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_38,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_179,plain,(
    ! [D_169,B_170,A_171,E_172] :
      ( r2_hidden(k4_tarski(D_169,'#skF_3'(B_170,A_171,k5_relat_1(A_171,B_170),D_169,E_172)),A_171)
      | ~ r2_hidden(k4_tarski(D_169,E_172),k5_relat_1(A_171,B_170))
      | ~ v1_relat_1(k5_relat_1(A_171,B_170))
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [C_16,D_17,B_11,A_1] :
      ( r2_hidden(k4_tarski(C_16,D_17),B_11)
      | ~ r2_hidden(k4_tarski(C_16,D_17),A_1)
      | ~ r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_185,plain,(
    ! [B_11,A_171,D_169,B_170,E_172] :
      ( r2_hidden(k4_tarski(D_169,'#skF_3'(B_170,A_171,k5_relat_1(A_171,B_170),D_169,E_172)),B_11)
      | ~ r1_tarski(A_171,B_11)
      | ~ r2_hidden(k4_tarski(D_169,E_172),k5_relat_1(A_171,B_170))
      | ~ v1_relat_1(k5_relat_1(A_171,B_170))
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(A_171) ) ),
    inference(resolution,[status(thm)],[c_179,c_2])).

tff(c_254,plain,(
    ! [B_188,A_189,D_190,E_191] :
      ( r2_hidden(k4_tarski('#skF_3'(B_188,A_189,k5_relat_1(A_189,B_188),D_190,E_191),E_191),B_188)
      | ~ r2_hidden(k4_tarski(D_190,E_191),k5_relat_1(A_189,B_188))
      | ~ v1_relat_1(k5_relat_1(A_189,B_188))
      | ~ v1_relat_1(B_188)
      | ~ v1_relat_1(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [B_70,F_113,D_109,E_110,A_18] :
      ( r2_hidden(k4_tarski(D_109,E_110),k5_relat_1(A_18,B_70))
      | ~ r2_hidden(k4_tarski(F_113,E_110),B_70)
      | ~ r2_hidden(k4_tarski(D_109,F_113),A_18)
      | ~ v1_relat_1(k5_relat_1(A_18,B_70))
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_881,plain,(
    ! [B_393,D_397,A_396,A_392,E_394,D_395] :
      ( r2_hidden(k4_tarski(D_397,E_394),k5_relat_1(A_392,B_393))
      | ~ r2_hidden(k4_tarski(D_397,'#skF_3'(B_393,A_396,k5_relat_1(A_396,B_393),D_395,E_394)),A_392)
      | ~ v1_relat_1(k5_relat_1(A_392,B_393))
      | ~ v1_relat_1(A_392)
      | ~ r2_hidden(k4_tarski(D_395,E_394),k5_relat_1(A_396,B_393))
      | ~ v1_relat_1(k5_relat_1(A_396,B_393))
      | ~ v1_relat_1(B_393)
      | ~ v1_relat_1(A_396) ) ),
    inference(resolution,[status(thm)],[c_254,c_20])).

tff(c_1230,plain,(
    ! [D_409,B_408,B_407,A_410,E_406] :
      ( r2_hidden(k4_tarski(D_409,E_406),k5_relat_1(B_408,B_407))
      | ~ v1_relat_1(k5_relat_1(B_408,B_407))
      | ~ v1_relat_1(B_408)
      | ~ r1_tarski(A_410,B_408)
      | ~ r2_hidden(k4_tarski(D_409,E_406),k5_relat_1(A_410,B_407))
      | ~ v1_relat_1(k5_relat_1(A_410,B_407))
      | ~ v1_relat_1(B_407)
      | ~ v1_relat_1(A_410) ) ),
    inference(resolution,[status(thm)],[c_185,c_881])).

tff(c_1238,plain,(
    ! [D_409,E_406,B_407] :
      ( r2_hidden(k4_tarski(D_409,E_406),k5_relat_1('#skF_10',B_407))
      | ~ v1_relat_1(k5_relat_1('#skF_10',B_407))
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(k4_tarski(D_409,E_406),k5_relat_1('#skF_9',B_407))
      | ~ v1_relat_1(k5_relat_1('#skF_9',B_407))
      | ~ v1_relat_1(B_407)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_1230])).

tff(c_1442,plain,(
    ! [D_414,E_415,B_416] :
      ( r2_hidden(k4_tarski(D_414,E_415),k5_relat_1('#skF_10',B_416))
      | ~ v1_relat_1(k5_relat_1('#skF_10',B_416))
      | ~ r2_hidden(k4_tarski(D_414,E_415),k5_relat_1('#skF_9',B_416))
      | ~ v1_relat_1(k5_relat_1('#skF_9',B_416))
      | ~ v1_relat_1(B_416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1238])).

tff(c_4,plain,(
    ! [A_1,B_11] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),B_11)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1886,plain,(
    ! [A_440,B_441] :
      ( r1_tarski(A_440,k5_relat_1('#skF_10',B_441))
      | ~ v1_relat_1(A_440)
      | ~ v1_relat_1(k5_relat_1('#skF_10',B_441))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_440,k5_relat_1('#skF_10',B_441)),'#skF_2'(A_440,k5_relat_1('#skF_10',B_441))),k5_relat_1('#skF_9',B_441))
      | ~ v1_relat_1(k5_relat_1('#skF_9',B_441))
      | ~ v1_relat_1(B_441) ) ),
    inference(resolution,[status(thm)],[c_1442,c_4])).

tff(c_2005,plain,(
    ! [B_445,A_446] :
      ( ~ v1_relat_1(k5_relat_1('#skF_10',B_445))
      | ~ v1_relat_1(k5_relat_1('#skF_9',B_445))
      | ~ v1_relat_1(B_445)
      | ~ r1_tarski(A_446,k5_relat_1('#skF_9',B_445))
      | r1_tarski(A_446,k5_relat_1('#skF_10',B_445))
      | ~ v1_relat_1(A_446) ) ),
    inference(resolution,[status(thm)],[c_53,c_1886])).

tff(c_2050,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_10','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_12'))
    | ~ v1_relat_1('#skF_12')
    | ~ r1_tarski(k5_relat_1('#skF_9','#skF_11'),k5_relat_1('#skF_9','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_11')) ),
    inference(resolution,[status(thm)],[c_2005,c_28])).

tff(c_2076,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_10','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_12'))
    | ~ r1_tarski(k5_relat_1('#skF_9','#skF_11'),k5_relat_1('#skF_9','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2050])).

tff(c_2077,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_9','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_2076])).

tff(c_2080,plain,
    ( ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_2077])).

tff(c_2084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_2080])).

tff(c_2086,plain,(
    v1_relat_1(k5_relat_1('#skF_9','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_2076])).

tff(c_2085,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_9','#skF_11'),k5_relat_1('#skF_9','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_10','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_2076])).

tff(c_2146,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_10','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_2085])).

tff(c_2149,plain,
    ( ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_26,c_2146])).

tff(c_2153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_2149])).

tff(c_2155,plain,(
    v1_relat_1(k5_relat_1('#skF_10','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_2085])).

tff(c_30,plain,(
    r1_tarski('#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_54,plain,(
    ! [A_141,B_142,B_143] :
      ( r2_hidden(k4_tarski('#skF_1'(A_141,B_142),'#skF_2'(A_141,B_142)),B_143)
      | ~ r1_tarski(A_141,B_143)
      | r1_tarski(A_141,B_142)
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_63,plain,(
    ! [A_144,B_145,B_146,B_147] :
      ( r2_hidden(k4_tarski('#skF_1'(A_144,B_145),'#skF_2'(A_144,B_145)),B_146)
      | ~ r1_tarski(B_147,B_146)
      | ~ v1_relat_1(B_147)
      | ~ r1_tarski(A_144,B_147)
      | r1_tarski(A_144,B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_67,plain,(
    ! [A_144,B_145] :
      ( r2_hidden(k4_tarski('#skF_1'(A_144,B_145),'#skF_2'(A_144,B_145)),'#skF_12')
      | ~ v1_relat_1('#skF_11')
      | ~ r1_tarski(A_144,'#skF_11')
      | r1_tarski(A_144,B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_30,c_63])).

tff(c_73,plain,(
    ! [A_144,B_145] :
      ( r2_hidden(k4_tarski('#skF_1'(A_144,B_145),'#skF_2'(A_144,B_145)),'#skF_12')
      | ~ r1_tarski(A_144,'#skF_11')
      | r1_tarski(A_144,B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_67])).

tff(c_88,plain,(
    ! [A_152,B_150,D_153,F_151,E_154] :
      ( r2_hidden(k4_tarski(D_153,E_154),k5_relat_1(A_152,B_150))
      | ~ r2_hidden(k4_tarski(F_151,E_154),B_150)
      | ~ r2_hidden(k4_tarski(D_153,F_151),A_152)
      | ~ v1_relat_1(k5_relat_1(A_152,B_150))
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [D_153,A_144,B_145,A_152] :
      ( r2_hidden(k4_tarski(D_153,'#skF_2'(A_144,B_145)),k5_relat_1(A_152,'#skF_12'))
      | ~ r2_hidden(k4_tarski(D_153,'#skF_1'(A_144,B_145)),A_152)
      | ~ v1_relat_1(k5_relat_1(A_152,'#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ v1_relat_1(A_152)
      | ~ r1_tarski(A_144,'#skF_11')
      | r1_tarski(A_144,B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_73,c_88])).

tff(c_97,plain,(
    ! [D_153,A_144,B_145,A_152] :
      ( r2_hidden(k4_tarski(D_153,'#skF_2'(A_144,B_145)),k5_relat_1(A_152,'#skF_12'))
      | ~ r2_hidden(k4_tarski(D_153,'#skF_1'(A_144,B_145)),A_152)
      | ~ v1_relat_1(k5_relat_1(A_152,'#skF_12'))
      | ~ v1_relat_1(A_152)
      | ~ r1_tarski(A_144,'#skF_11')
      | r1_tarski(A_144,B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_90])).

tff(c_1910,plain,(
    ! [A_144] :
      ( ~ v1_relat_1(k5_relat_1('#skF_10','#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ r2_hidden(k4_tarski('#skF_1'(A_144,k5_relat_1('#skF_10','#skF_12')),'#skF_1'(A_144,k5_relat_1('#skF_10','#skF_12'))),'#skF_9')
      | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_12'))
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(A_144,'#skF_11')
      | r1_tarski(A_144,k5_relat_1('#skF_10','#skF_12'))
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_97,c_1886])).

tff(c_1944,plain,(
    ! [A_144] :
      ( ~ v1_relat_1(k5_relat_1('#skF_10','#skF_12'))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_144,k5_relat_1('#skF_10','#skF_12')),'#skF_1'(A_144,k5_relat_1('#skF_10','#skF_12'))),'#skF_9')
      | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_12'))
      | ~ r1_tarski(A_144,'#skF_11')
      | r1_tarski(A_144,k5_relat_1('#skF_10','#skF_12'))
      | ~ v1_relat_1(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_1910])).

tff(c_2289,plain,(
    ! [A_144] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_144,k5_relat_1('#skF_10','#skF_12')),'#skF_1'(A_144,k5_relat_1('#skF_10','#skF_12'))),'#skF_9')
      | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_12'))
      | ~ r1_tarski(A_144,'#skF_11')
      | r1_tarski(A_144,k5_relat_1('#skF_10','#skF_12'))
      | ~ v1_relat_1(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2155,c_1944])).

tff(c_2290,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_9','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_2289])).

tff(c_2361,plain,
    ( ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_2290])).

tff(c_2365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_2361])).

tff(c_2367,plain,(
    v1_relat_1(k5_relat_1('#skF_9','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_2289])).

tff(c_24,plain,(
    ! [D_109,B_70,A_18,E_110] :
      ( r2_hidden(k4_tarski(D_109,'#skF_3'(B_70,A_18,k5_relat_1(A_18,B_70),D_109,E_110)),A_18)
      | ~ r2_hidden(k4_tarski(D_109,E_110),k5_relat_1(A_18,B_70))
      | ~ v1_relat_1(k5_relat_1(A_18,B_70))
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_301,plain,(
    ! [B_209,D_210,E_208,A_211,B_207] :
      ( r2_hidden(k4_tarski('#skF_3'(B_207,A_211,k5_relat_1(A_211,B_207),D_210,E_208),E_208),B_209)
      | ~ r1_tarski(B_207,B_209)
      | ~ r2_hidden(k4_tarski(D_210,E_208),k5_relat_1(A_211,B_207))
      | ~ v1_relat_1(k5_relat_1(A_211,B_207))
      | ~ v1_relat_1(B_207)
      | ~ v1_relat_1(A_211) ) ),
    inference(resolution,[status(thm)],[c_254,c_2])).

tff(c_9627,plain,(
    ! [B_1005,D_1001,B_1002,E_1004,A_1003,D_1007,A_1006] :
      ( r2_hidden(k4_tarski(D_1007,E_1004),k5_relat_1(A_1003,B_1005))
      | ~ r2_hidden(k4_tarski(D_1007,'#skF_3'(B_1002,A_1006,k5_relat_1(A_1006,B_1002),D_1001,E_1004)),A_1003)
      | ~ v1_relat_1(k5_relat_1(A_1003,B_1005))
      | ~ v1_relat_1(B_1005)
      | ~ v1_relat_1(A_1003)
      | ~ r1_tarski(B_1002,B_1005)
      | ~ r2_hidden(k4_tarski(D_1001,E_1004),k5_relat_1(A_1006,B_1002))
      | ~ v1_relat_1(k5_relat_1(A_1006,B_1002))
      | ~ v1_relat_1(B_1002)
      | ~ v1_relat_1(A_1006) ) ),
    inference(resolution,[status(thm)],[c_301,c_20])).

tff(c_9693,plain,(
    ! [E_1014,B_1012,D_1013,B_1010,A_1011] :
      ( r2_hidden(k4_tarski(D_1013,E_1014),k5_relat_1(A_1011,B_1012))
      | ~ v1_relat_1(k5_relat_1(A_1011,B_1012))
      | ~ v1_relat_1(B_1012)
      | ~ r1_tarski(B_1010,B_1012)
      | ~ r2_hidden(k4_tarski(D_1013,E_1014),k5_relat_1(A_1011,B_1010))
      | ~ v1_relat_1(k5_relat_1(A_1011,B_1010))
      | ~ v1_relat_1(B_1010)
      | ~ v1_relat_1(A_1011) ) ),
    inference(resolution,[status(thm)],[c_24,c_9627])).

tff(c_9721,plain,(
    ! [D_1013,E_1014,A_1011] :
      ( r2_hidden(k4_tarski(D_1013,E_1014),k5_relat_1(A_1011,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1011,'#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ r2_hidden(k4_tarski(D_1013,E_1014),k5_relat_1(A_1011,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1011,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(A_1011) ) ),
    inference(resolution,[status(thm)],[c_30,c_9693])).

tff(c_9751,plain,(
    ! [D_1015,E_1016,A_1017] :
      ( r2_hidden(k4_tarski(D_1015,E_1016),k5_relat_1(A_1017,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1017,'#skF_12'))
      | ~ r2_hidden(k4_tarski(D_1015,E_1016),k5_relat_1(A_1017,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(A_1017,'#skF_11'))
      | ~ v1_relat_1(A_1017) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_9721])).

tff(c_13221,plain,(
    ! [A_1056,B_1057] :
      ( r2_hidden(k4_tarski('#skF_1'(k5_relat_1(A_1056,'#skF_11'),B_1057),'#skF_2'(k5_relat_1(A_1056,'#skF_11'),B_1057)),k5_relat_1(A_1056,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1056,'#skF_12'))
      | ~ v1_relat_1(A_1056)
      | r1_tarski(k5_relat_1(A_1056,'#skF_11'),B_1057)
      | ~ v1_relat_1(k5_relat_1(A_1056,'#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_6,c_9751])).

tff(c_1535,plain,(
    ! [A_1,B_416] :
      ( r1_tarski(A_1,k5_relat_1('#skF_10',B_416))
      | ~ v1_relat_1(A_1)
      | ~ v1_relat_1(k5_relat_1('#skF_10',B_416))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_1,k5_relat_1('#skF_10',B_416)),'#skF_2'(A_1,k5_relat_1('#skF_10',B_416))),k5_relat_1('#skF_9',B_416))
      | ~ v1_relat_1(k5_relat_1('#skF_9',B_416))
      | ~ v1_relat_1(B_416) ) ),
    inference(resolution,[status(thm)],[c_1442,c_4])).

tff(c_13235,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_10','#skF_12'))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_12'))
    | ~ v1_relat_1('#skF_9')
    | r1_tarski(k5_relat_1('#skF_9','#skF_11'),k5_relat_1('#skF_10','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_9','#skF_11')) ),
    inference(resolution,[status(thm)],[c_13221,c_1535])).

tff(c_13267,plain,(
    r1_tarski(k5_relat_1('#skF_9','#skF_11'),k5_relat_1('#skF_10','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2086,c_40,c_2367,c_34,c_2155,c_13235])).

tff(c_13269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_13267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:11:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.85/6.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.97/6.14  
% 13.97/6.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.97/6.14  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_12
% 13.97/6.14  
% 13.97/6.14  %Foreground sorts:
% 13.97/6.14  
% 13.97/6.14  
% 13.97/6.14  %Background operators:
% 13.97/6.14  
% 13.97/6.14  
% 13.97/6.14  %Foreground operators:
% 13.97/6.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.97/6.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.97/6.14  tff('#skF_11', type, '#skF_11': $i).
% 13.97/6.14  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 13.97/6.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.97/6.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.97/6.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.97/6.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.97/6.14  tff('#skF_10', type, '#skF_10': $i).
% 13.97/6.14  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 13.97/6.14  tff('#skF_9', type, '#skF_9': $i).
% 13.97/6.14  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 13.97/6.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 13.97/6.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.97/6.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.97/6.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.97/6.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.97/6.14  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 13.97/6.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.97/6.14  tff('#skF_12', type, '#skF_12': $i).
% 13.97/6.14  
% 13.97/6.16  tff(f_77, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 13.97/6.16  tff(f_59, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 13.97/6.16  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 13.97/6.16  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 13.97/6.16  tff(c_28, plain, (~r1_tarski(k5_relat_1('#skF_9', '#skF_11'), k5_relat_1('#skF_10', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.97/6.16  tff(c_40, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.97/6.16  tff(c_36, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.97/6.16  tff(c_26, plain, (![A_117, B_118]: (v1_relat_1(k5_relat_1(A_117, B_118)) | ~v1_relat_1(B_118) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.97/6.16  tff(c_34, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.97/6.16  tff(c_6, plain, (![A_1, B_11]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), A_1) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.97/6.16  tff(c_50, plain, (![C_137, D_138, B_139, A_140]: (r2_hidden(k4_tarski(C_137, D_138), B_139) | ~r2_hidden(k4_tarski(C_137, D_138), A_140) | ~r1_tarski(A_140, B_139) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.97/6.16  tff(c_53, plain, (![A_1, B_11, B_139]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), B_139) | ~r1_tarski(A_1, B_139) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_6, c_50])).
% 13.97/6.16  tff(c_38, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.97/6.16  tff(c_32, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.97/6.16  tff(c_179, plain, (![D_169, B_170, A_171, E_172]: (r2_hidden(k4_tarski(D_169, '#skF_3'(B_170, A_171, k5_relat_1(A_171, B_170), D_169, E_172)), A_171) | ~r2_hidden(k4_tarski(D_169, E_172), k5_relat_1(A_171, B_170)) | ~v1_relat_1(k5_relat_1(A_171, B_170)) | ~v1_relat_1(B_170) | ~v1_relat_1(A_171))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.97/6.16  tff(c_2, plain, (![C_16, D_17, B_11, A_1]: (r2_hidden(k4_tarski(C_16, D_17), B_11) | ~r2_hidden(k4_tarski(C_16, D_17), A_1) | ~r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.97/6.16  tff(c_185, plain, (![B_11, A_171, D_169, B_170, E_172]: (r2_hidden(k4_tarski(D_169, '#skF_3'(B_170, A_171, k5_relat_1(A_171, B_170), D_169, E_172)), B_11) | ~r1_tarski(A_171, B_11) | ~r2_hidden(k4_tarski(D_169, E_172), k5_relat_1(A_171, B_170)) | ~v1_relat_1(k5_relat_1(A_171, B_170)) | ~v1_relat_1(B_170) | ~v1_relat_1(A_171))), inference(resolution, [status(thm)], [c_179, c_2])).
% 13.97/6.16  tff(c_254, plain, (![B_188, A_189, D_190, E_191]: (r2_hidden(k4_tarski('#skF_3'(B_188, A_189, k5_relat_1(A_189, B_188), D_190, E_191), E_191), B_188) | ~r2_hidden(k4_tarski(D_190, E_191), k5_relat_1(A_189, B_188)) | ~v1_relat_1(k5_relat_1(A_189, B_188)) | ~v1_relat_1(B_188) | ~v1_relat_1(A_189))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.97/6.16  tff(c_20, plain, (![B_70, F_113, D_109, E_110, A_18]: (r2_hidden(k4_tarski(D_109, E_110), k5_relat_1(A_18, B_70)) | ~r2_hidden(k4_tarski(F_113, E_110), B_70) | ~r2_hidden(k4_tarski(D_109, F_113), A_18) | ~v1_relat_1(k5_relat_1(A_18, B_70)) | ~v1_relat_1(B_70) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.97/6.16  tff(c_881, plain, (![B_393, D_397, A_396, A_392, E_394, D_395]: (r2_hidden(k4_tarski(D_397, E_394), k5_relat_1(A_392, B_393)) | ~r2_hidden(k4_tarski(D_397, '#skF_3'(B_393, A_396, k5_relat_1(A_396, B_393), D_395, E_394)), A_392) | ~v1_relat_1(k5_relat_1(A_392, B_393)) | ~v1_relat_1(A_392) | ~r2_hidden(k4_tarski(D_395, E_394), k5_relat_1(A_396, B_393)) | ~v1_relat_1(k5_relat_1(A_396, B_393)) | ~v1_relat_1(B_393) | ~v1_relat_1(A_396))), inference(resolution, [status(thm)], [c_254, c_20])).
% 13.97/6.16  tff(c_1230, plain, (![D_409, B_408, B_407, A_410, E_406]: (r2_hidden(k4_tarski(D_409, E_406), k5_relat_1(B_408, B_407)) | ~v1_relat_1(k5_relat_1(B_408, B_407)) | ~v1_relat_1(B_408) | ~r1_tarski(A_410, B_408) | ~r2_hidden(k4_tarski(D_409, E_406), k5_relat_1(A_410, B_407)) | ~v1_relat_1(k5_relat_1(A_410, B_407)) | ~v1_relat_1(B_407) | ~v1_relat_1(A_410))), inference(resolution, [status(thm)], [c_185, c_881])).
% 13.97/6.16  tff(c_1238, plain, (![D_409, E_406, B_407]: (r2_hidden(k4_tarski(D_409, E_406), k5_relat_1('#skF_10', B_407)) | ~v1_relat_1(k5_relat_1('#skF_10', B_407)) | ~v1_relat_1('#skF_10') | ~r2_hidden(k4_tarski(D_409, E_406), k5_relat_1('#skF_9', B_407)) | ~v1_relat_1(k5_relat_1('#skF_9', B_407)) | ~v1_relat_1(B_407) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_32, c_1230])).
% 13.97/6.16  tff(c_1442, plain, (![D_414, E_415, B_416]: (r2_hidden(k4_tarski(D_414, E_415), k5_relat_1('#skF_10', B_416)) | ~v1_relat_1(k5_relat_1('#skF_10', B_416)) | ~r2_hidden(k4_tarski(D_414, E_415), k5_relat_1('#skF_9', B_416)) | ~v1_relat_1(k5_relat_1('#skF_9', B_416)) | ~v1_relat_1(B_416))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1238])).
% 13.97/6.16  tff(c_4, plain, (![A_1, B_11]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), B_11) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.97/6.16  tff(c_1886, plain, (![A_440, B_441]: (r1_tarski(A_440, k5_relat_1('#skF_10', B_441)) | ~v1_relat_1(A_440) | ~v1_relat_1(k5_relat_1('#skF_10', B_441)) | ~r2_hidden(k4_tarski('#skF_1'(A_440, k5_relat_1('#skF_10', B_441)), '#skF_2'(A_440, k5_relat_1('#skF_10', B_441))), k5_relat_1('#skF_9', B_441)) | ~v1_relat_1(k5_relat_1('#skF_9', B_441)) | ~v1_relat_1(B_441))), inference(resolution, [status(thm)], [c_1442, c_4])).
% 13.97/6.16  tff(c_2005, plain, (![B_445, A_446]: (~v1_relat_1(k5_relat_1('#skF_10', B_445)) | ~v1_relat_1(k5_relat_1('#skF_9', B_445)) | ~v1_relat_1(B_445) | ~r1_tarski(A_446, k5_relat_1('#skF_9', B_445)) | r1_tarski(A_446, k5_relat_1('#skF_10', B_445)) | ~v1_relat_1(A_446))), inference(resolution, [status(thm)], [c_53, c_1886])).
% 13.97/6.16  tff(c_2050, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_12')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_12')) | ~v1_relat_1('#skF_12') | ~r1_tarski(k5_relat_1('#skF_9', '#skF_11'), k5_relat_1('#skF_9', '#skF_12')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_11'))), inference(resolution, [status(thm)], [c_2005, c_28])).
% 13.97/6.16  tff(c_2076, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_12')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_12')) | ~r1_tarski(k5_relat_1('#skF_9', '#skF_11'), k5_relat_1('#skF_9', '#skF_12')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2050])).
% 13.97/6.16  tff(c_2077, plain, (~v1_relat_1(k5_relat_1('#skF_9', '#skF_11'))), inference(splitLeft, [status(thm)], [c_2076])).
% 13.97/6.16  tff(c_2080, plain, (~v1_relat_1('#skF_11') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_2077])).
% 13.97/6.16  tff(c_2084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_2080])).
% 13.97/6.16  tff(c_2086, plain, (v1_relat_1(k5_relat_1('#skF_9', '#skF_11'))), inference(splitRight, [status(thm)], [c_2076])).
% 13.97/6.16  tff(c_2085, plain, (~r1_tarski(k5_relat_1('#skF_9', '#skF_11'), k5_relat_1('#skF_9', '#skF_12')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_12')) | ~v1_relat_1(k5_relat_1('#skF_10', '#skF_12'))), inference(splitRight, [status(thm)], [c_2076])).
% 13.97/6.16  tff(c_2146, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_12'))), inference(splitLeft, [status(thm)], [c_2085])).
% 13.97/6.16  tff(c_2149, plain, (~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_26, c_2146])).
% 13.97/6.16  tff(c_2153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_2149])).
% 13.97/6.16  tff(c_2155, plain, (v1_relat_1(k5_relat_1('#skF_10', '#skF_12'))), inference(splitRight, [status(thm)], [c_2085])).
% 13.97/6.16  tff(c_30, plain, (r1_tarski('#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.97/6.16  tff(c_54, plain, (![A_141, B_142, B_143]: (r2_hidden(k4_tarski('#skF_1'(A_141, B_142), '#skF_2'(A_141, B_142)), B_143) | ~r1_tarski(A_141, B_143) | r1_tarski(A_141, B_142) | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_6, c_50])).
% 13.97/6.16  tff(c_63, plain, (![A_144, B_145, B_146, B_147]: (r2_hidden(k4_tarski('#skF_1'(A_144, B_145), '#skF_2'(A_144, B_145)), B_146) | ~r1_tarski(B_147, B_146) | ~v1_relat_1(B_147) | ~r1_tarski(A_144, B_147) | r1_tarski(A_144, B_145) | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_54, c_2])).
% 13.97/6.16  tff(c_67, plain, (![A_144, B_145]: (r2_hidden(k4_tarski('#skF_1'(A_144, B_145), '#skF_2'(A_144, B_145)), '#skF_12') | ~v1_relat_1('#skF_11') | ~r1_tarski(A_144, '#skF_11') | r1_tarski(A_144, B_145) | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_30, c_63])).
% 13.97/6.16  tff(c_73, plain, (![A_144, B_145]: (r2_hidden(k4_tarski('#skF_1'(A_144, B_145), '#skF_2'(A_144, B_145)), '#skF_12') | ~r1_tarski(A_144, '#skF_11') | r1_tarski(A_144, B_145) | ~v1_relat_1(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_67])).
% 13.97/6.16  tff(c_88, plain, (![A_152, B_150, D_153, F_151, E_154]: (r2_hidden(k4_tarski(D_153, E_154), k5_relat_1(A_152, B_150)) | ~r2_hidden(k4_tarski(F_151, E_154), B_150) | ~r2_hidden(k4_tarski(D_153, F_151), A_152) | ~v1_relat_1(k5_relat_1(A_152, B_150)) | ~v1_relat_1(B_150) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.97/6.16  tff(c_90, plain, (![D_153, A_144, B_145, A_152]: (r2_hidden(k4_tarski(D_153, '#skF_2'(A_144, B_145)), k5_relat_1(A_152, '#skF_12')) | ~r2_hidden(k4_tarski(D_153, '#skF_1'(A_144, B_145)), A_152) | ~v1_relat_1(k5_relat_1(A_152, '#skF_12')) | ~v1_relat_1('#skF_12') | ~v1_relat_1(A_152) | ~r1_tarski(A_144, '#skF_11') | r1_tarski(A_144, B_145) | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_73, c_88])).
% 13.97/6.16  tff(c_97, plain, (![D_153, A_144, B_145, A_152]: (r2_hidden(k4_tarski(D_153, '#skF_2'(A_144, B_145)), k5_relat_1(A_152, '#skF_12')) | ~r2_hidden(k4_tarski(D_153, '#skF_1'(A_144, B_145)), A_152) | ~v1_relat_1(k5_relat_1(A_152, '#skF_12')) | ~v1_relat_1(A_152) | ~r1_tarski(A_144, '#skF_11') | r1_tarski(A_144, B_145) | ~v1_relat_1(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_90])).
% 13.97/6.16  tff(c_1910, plain, (![A_144]: (~v1_relat_1(k5_relat_1('#skF_10', '#skF_12')) | ~v1_relat_1('#skF_12') | ~r2_hidden(k4_tarski('#skF_1'(A_144, k5_relat_1('#skF_10', '#skF_12')), '#skF_1'(A_144, k5_relat_1('#skF_10', '#skF_12'))), '#skF_9') | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_12')) | ~v1_relat_1('#skF_9') | ~r1_tarski(A_144, '#skF_11') | r1_tarski(A_144, k5_relat_1('#skF_10', '#skF_12')) | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_97, c_1886])).
% 13.97/6.16  tff(c_1944, plain, (![A_144]: (~v1_relat_1(k5_relat_1('#skF_10', '#skF_12')) | ~r2_hidden(k4_tarski('#skF_1'(A_144, k5_relat_1('#skF_10', '#skF_12')), '#skF_1'(A_144, k5_relat_1('#skF_10', '#skF_12'))), '#skF_9') | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_12')) | ~r1_tarski(A_144, '#skF_11') | r1_tarski(A_144, k5_relat_1('#skF_10', '#skF_12')) | ~v1_relat_1(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_1910])).
% 13.97/6.16  tff(c_2289, plain, (![A_144]: (~r2_hidden(k4_tarski('#skF_1'(A_144, k5_relat_1('#skF_10', '#skF_12')), '#skF_1'(A_144, k5_relat_1('#skF_10', '#skF_12'))), '#skF_9') | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_12')) | ~r1_tarski(A_144, '#skF_11') | r1_tarski(A_144, k5_relat_1('#skF_10', '#skF_12')) | ~v1_relat_1(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_2155, c_1944])).
% 13.97/6.16  tff(c_2290, plain, (~v1_relat_1(k5_relat_1('#skF_9', '#skF_12'))), inference(splitLeft, [status(thm)], [c_2289])).
% 13.97/6.16  tff(c_2361, plain, (~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_2290])).
% 13.97/6.16  tff(c_2365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_2361])).
% 13.97/6.16  tff(c_2367, plain, (v1_relat_1(k5_relat_1('#skF_9', '#skF_12'))), inference(splitRight, [status(thm)], [c_2289])).
% 13.97/6.16  tff(c_24, plain, (![D_109, B_70, A_18, E_110]: (r2_hidden(k4_tarski(D_109, '#skF_3'(B_70, A_18, k5_relat_1(A_18, B_70), D_109, E_110)), A_18) | ~r2_hidden(k4_tarski(D_109, E_110), k5_relat_1(A_18, B_70)) | ~v1_relat_1(k5_relat_1(A_18, B_70)) | ~v1_relat_1(B_70) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.97/6.16  tff(c_301, plain, (![B_209, D_210, E_208, A_211, B_207]: (r2_hidden(k4_tarski('#skF_3'(B_207, A_211, k5_relat_1(A_211, B_207), D_210, E_208), E_208), B_209) | ~r1_tarski(B_207, B_209) | ~r2_hidden(k4_tarski(D_210, E_208), k5_relat_1(A_211, B_207)) | ~v1_relat_1(k5_relat_1(A_211, B_207)) | ~v1_relat_1(B_207) | ~v1_relat_1(A_211))), inference(resolution, [status(thm)], [c_254, c_2])).
% 13.97/6.16  tff(c_9627, plain, (![B_1005, D_1001, B_1002, E_1004, A_1003, D_1007, A_1006]: (r2_hidden(k4_tarski(D_1007, E_1004), k5_relat_1(A_1003, B_1005)) | ~r2_hidden(k4_tarski(D_1007, '#skF_3'(B_1002, A_1006, k5_relat_1(A_1006, B_1002), D_1001, E_1004)), A_1003) | ~v1_relat_1(k5_relat_1(A_1003, B_1005)) | ~v1_relat_1(B_1005) | ~v1_relat_1(A_1003) | ~r1_tarski(B_1002, B_1005) | ~r2_hidden(k4_tarski(D_1001, E_1004), k5_relat_1(A_1006, B_1002)) | ~v1_relat_1(k5_relat_1(A_1006, B_1002)) | ~v1_relat_1(B_1002) | ~v1_relat_1(A_1006))), inference(resolution, [status(thm)], [c_301, c_20])).
% 13.97/6.16  tff(c_9693, plain, (![E_1014, B_1012, D_1013, B_1010, A_1011]: (r2_hidden(k4_tarski(D_1013, E_1014), k5_relat_1(A_1011, B_1012)) | ~v1_relat_1(k5_relat_1(A_1011, B_1012)) | ~v1_relat_1(B_1012) | ~r1_tarski(B_1010, B_1012) | ~r2_hidden(k4_tarski(D_1013, E_1014), k5_relat_1(A_1011, B_1010)) | ~v1_relat_1(k5_relat_1(A_1011, B_1010)) | ~v1_relat_1(B_1010) | ~v1_relat_1(A_1011))), inference(resolution, [status(thm)], [c_24, c_9627])).
% 13.97/6.16  tff(c_9721, plain, (![D_1013, E_1014, A_1011]: (r2_hidden(k4_tarski(D_1013, E_1014), k5_relat_1(A_1011, '#skF_12')) | ~v1_relat_1(k5_relat_1(A_1011, '#skF_12')) | ~v1_relat_1('#skF_12') | ~r2_hidden(k4_tarski(D_1013, E_1014), k5_relat_1(A_1011, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1011, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(A_1011))), inference(resolution, [status(thm)], [c_30, c_9693])).
% 13.97/6.16  tff(c_9751, plain, (![D_1015, E_1016, A_1017]: (r2_hidden(k4_tarski(D_1015, E_1016), k5_relat_1(A_1017, '#skF_12')) | ~v1_relat_1(k5_relat_1(A_1017, '#skF_12')) | ~r2_hidden(k4_tarski(D_1015, E_1016), k5_relat_1(A_1017, '#skF_11')) | ~v1_relat_1(k5_relat_1(A_1017, '#skF_11')) | ~v1_relat_1(A_1017))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_9721])).
% 13.97/6.16  tff(c_13221, plain, (![A_1056, B_1057]: (r2_hidden(k4_tarski('#skF_1'(k5_relat_1(A_1056, '#skF_11'), B_1057), '#skF_2'(k5_relat_1(A_1056, '#skF_11'), B_1057)), k5_relat_1(A_1056, '#skF_12')) | ~v1_relat_1(k5_relat_1(A_1056, '#skF_12')) | ~v1_relat_1(A_1056) | r1_tarski(k5_relat_1(A_1056, '#skF_11'), B_1057) | ~v1_relat_1(k5_relat_1(A_1056, '#skF_11')))), inference(resolution, [status(thm)], [c_6, c_9751])).
% 13.97/6.16  tff(c_1535, plain, (![A_1, B_416]: (r1_tarski(A_1, k5_relat_1('#skF_10', B_416)) | ~v1_relat_1(A_1) | ~v1_relat_1(k5_relat_1('#skF_10', B_416)) | ~r2_hidden(k4_tarski('#skF_1'(A_1, k5_relat_1('#skF_10', B_416)), '#skF_2'(A_1, k5_relat_1('#skF_10', B_416))), k5_relat_1('#skF_9', B_416)) | ~v1_relat_1(k5_relat_1('#skF_9', B_416)) | ~v1_relat_1(B_416))), inference(resolution, [status(thm)], [c_1442, c_4])).
% 13.97/6.16  tff(c_13235, plain, (~v1_relat_1(k5_relat_1('#skF_10', '#skF_12')) | ~v1_relat_1('#skF_12') | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_12')) | ~v1_relat_1('#skF_9') | r1_tarski(k5_relat_1('#skF_9', '#skF_11'), k5_relat_1('#skF_10', '#skF_12')) | ~v1_relat_1(k5_relat_1('#skF_9', '#skF_11'))), inference(resolution, [status(thm)], [c_13221, c_1535])).
% 13.97/6.16  tff(c_13267, plain, (r1_tarski(k5_relat_1('#skF_9', '#skF_11'), k5_relat_1('#skF_10', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_2086, c_40, c_2367, c_34, c_2155, c_13235])).
% 13.97/6.16  tff(c_13269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_13267])).
% 13.97/6.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.97/6.16  
% 13.97/6.16  Inference rules
% 13.97/6.16  ----------------------
% 13.97/6.16  #Ref     : 0
% 13.97/6.16  #Sup     : 2956
% 13.97/6.16  #Fact    : 0
% 13.97/6.16  #Define  : 0
% 13.97/6.16  #Split   : 31
% 13.97/6.16  #Chain   : 0
% 13.97/6.16  #Close   : 0
% 13.97/6.16  
% 13.97/6.16  Ordering : KBO
% 13.97/6.16  
% 13.97/6.16  Simplification rules
% 13.97/6.16  ----------------------
% 13.97/6.16  #Subsume      : 395
% 13.97/6.16  #Demod        : 1248
% 13.97/6.16  #Tautology    : 25
% 13.97/6.16  #SimpNegUnit  : 1
% 13.97/6.16  #BackRed      : 0
% 13.97/6.16  
% 13.97/6.16  #Partial instantiations: 0
% 13.97/6.16  #Strategies tried      : 1
% 13.97/6.16  
% 13.97/6.16  Timing (in seconds)
% 13.97/6.16  ----------------------
% 13.97/6.16  Preprocessing        : 0.32
% 13.97/6.16  Parsing              : 0.17
% 13.97/6.16  CNF conversion       : 0.04
% 13.97/6.16  Main loop            : 5.05
% 13.97/6.16  Inferencing          : 0.95
% 13.97/6.16  Reduction            : 0.83
% 13.97/6.17  Demodulation         : 0.54
% 13.97/6.17  BG Simplification    : 0.11
% 13.97/6.17  Subsumption          : 2.92
% 13.97/6.17  Abstraction          : 0.15
% 13.97/6.17  MUC search           : 0.00
% 13.97/6.17  Cooper               : 0.00
% 13.97/6.17  Total                : 5.40
% 13.97/6.17  Index Insertion      : 0.00
% 13.97/6.17  Index Deletion       : 0.00
% 13.97/6.17  Index Matching       : 0.00
% 13.97/6.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
