%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:18 EST 2020

% Result     : Theorem 39.21s
% Output     : CNFRefutation 39.29s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 502 expanded)
%              Number of leaves         :   23 ( 180 expanded)
%              Depth                    :   18
%              Number of atoms          :  339 (1881 expanded)
%              Number of equality atoms :   28 ( 188 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k8_relat_1(A_36,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_19,B_29] :
      ( r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),A_19)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    ! [D_63,E_64,B_65,A_66] :
      ( r2_hidden(k4_tarski(D_63,E_64),B_65)
      | ~ r2_hidden(k4_tarski(D_63,E_64),k8_relat_1(A_66,B_65))
      | ~ v1_relat_1(k8_relat_1(A_66,B_65))
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_443,plain,(
    ! [A_118,B_119,B_120] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_118,B_119),B_120),'#skF_6'(k8_relat_1(A_118,B_119),B_120)),B_119)
      | ~ v1_relat_1(B_119)
      | r1_tarski(k8_relat_1(A_118,B_119),B_120)
      | ~ v1_relat_1(k8_relat_1(A_118,B_119)) ) ),
    inference(resolution,[status(thm)],[c_24,c_93])).

tff(c_20,plain,(
    ! [C_34,D_35,B_29,A_19] :
      ( r2_hidden(k4_tarski(C_34,D_35),B_29)
      | ~ r2_hidden(k4_tarski(C_34,D_35),A_19)
      | ~ r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_53334,plain,(
    ! [A_473,B_474,B_475,B_476] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_473,B_474),B_475),'#skF_6'(k8_relat_1(A_473,B_474),B_475)),B_476)
      | ~ r1_tarski(B_474,B_476)
      | ~ v1_relat_1(B_474)
      | r1_tarski(k8_relat_1(A_473,B_474),B_475)
      | ~ v1_relat_1(k8_relat_1(A_473,B_474)) ) ),
    inference(resolution,[status(thm)],[c_443,c_20])).

tff(c_22,plain,(
    ! [A_19,B_29] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),B_29)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_53735,plain,(
    ! [B_477,B_478,A_479] :
      ( ~ r1_tarski(B_477,B_478)
      | ~ v1_relat_1(B_477)
      | r1_tarski(k8_relat_1(A_479,B_477),B_478)
      | ~ v1_relat_1(k8_relat_1(A_479,B_477)) ) ),
    inference(resolution,[status(thm)],[c_53334,c_22])).

tff(c_30,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1('#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_53761,plain,
    ( ~ r1_tarski('#skF_9',k8_relat_1('#skF_8','#skF_10'))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_53735,c_30])).

tff(c_53957,plain,
    ( ~ r1_tarski('#skF_9',k8_relat_1('#skF_8','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_53761])).

tff(c_53958,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_53957])).

tff(c_53961,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_53958])).

tff(c_53965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_53961])).

tff(c_53967,plain,(
    v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_53957])).

tff(c_59,plain,(
    ! [A_49,B_50] :
      ( r2_hidden(k4_tarski('#skF_5'(A_49,B_50),'#skF_6'(A_49,B_50)),A_49)
      | r1_tarski(A_49,B_50)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_59,c_22])).

tff(c_34,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_65,plain,(
    ! [C_51,D_52,B_53,A_54] :
      ( r2_hidden(k4_tarski(C_51,D_52),B_53)
      | ~ r2_hidden(k4_tarski(C_51,D_52),A_54)
      | ~ r1_tarski(A_54,B_53)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    ! [A_60,B_61,B_62] :
      ( r2_hidden(k4_tarski('#skF_5'(A_60,B_61),'#skF_6'(A_60,B_61)),B_62)
      | ~ r1_tarski(A_60,B_62)
      | r1_tarski(A_60,B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_24,c_65])).

tff(c_339,plain,(
    ! [A_95,B_96,B_97,B_98] :
      ( r2_hidden(k4_tarski('#skF_5'(A_95,B_96),'#skF_6'(A_95,B_96)),B_97)
      | ~ r1_tarski(B_98,B_97)
      | ~ v1_relat_1(B_98)
      | ~ r1_tarski(A_95,B_98)
      | r1_tarski(A_95,B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_79,c_20])).

tff(c_343,plain,(
    ! [A_95,B_96] :
      ( r2_hidden(k4_tarski('#skF_5'(A_95,B_96),'#skF_6'(A_95,B_96)),'#skF_10')
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(A_95,'#skF_9')
      | r1_tarski(A_95,B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_34,c_339])).

tff(c_351,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(k4_tarski('#skF_5'(A_99,B_100),'#skF_6'(A_99,B_100)),'#skF_10')
      | ~ r1_tarski(A_99,'#skF_9')
      | r1_tarski(A_99,B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_343])).

tff(c_362,plain,(
    ! [A_101] :
      ( ~ r1_tarski(A_101,'#skF_9')
      | r1_tarski(A_101,'#skF_10')
      | ~ v1_relat_1(A_101) ) ),
    inference(resolution,[status(thm)],[c_351,c_22])).

tff(c_28,plain,(
    ! [B_39,A_38,C_40] :
      ( k8_relat_1(B_39,k8_relat_1(A_38,C_40)) = k8_relat_1(A_38,C_40)
      | ~ r1_tarski(A_38,B_39)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [B_44,A_45,C_46] :
      ( k8_relat_1(B_44,k8_relat_1(A_45,C_46)) = k8_relat_1(A_45,C_46)
      | ~ r1_tarski(A_45,B_44)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ! [B_44,A_38,C_40,B_39] :
      ( k8_relat_1(B_44,k8_relat_1(A_38,C_40)) = k8_relat_1(B_39,k8_relat_1(A_38,C_40))
      | ~ r1_tarski(B_39,B_44)
      | ~ v1_relat_1(k8_relat_1(A_38,C_40))
      | ~ r1_tarski(A_38,B_39)
      | ~ v1_relat_1(C_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_40])).

tff(c_1440,plain,(
    ! [A_165,A_166,C_167] :
      ( k8_relat_1(A_165,k8_relat_1(A_166,C_167)) = k8_relat_1('#skF_10',k8_relat_1(A_166,C_167))
      | ~ v1_relat_1(k8_relat_1(A_166,C_167))
      | ~ r1_tarski(A_166,A_165)
      | ~ v1_relat_1(C_167)
      | ~ r1_tarski(A_165,'#skF_9')
      | ~ v1_relat_1(A_165) ) ),
    inference(resolution,[status(thm)],[c_362,c_52])).

tff(c_1460,plain,(
    ! [A_168,A_169,B_170] :
      ( k8_relat_1(A_168,k8_relat_1(A_169,B_170)) = k8_relat_1('#skF_10',k8_relat_1(A_169,B_170))
      | ~ r1_tarski(A_169,A_168)
      | ~ r1_tarski(A_168,'#skF_9')
      | ~ v1_relat_1(A_168)
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_26,c_1440])).

tff(c_1775,plain,(
    ! [A_171,B_172,A_173] :
      ( k8_relat_1('#skF_10',k8_relat_1(A_171,B_172)) = k8_relat_1(A_171,B_172)
      | ~ r1_tarski(A_171,A_173)
      | ~ v1_relat_1(B_172)
      | ~ r1_tarski(A_171,A_173)
      | ~ r1_tarski(A_173,'#skF_9')
      | ~ v1_relat_1(A_173)
      | ~ v1_relat_1(B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1460,c_28])).

tff(c_1813,plain,(
    ! [A_177,B_178] :
      ( k8_relat_1('#skF_10',k8_relat_1(A_177,B_178)) = k8_relat_1(A_177,B_178)
      | ~ r1_tarski(A_177,A_177)
      | ~ r1_tarski(A_177,'#skF_9')
      | ~ v1_relat_1(B_178)
      | ~ v1_relat_1(A_177) ) ),
    inference(resolution,[status(thm)],[c_64,c_1775])).

tff(c_1823,plain,(
    ! [A_179,B_180] :
      ( k8_relat_1('#skF_10',k8_relat_1(A_179,B_180)) = k8_relat_1(A_179,B_180)
      | ~ r1_tarski(A_179,'#skF_9')
      | ~ v1_relat_1(B_180)
      | ~ v1_relat_1(A_179) ) ),
    inference(resolution,[status(thm)],[c_64,c_1813])).

tff(c_2446,plain,(
    ! [B_188,A_189,B_190] :
      ( k8_relat_1(B_188,k8_relat_1(A_189,B_190)) = k8_relat_1('#skF_10',k8_relat_1(A_189,B_190))
      | ~ r1_tarski('#skF_10',B_188)
      | ~ v1_relat_1(k8_relat_1(A_189,B_190))
      | ~ r1_tarski(A_189,'#skF_9')
      | ~ v1_relat_1(B_190)
      | ~ v1_relat_1(A_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1823,c_28])).

tff(c_2485,plain,(
    ! [B_188,A_36,B_37] :
      ( k8_relat_1(B_188,k8_relat_1(A_36,B_37)) = k8_relat_1('#skF_10',k8_relat_1(A_36,B_37))
      | ~ r1_tarski('#skF_10',B_188)
      | ~ r1_tarski(A_36,'#skF_9')
      | ~ v1_relat_1(A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(resolution,[status(thm)],[c_26,c_2446])).

tff(c_873,plain,(
    ! [A_133,B_134,C_135] :
      ( r2_hidden(k4_tarski('#skF_1'(A_133,B_134,C_135),'#skF_2'(A_133,B_134,C_135)),B_134)
      | r2_hidden(k4_tarski('#skF_3'(A_133,B_134,C_135),'#skF_4'(A_133,B_134,C_135)),C_135)
      | k8_relat_1(A_133,B_134) = C_135
      | ~ v1_relat_1(C_135)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_1,B_2,C_12] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),C_12)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),C_12)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_905,plain,(
    ! [A_136,B_137] :
      ( r2_hidden(k4_tarski('#skF_3'(A_136,B_137,B_137),'#skF_4'(A_136,B_137,B_137)),B_137)
      | k8_relat_1(A_136,B_137) = B_137
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_873,c_8])).

tff(c_18,plain,(
    ! [E_18,A_1,D_17,B_2] :
      ( r2_hidden(E_18,A_1)
      | ~ r2_hidden(k4_tarski(D_17,E_18),k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_917,plain,(
    ! [A_136,A_1,B_2] :
      ( r2_hidden('#skF_4'(A_136,k8_relat_1(A_1,B_2),k8_relat_1(A_1,B_2)),A_1)
      | ~ v1_relat_1(B_2)
      | k8_relat_1(A_136,k8_relat_1(A_1,B_2)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(k8_relat_1(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_905,c_18])).

tff(c_898,plain,(
    ! [A_133,B_134] :
      ( r2_hidden(k4_tarski('#skF_3'(A_133,B_134,B_134),'#skF_4'(A_133,B_134,B_134)),B_134)
      | k8_relat_1(A_133,B_134) = B_134
      | ~ v1_relat_1(B_134) ) ),
    inference(resolution,[status(thm)],[c_873,c_8])).

tff(c_3242,plain,(
    ! [A_197,B_198,C_199] :
      ( r2_hidden(k4_tarski('#skF_1'(A_197,B_198,C_199),'#skF_2'(A_197,B_198,C_199)),B_198)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_197,B_198,C_199),'#skF_4'(A_197,B_198,C_199)),B_198)
      | ~ r2_hidden('#skF_4'(A_197,B_198,C_199),A_197)
      | k8_relat_1(A_197,B_198) = C_199
      | ~ v1_relat_1(C_199)
      | ~ v1_relat_1(B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_12] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),C_12)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),B_2)
      | ~ r2_hidden('#skF_4'(A_1,B_2,C_12),A_1)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3268,plain,(
    ! [A_200,B_201] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_200,B_201,B_201),'#skF_4'(A_200,B_201,B_201)),B_201)
      | ~ r2_hidden('#skF_4'(A_200,B_201,B_201),A_200)
      | k8_relat_1(A_200,B_201) = B_201
      | ~ v1_relat_1(B_201) ) ),
    inference(resolution,[status(thm)],[c_3242,c_2])).

tff(c_3290,plain,(
    ! [A_202,B_203] :
      ( ~ r2_hidden('#skF_4'(A_202,B_203,B_203),A_202)
      | k8_relat_1(A_202,B_203) = B_203
      | ~ v1_relat_1(B_203) ) ),
    inference(resolution,[status(thm)],[c_898,c_3268])).

tff(c_3296,plain,(
    ! [B_204,A_205] :
      ( ~ v1_relat_1(B_204)
      | k8_relat_1(A_205,k8_relat_1(A_205,B_204)) = k8_relat_1(A_205,B_204)
      | ~ v1_relat_1(k8_relat_1(A_205,B_204)) ) ),
    inference(resolution,[status(thm)],[c_917,c_3290])).

tff(c_3332,plain,(
    ! [A_206,B_207] :
      ( k8_relat_1(A_206,k8_relat_1(A_206,B_207)) = k8_relat_1(A_206,B_207)
      | ~ v1_relat_1(B_207) ) ),
    inference(resolution,[status(thm)],[c_26,c_3296])).

tff(c_3745,plain,(
    ! [B_213,A_214,B_215] :
      ( k8_relat_1(B_213,k8_relat_1(A_214,B_215)) = k8_relat_1(A_214,k8_relat_1(A_214,B_215))
      | ~ r1_tarski(A_214,B_213)
      | ~ v1_relat_1(k8_relat_1(A_214,B_215))
      | ~ v1_relat_1(B_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3332,c_28])).

tff(c_3782,plain,(
    ! [B_213,A_36,B_37] :
      ( k8_relat_1(B_213,k8_relat_1(A_36,B_37)) = k8_relat_1(A_36,k8_relat_1(A_36,B_37))
      | ~ r1_tarski(A_36,B_213)
      | ~ v1_relat_1(B_37) ) ),
    inference(resolution,[status(thm)],[c_26,c_3745])).

tff(c_3331,plain,(
    ! [A_36,B_37] :
      ( k8_relat_1(A_36,k8_relat_1(A_36,B_37)) = k8_relat_1(A_36,B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(resolution,[status(thm)],[c_26,c_3296])).

tff(c_3783,plain,(
    ! [B_216,A_217,B_218] :
      ( k8_relat_1(B_216,k8_relat_1(A_217,B_218)) = k8_relat_1(A_217,k8_relat_1(A_217,B_218))
      | ~ r1_tarski(A_217,B_216)
      | ~ v1_relat_1(B_218) ) ),
    inference(resolution,[status(thm)],[c_26,c_3745])).

tff(c_9400,plain,(
    ! [B_248,A_249,B_250] :
      ( k8_relat_1(B_248,k8_relat_1(A_249,B_250)) = k8_relat_1(A_249,k8_relat_1(A_249,k8_relat_1(A_249,B_250)))
      | ~ r1_tarski(A_249,B_248)
      | ~ v1_relat_1(k8_relat_1(A_249,B_250))
      | ~ v1_relat_1(B_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3331,c_3783])).

tff(c_10354,plain,(
    ! [A_251,B_252,B_253] :
      ( v1_relat_1(k8_relat_1(A_251,k8_relat_1(A_251,k8_relat_1(A_251,B_252))))
      | ~ v1_relat_1(k8_relat_1(A_251,B_252))
      | ~ r1_tarski(A_251,B_253)
      | ~ v1_relat_1(k8_relat_1(A_251,B_252))
      | ~ v1_relat_1(B_252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9400,c_26])).

tff(c_10376,plain,(
    ! [B_254] :
      ( v1_relat_1(k8_relat_1('#skF_9',k8_relat_1('#skF_9',k8_relat_1('#skF_9',B_254))))
      | ~ v1_relat_1(k8_relat_1('#skF_9',B_254))
      | ~ v1_relat_1(B_254) ) ),
    inference(resolution,[status(thm)],[c_34,c_10354])).

tff(c_11286,plain,(
    ! [B_262,B_263] :
      ( v1_relat_1(k8_relat_1('#skF_9',k8_relat_1(B_262,k8_relat_1('#skF_9',B_263))))
      | ~ v1_relat_1(k8_relat_1('#skF_9',B_263))
      | ~ v1_relat_1(B_263)
      | ~ r1_tarski('#skF_9',B_262)
      | ~ v1_relat_1(B_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3782,c_10376])).

tff(c_11458,plain,(
    ! [B_188,B_37] :
      ( v1_relat_1(k8_relat_1('#skF_9',k8_relat_1(B_188,k8_relat_1('#skF_9',B_37))))
      | ~ v1_relat_1(k8_relat_1('#skF_9',B_37))
      | ~ v1_relat_1(B_37)
      | ~ r1_tarski('#skF_9','#skF_10')
      | ~ v1_relat_1(B_37)
      | ~ r1_tarski('#skF_10',B_188)
      | ~ r1_tarski('#skF_9','#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2485,c_11286])).

tff(c_11538,plain,(
    ! [B_188,B_37] :
      ( v1_relat_1(k8_relat_1('#skF_9',k8_relat_1(B_188,k8_relat_1('#skF_9',B_37))))
      | ~ v1_relat_1(k8_relat_1('#skF_9',B_37))
      | ~ r1_tarski('#skF_10',B_188)
      | ~ r1_tarski('#skF_9','#skF_9')
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_11458])).

tff(c_11806,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_11538])).

tff(c_11809,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_11806])).

tff(c_11813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_11809])).

tff(c_11815,plain,(
    r1_tarski('#skF_9','#skF_9') ),
    inference(splitRight,[status(thm)],[c_11538])).

tff(c_53734,plain,(
    ! [B_474,B_476,A_473] :
      ( ~ r1_tarski(B_474,B_476)
      | ~ v1_relat_1(B_474)
      | r1_tarski(k8_relat_1(A_473,B_474),B_476)
      | ~ v1_relat_1(k8_relat_1(A_473,B_474)) ) ),
    inference(resolution,[status(thm)],[c_53334,c_22])).

tff(c_36,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_70,plain,(
    ! [E_56,A_57,D_58,B_59] :
      ( r2_hidden(E_56,A_57)
      | ~ r2_hidden(k4_tarski(D_58,E_56),k8_relat_1(A_57,B_59))
      | ~ v1_relat_1(k8_relat_1(A_57,B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [A_57,B_59,B_29] :
      ( r2_hidden('#skF_6'(k8_relat_1(A_57,B_59),B_29),A_57)
      | ~ v1_relat_1(B_59)
      | r1_tarski(k8_relat_1(A_57,B_59),B_29)
      | ~ v1_relat_1(k8_relat_1(A_57,B_59)) ) ),
    inference(resolution,[status(thm)],[c_24,c_70])).

tff(c_106,plain,(
    ! [A_66,B_65,B_29] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_66,B_65),B_29),'#skF_6'(k8_relat_1(A_66,B_65),B_29)),B_65)
      | ~ v1_relat_1(B_65)
      | r1_tarski(k8_relat_1(A_66,B_65),B_29)
      | ~ v1_relat_1(k8_relat_1(A_66,B_65)) ) ),
    inference(resolution,[status(thm)],[c_24,c_93])).

tff(c_32,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [D_17,E_18,A_1,B_2] :
      ( r2_hidden(k4_tarski(D_17,E_18),k8_relat_1(A_1,B_2))
      | ~ r2_hidden(k4_tarski(D_17,E_18),B_2)
      | ~ r2_hidden(E_18,A_1)
      | ~ v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3667,plain,(
    ! [D_209,E_211,B_210,C_212,A_208] :
      ( r2_hidden(E_211,B_210)
      | ~ r2_hidden(k4_tarski(D_209,E_211),k8_relat_1(A_208,C_212))
      | ~ v1_relat_1(k8_relat_1(B_210,k8_relat_1(A_208,C_212)))
      | ~ v1_relat_1(k8_relat_1(A_208,C_212))
      | ~ r1_tarski(A_208,B_210)
      | ~ v1_relat_1(C_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_48809,plain,(
    ! [D_455,E_453,B_456,B_454,A_457] :
      ( r2_hidden(E_453,B_454)
      | ~ v1_relat_1(k8_relat_1(B_454,k8_relat_1(A_457,B_456)))
      | ~ r1_tarski(A_457,B_454)
      | ~ r2_hidden(k4_tarski(D_455,E_453),B_456)
      | ~ r2_hidden(E_453,A_457)
      | ~ v1_relat_1(k8_relat_1(A_457,B_456))
      | ~ v1_relat_1(B_456) ) ),
    inference(resolution,[status(thm)],[c_14,c_3667])).

tff(c_61982,plain,(
    ! [A_517,E_516,D_519,B_518,A_520] :
      ( r2_hidden(E_516,A_520)
      | ~ r1_tarski(A_517,A_520)
      | ~ r2_hidden(k4_tarski(D_519,E_516),B_518)
      | ~ r2_hidden(E_516,A_517)
      | ~ v1_relat_1(B_518)
      | ~ v1_relat_1(k8_relat_1(A_517,B_518)) ) ),
    inference(resolution,[status(thm)],[c_26,c_48809])).

tff(c_62013,plain,(
    ! [E_521,D_522,B_523] :
      ( r2_hidden(E_521,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_522,E_521),B_523)
      | ~ r2_hidden(E_521,'#skF_7')
      | ~ v1_relat_1(B_523)
      | ~ v1_relat_1(k8_relat_1('#skF_7',B_523)) ) ),
    inference(resolution,[status(thm)],[c_32,c_61982])).

tff(c_91121,plain,(
    ! [A_632,B_633,B_634] :
      ( r2_hidden('#skF_6'(k8_relat_1(A_632,B_633),B_634),'#skF_8')
      | ~ r2_hidden('#skF_6'(k8_relat_1(A_632,B_633),B_634),'#skF_7')
      | ~ v1_relat_1(k8_relat_1('#skF_7',B_633))
      | ~ v1_relat_1(B_633)
      | r1_tarski(k8_relat_1(A_632,B_633),B_634)
      | ~ v1_relat_1(k8_relat_1(A_632,B_633)) ) ),
    inference(resolution,[status(thm)],[c_106,c_62013])).

tff(c_91385,plain,(
    ! [B_635,B_636] :
      ( r2_hidden('#skF_6'(k8_relat_1('#skF_7',B_635),B_636),'#skF_8')
      | ~ v1_relat_1(B_635)
      | r1_tarski(k8_relat_1('#skF_7',B_635),B_636)
      | ~ v1_relat_1(k8_relat_1('#skF_7',B_635)) ) ),
    inference(resolution,[status(thm)],[c_78,c_91121])).

tff(c_349,plain,(
    ! [A_95,B_96] :
      ( r2_hidden(k4_tarski('#skF_5'(A_95,B_96),'#skF_6'(A_95,B_96)),'#skF_10')
      | ~ r1_tarski(A_95,'#skF_9')
      | r1_tarski(A_95,B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_343])).

tff(c_111,plain,(
    ! [D_70,E_71,A_72,B_73] :
      ( r2_hidden(k4_tarski(D_70,E_71),k8_relat_1(A_72,B_73))
      | ~ r2_hidden(k4_tarski(D_70,E_71),B_73)
      | ~ r2_hidden(E_71,A_72)
      | ~ v1_relat_1(k8_relat_1(A_72,B_73))
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15356,plain,(
    ! [A_292,A_293,B_294] :
      ( r1_tarski(A_292,k8_relat_1(A_293,B_294))
      | ~ v1_relat_1(A_292)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_292,k8_relat_1(A_293,B_294)),'#skF_6'(A_292,k8_relat_1(A_293,B_294))),B_294)
      | ~ r2_hidden('#skF_6'(A_292,k8_relat_1(A_293,B_294)),A_293)
      | ~ v1_relat_1(k8_relat_1(A_293,B_294))
      | ~ v1_relat_1(B_294) ) ),
    inference(resolution,[status(thm)],[c_111,c_22])).

tff(c_15574,plain,(
    ! [A_95,A_293] :
      ( ~ r2_hidden('#skF_6'(A_95,k8_relat_1(A_293,'#skF_10')),A_293)
      | ~ v1_relat_1(k8_relat_1(A_293,'#skF_10'))
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski(A_95,'#skF_9')
      | r1_tarski(A_95,k8_relat_1(A_293,'#skF_10'))
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_349,c_15356])).

tff(c_15621,plain,(
    ! [A_95,A_293] :
      ( ~ r2_hidden('#skF_6'(A_95,k8_relat_1(A_293,'#skF_10')),A_293)
      | ~ v1_relat_1(k8_relat_1(A_293,'#skF_10'))
      | ~ r1_tarski(A_95,'#skF_9')
      | r1_tarski(A_95,k8_relat_1(A_293,'#skF_10'))
      | ~ v1_relat_1(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_15574])).

tff(c_91546,plain,(
    ! [B_635] :
      ( ~ v1_relat_1(k8_relat_1('#skF_8','#skF_10'))
      | ~ r1_tarski(k8_relat_1('#skF_7',B_635),'#skF_9')
      | ~ v1_relat_1(B_635)
      | r1_tarski(k8_relat_1('#skF_7',B_635),k8_relat_1('#skF_8','#skF_10'))
      | ~ v1_relat_1(k8_relat_1('#skF_7',B_635)) ) ),
    inference(resolution,[status(thm)],[c_91385,c_15621])).

tff(c_125487,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_8','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_91546])).

tff(c_126079,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_26,c_125487])).

tff(c_126083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_126079])).

tff(c_126086,plain,(
    ! [B_790] :
      ( ~ r1_tarski(k8_relat_1('#skF_7',B_790),'#skF_9')
      | ~ v1_relat_1(B_790)
      | r1_tarski(k8_relat_1('#skF_7',B_790),k8_relat_1('#skF_8','#skF_10'))
      | ~ v1_relat_1(k8_relat_1('#skF_7',B_790)) ) ),
    inference(splitRight,[status(thm)],[c_91546])).

tff(c_126125,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),'#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_126086,c_30])).

tff(c_126314,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53967,c_38,c_126125])).

tff(c_126317,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_53734,c_126314])).

tff(c_126324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53967,c_38,c_11815,c_126317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:15:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.21/25.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.29/25.95  
% 39.29/25.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.29/25.95  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 39.29/25.95  
% 39.29/25.95  %Foreground sorts:
% 39.29/25.95  
% 39.29/25.95  
% 39.29/25.95  %Background operators:
% 39.29/25.95  
% 39.29/25.95  
% 39.29/25.95  %Foreground operators:
% 39.29/25.95  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 39.29/25.95  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 39.29/25.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 39.29/25.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 39.29/25.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 39.29/25.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 39.29/25.95  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 39.29/25.95  tff('#skF_7', type, '#skF_7': $i).
% 39.29/25.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 39.29/25.95  tff('#skF_10', type, '#skF_10': $i).
% 39.29/25.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 39.29/25.95  tff('#skF_9', type, '#skF_9': $i).
% 39.29/25.95  tff('#skF_8', type, '#skF_8': $i).
% 39.29/25.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 39.29/25.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 39.29/25.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 39.29/25.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 39.29/25.95  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 39.29/25.95  
% 39.29/25.98  tff(f_71, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_relat_1)).
% 39.29/25.98  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 39.29/25.98  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 39.29/25.98  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 39.29/25.98  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 39.29/25.98  tff(c_38, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_71])).
% 39.29/25.98  tff(c_26, plain, (![A_36, B_37]: (v1_relat_1(k8_relat_1(A_36, B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 39.29/25.98  tff(c_24, plain, (![A_19, B_29]: (r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), A_19) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 39.29/25.98  tff(c_93, plain, (![D_63, E_64, B_65, A_66]: (r2_hidden(k4_tarski(D_63, E_64), B_65) | ~r2_hidden(k4_tarski(D_63, E_64), k8_relat_1(A_66, B_65)) | ~v1_relat_1(k8_relat_1(A_66, B_65)) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.29/25.98  tff(c_443, plain, (![A_118, B_119, B_120]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_118, B_119), B_120), '#skF_6'(k8_relat_1(A_118, B_119), B_120)), B_119) | ~v1_relat_1(B_119) | r1_tarski(k8_relat_1(A_118, B_119), B_120) | ~v1_relat_1(k8_relat_1(A_118, B_119)))), inference(resolution, [status(thm)], [c_24, c_93])).
% 39.29/25.98  tff(c_20, plain, (![C_34, D_35, B_29, A_19]: (r2_hidden(k4_tarski(C_34, D_35), B_29) | ~r2_hidden(k4_tarski(C_34, D_35), A_19) | ~r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 39.29/25.98  tff(c_53334, plain, (![A_473, B_474, B_475, B_476]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_473, B_474), B_475), '#skF_6'(k8_relat_1(A_473, B_474), B_475)), B_476) | ~r1_tarski(B_474, B_476) | ~v1_relat_1(B_474) | r1_tarski(k8_relat_1(A_473, B_474), B_475) | ~v1_relat_1(k8_relat_1(A_473, B_474)))), inference(resolution, [status(thm)], [c_443, c_20])).
% 39.29/25.98  tff(c_22, plain, (![A_19, B_29]: (~r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), B_29) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 39.29/25.98  tff(c_53735, plain, (![B_477, B_478, A_479]: (~r1_tarski(B_477, B_478) | ~v1_relat_1(B_477) | r1_tarski(k8_relat_1(A_479, B_477), B_478) | ~v1_relat_1(k8_relat_1(A_479, B_477)))), inference(resolution, [status(thm)], [c_53334, c_22])).
% 39.29/25.98  tff(c_30, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1('#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 39.29/25.98  tff(c_53761, plain, (~r1_tarski('#skF_9', k8_relat_1('#skF_8', '#skF_10')) | ~v1_relat_1('#skF_9') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_53735, c_30])).
% 39.29/25.98  tff(c_53957, plain, (~r1_tarski('#skF_9', k8_relat_1('#skF_8', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_53761])).
% 39.29/25.98  tff(c_53958, plain, (~v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_53957])).
% 39.29/25.98  tff(c_53961, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_53958])).
% 39.29/25.98  tff(c_53965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_53961])).
% 39.29/25.98  tff(c_53967, plain, (v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_53957])).
% 39.29/25.98  tff(c_59, plain, (![A_49, B_50]: (r2_hidden(k4_tarski('#skF_5'(A_49, B_50), '#skF_6'(A_49, B_50)), A_49) | r1_tarski(A_49, B_50) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 39.29/25.98  tff(c_64, plain, (![A_49]: (r1_tarski(A_49, A_49) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_59, c_22])).
% 39.29/25.98  tff(c_34, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_71])).
% 39.29/25.98  tff(c_65, plain, (![C_51, D_52, B_53, A_54]: (r2_hidden(k4_tarski(C_51, D_52), B_53) | ~r2_hidden(k4_tarski(C_51, D_52), A_54) | ~r1_tarski(A_54, B_53) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 39.29/25.98  tff(c_79, plain, (![A_60, B_61, B_62]: (r2_hidden(k4_tarski('#skF_5'(A_60, B_61), '#skF_6'(A_60, B_61)), B_62) | ~r1_tarski(A_60, B_62) | r1_tarski(A_60, B_61) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_24, c_65])).
% 39.29/25.98  tff(c_339, plain, (![A_95, B_96, B_97, B_98]: (r2_hidden(k4_tarski('#skF_5'(A_95, B_96), '#skF_6'(A_95, B_96)), B_97) | ~r1_tarski(B_98, B_97) | ~v1_relat_1(B_98) | ~r1_tarski(A_95, B_98) | r1_tarski(A_95, B_96) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_79, c_20])).
% 39.29/25.98  tff(c_343, plain, (![A_95, B_96]: (r2_hidden(k4_tarski('#skF_5'(A_95, B_96), '#skF_6'(A_95, B_96)), '#skF_10') | ~v1_relat_1('#skF_9') | ~r1_tarski(A_95, '#skF_9') | r1_tarski(A_95, B_96) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_34, c_339])).
% 39.29/25.98  tff(c_351, plain, (![A_99, B_100]: (r2_hidden(k4_tarski('#skF_5'(A_99, B_100), '#skF_6'(A_99, B_100)), '#skF_10') | ~r1_tarski(A_99, '#skF_9') | r1_tarski(A_99, B_100) | ~v1_relat_1(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_343])).
% 39.29/25.98  tff(c_362, plain, (![A_101]: (~r1_tarski(A_101, '#skF_9') | r1_tarski(A_101, '#skF_10') | ~v1_relat_1(A_101))), inference(resolution, [status(thm)], [c_351, c_22])).
% 39.29/25.98  tff(c_28, plain, (![B_39, A_38, C_40]: (k8_relat_1(B_39, k8_relat_1(A_38, C_40))=k8_relat_1(A_38, C_40) | ~r1_tarski(A_38, B_39) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 39.29/25.98  tff(c_40, plain, (![B_44, A_45, C_46]: (k8_relat_1(B_44, k8_relat_1(A_45, C_46))=k8_relat_1(A_45, C_46) | ~r1_tarski(A_45, B_44) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_59])).
% 39.29/25.98  tff(c_52, plain, (![B_44, A_38, C_40, B_39]: (k8_relat_1(B_44, k8_relat_1(A_38, C_40))=k8_relat_1(B_39, k8_relat_1(A_38, C_40)) | ~r1_tarski(B_39, B_44) | ~v1_relat_1(k8_relat_1(A_38, C_40)) | ~r1_tarski(A_38, B_39) | ~v1_relat_1(C_40))), inference(superposition, [status(thm), theory('equality')], [c_28, c_40])).
% 39.29/25.98  tff(c_1440, plain, (![A_165, A_166, C_167]: (k8_relat_1(A_165, k8_relat_1(A_166, C_167))=k8_relat_1('#skF_10', k8_relat_1(A_166, C_167)) | ~v1_relat_1(k8_relat_1(A_166, C_167)) | ~r1_tarski(A_166, A_165) | ~v1_relat_1(C_167) | ~r1_tarski(A_165, '#skF_9') | ~v1_relat_1(A_165))), inference(resolution, [status(thm)], [c_362, c_52])).
% 39.29/25.98  tff(c_1460, plain, (![A_168, A_169, B_170]: (k8_relat_1(A_168, k8_relat_1(A_169, B_170))=k8_relat_1('#skF_10', k8_relat_1(A_169, B_170)) | ~r1_tarski(A_169, A_168) | ~r1_tarski(A_168, '#skF_9') | ~v1_relat_1(A_168) | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_26, c_1440])).
% 39.29/25.98  tff(c_1775, plain, (![A_171, B_172, A_173]: (k8_relat_1('#skF_10', k8_relat_1(A_171, B_172))=k8_relat_1(A_171, B_172) | ~r1_tarski(A_171, A_173) | ~v1_relat_1(B_172) | ~r1_tarski(A_171, A_173) | ~r1_tarski(A_173, '#skF_9') | ~v1_relat_1(A_173) | ~v1_relat_1(B_172))), inference(superposition, [status(thm), theory('equality')], [c_1460, c_28])).
% 39.29/25.98  tff(c_1813, plain, (![A_177, B_178]: (k8_relat_1('#skF_10', k8_relat_1(A_177, B_178))=k8_relat_1(A_177, B_178) | ~r1_tarski(A_177, A_177) | ~r1_tarski(A_177, '#skF_9') | ~v1_relat_1(B_178) | ~v1_relat_1(A_177))), inference(resolution, [status(thm)], [c_64, c_1775])).
% 39.29/25.98  tff(c_1823, plain, (![A_179, B_180]: (k8_relat_1('#skF_10', k8_relat_1(A_179, B_180))=k8_relat_1(A_179, B_180) | ~r1_tarski(A_179, '#skF_9') | ~v1_relat_1(B_180) | ~v1_relat_1(A_179))), inference(resolution, [status(thm)], [c_64, c_1813])).
% 39.29/25.98  tff(c_2446, plain, (![B_188, A_189, B_190]: (k8_relat_1(B_188, k8_relat_1(A_189, B_190))=k8_relat_1('#skF_10', k8_relat_1(A_189, B_190)) | ~r1_tarski('#skF_10', B_188) | ~v1_relat_1(k8_relat_1(A_189, B_190)) | ~r1_tarski(A_189, '#skF_9') | ~v1_relat_1(B_190) | ~v1_relat_1(A_189))), inference(superposition, [status(thm), theory('equality')], [c_1823, c_28])).
% 39.29/25.98  tff(c_2485, plain, (![B_188, A_36, B_37]: (k8_relat_1(B_188, k8_relat_1(A_36, B_37))=k8_relat_1('#skF_10', k8_relat_1(A_36, B_37)) | ~r1_tarski('#skF_10', B_188) | ~r1_tarski(A_36, '#skF_9') | ~v1_relat_1(A_36) | ~v1_relat_1(B_37))), inference(resolution, [status(thm)], [c_26, c_2446])).
% 39.29/25.98  tff(c_873, plain, (![A_133, B_134, C_135]: (r2_hidden(k4_tarski('#skF_1'(A_133, B_134, C_135), '#skF_2'(A_133, B_134, C_135)), B_134) | r2_hidden(k4_tarski('#skF_3'(A_133, B_134, C_135), '#skF_4'(A_133, B_134, C_135)), C_135) | k8_relat_1(A_133, B_134)=C_135 | ~v1_relat_1(C_135) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.29/25.98  tff(c_8, plain, (![A_1, B_2, C_12]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_12), '#skF_2'(A_1, B_2, C_12)), C_12) | r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), C_12) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.29/25.98  tff(c_905, plain, (![A_136, B_137]: (r2_hidden(k4_tarski('#skF_3'(A_136, B_137, B_137), '#skF_4'(A_136, B_137, B_137)), B_137) | k8_relat_1(A_136, B_137)=B_137 | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_873, c_8])).
% 39.29/25.98  tff(c_18, plain, (![E_18, A_1, D_17, B_2]: (r2_hidden(E_18, A_1) | ~r2_hidden(k4_tarski(D_17, E_18), k8_relat_1(A_1, B_2)) | ~v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.29/25.98  tff(c_917, plain, (![A_136, A_1, B_2]: (r2_hidden('#skF_4'(A_136, k8_relat_1(A_1, B_2), k8_relat_1(A_1, B_2)), A_1) | ~v1_relat_1(B_2) | k8_relat_1(A_136, k8_relat_1(A_1, B_2))=k8_relat_1(A_1, B_2) | ~v1_relat_1(k8_relat_1(A_1, B_2)))), inference(resolution, [status(thm)], [c_905, c_18])).
% 39.29/25.98  tff(c_898, plain, (![A_133, B_134]: (r2_hidden(k4_tarski('#skF_3'(A_133, B_134, B_134), '#skF_4'(A_133, B_134, B_134)), B_134) | k8_relat_1(A_133, B_134)=B_134 | ~v1_relat_1(B_134))), inference(resolution, [status(thm)], [c_873, c_8])).
% 39.29/25.98  tff(c_3242, plain, (![A_197, B_198, C_199]: (r2_hidden(k4_tarski('#skF_1'(A_197, B_198, C_199), '#skF_2'(A_197, B_198, C_199)), B_198) | ~r2_hidden(k4_tarski('#skF_3'(A_197, B_198, C_199), '#skF_4'(A_197, B_198, C_199)), B_198) | ~r2_hidden('#skF_4'(A_197, B_198, C_199), A_197) | k8_relat_1(A_197, B_198)=C_199 | ~v1_relat_1(C_199) | ~v1_relat_1(B_198))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.29/25.98  tff(c_2, plain, (![A_1, B_2, C_12]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_12), '#skF_2'(A_1, B_2, C_12)), C_12) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), B_2) | ~r2_hidden('#skF_4'(A_1, B_2, C_12), A_1) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.29/25.98  tff(c_3268, plain, (![A_200, B_201]: (~r2_hidden(k4_tarski('#skF_3'(A_200, B_201, B_201), '#skF_4'(A_200, B_201, B_201)), B_201) | ~r2_hidden('#skF_4'(A_200, B_201, B_201), A_200) | k8_relat_1(A_200, B_201)=B_201 | ~v1_relat_1(B_201))), inference(resolution, [status(thm)], [c_3242, c_2])).
% 39.29/25.98  tff(c_3290, plain, (![A_202, B_203]: (~r2_hidden('#skF_4'(A_202, B_203, B_203), A_202) | k8_relat_1(A_202, B_203)=B_203 | ~v1_relat_1(B_203))), inference(resolution, [status(thm)], [c_898, c_3268])).
% 39.29/25.98  tff(c_3296, plain, (![B_204, A_205]: (~v1_relat_1(B_204) | k8_relat_1(A_205, k8_relat_1(A_205, B_204))=k8_relat_1(A_205, B_204) | ~v1_relat_1(k8_relat_1(A_205, B_204)))), inference(resolution, [status(thm)], [c_917, c_3290])).
% 39.29/25.98  tff(c_3332, plain, (![A_206, B_207]: (k8_relat_1(A_206, k8_relat_1(A_206, B_207))=k8_relat_1(A_206, B_207) | ~v1_relat_1(B_207))), inference(resolution, [status(thm)], [c_26, c_3296])).
% 39.29/25.98  tff(c_3745, plain, (![B_213, A_214, B_215]: (k8_relat_1(B_213, k8_relat_1(A_214, B_215))=k8_relat_1(A_214, k8_relat_1(A_214, B_215)) | ~r1_tarski(A_214, B_213) | ~v1_relat_1(k8_relat_1(A_214, B_215)) | ~v1_relat_1(B_215))), inference(superposition, [status(thm), theory('equality')], [c_3332, c_28])).
% 39.29/25.98  tff(c_3782, plain, (![B_213, A_36, B_37]: (k8_relat_1(B_213, k8_relat_1(A_36, B_37))=k8_relat_1(A_36, k8_relat_1(A_36, B_37)) | ~r1_tarski(A_36, B_213) | ~v1_relat_1(B_37))), inference(resolution, [status(thm)], [c_26, c_3745])).
% 39.29/25.98  tff(c_3331, plain, (![A_36, B_37]: (k8_relat_1(A_36, k8_relat_1(A_36, B_37))=k8_relat_1(A_36, B_37) | ~v1_relat_1(B_37))), inference(resolution, [status(thm)], [c_26, c_3296])).
% 39.29/25.98  tff(c_3783, plain, (![B_216, A_217, B_218]: (k8_relat_1(B_216, k8_relat_1(A_217, B_218))=k8_relat_1(A_217, k8_relat_1(A_217, B_218)) | ~r1_tarski(A_217, B_216) | ~v1_relat_1(B_218))), inference(resolution, [status(thm)], [c_26, c_3745])).
% 39.29/25.98  tff(c_9400, plain, (![B_248, A_249, B_250]: (k8_relat_1(B_248, k8_relat_1(A_249, B_250))=k8_relat_1(A_249, k8_relat_1(A_249, k8_relat_1(A_249, B_250))) | ~r1_tarski(A_249, B_248) | ~v1_relat_1(k8_relat_1(A_249, B_250)) | ~v1_relat_1(B_250))), inference(superposition, [status(thm), theory('equality')], [c_3331, c_3783])).
% 39.29/25.98  tff(c_10354, plain, (![A_251, B_252, B_253]: (v1_relat_1(k8_relat_1(A_251, k8_relat_1(A_251, k8_relat_1(A_251, B_252)))) | ~v1_relat_1(k8_relat_1(A_251, B_252)) | ~r1_tarski(A_251, B_253) | ~v1_relat_1(k8_relat_1(A_251, B_252)) | ~v1_relat_1(B_252))), inference(superposition, [status(thm), theory('equality')], [c_9400, c_26])).
% 39.29/25.98  tff(c_10376, plain, (![B_254]: (v1_relat_1(k8_relat_1('#skF_9', k8_relat_1('#skF_9', k8_relat_1('#skF_9', B_254)))) | ~v1_relat_1(k8_relat_1('#skF_9', B_254)) | ~v1_relat_1(B_254))), inference(resolution, [status(thm)], [c_34, c_10354])).
% 39.29/25.98  tff(c_11286, plain, (![B_262, B_263]: (v1_relat_1(k8_relat_1('#skF_9', k8_relat_1(B_262, k8_relat_1('#skF_9', B_263)))) | ~v1_relat_1(k8_relat_1('#skF_9', B_263)) | ~v1_relat_1(B_263) | ~r1_tarski('#skF_9', B_262) | ~v1_relat_1(B_263))), inference(superposition, [status(thm), theory('equality')], [c_3782, c_10376])).
% 39.29/25.98  tff(c_11458, plain, (![B_188, B_37]: (v1_relat_1(k8_relat_1('#skF_9', k8_relat_1(B_188, k8_relat_1('#skF_9', B_37)))) | ~v1_relat_1(k8_relat_1('#skF_9', B_37)) | ~v1_relat_1(B_37) | ~r1_tarski('#skF_9', '#skF_10') | ~v1_relat_1(B_37) | ~r1_tarski('#skF_10', B_188) | ~r1_tarski('#skF_9', '#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_2485, c_11286])).
% 39.29/25.98  tff(c_11538, plain, (![B_188, B_37]: (v1_relat_1(k8_relat_1('#skF_9', k8_relat_1(B_188, k8_relat_1('#skF_9', B_37)))) | ~v1_relat_1(k8_relat_1('#skF_9', B_37)) | ~r1_tarski('#skF_10', B_188) | ~r1_tarski('#skF_9', '#skF_9') | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_11458])).
% 39.29/25.98  tff(c_11806, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(splitLeft, [status(thm)], [c_11538])).
% 39.29/25.98  tff(c_11809, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_64, c_11806])).
% 39.29/25.98  tff(c_11813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_11809])).
% 39.29/25.98  tff(c_11815, plain, (r1_tarski('#skF_9', '#skF_9')), inference(splitRight, [status(thm)], [c_11538])).
% 39.29/25.98  tff(c_53734, plain, (![B_474, B_476, A_473]: (~r1_tarski(B_474, B_476) | ~v1_relat_1(B_474) | r1_tarski(k8_relat_1(A_473, B_474), B_476) | ~v1_relat_1(k8_relat_1(A_473, B_474)))), inference(resolution, [status(thm)], [c_53334, c_22])).
% 39.29/25.98  tff(c_36, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_71])).
% 39.29/25.98  tff(c_70, plain, (![E_56, A_57, D_58, B_59]: (r2_hidden(E_56, A_57) | ~r2_hidden(k4_tarski(D_58, E_56), k8_relat_1(A_57, B_59)) | ~v1_relat_1(k8_relat_1(A_57, B_59)) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.29/25.98  tff(c_78, plain, (![A_57, B_59, B_29]: (r2_hidden('#skF_6'(k8_relat_1(A_57, B_59), B_29), A_57) | ~v1_relat_1(B_59) | r1_tarski(k8_relat_1(A_57, B_59), B_29) | ~v1_relat_1(k8_relat_1(A_57, B_59)))), inference(resolution, [status(thm)], [c_24, c_70])).
% 39.29/25.98  tff(c_106, plain, (![A_66, B_65, B_29]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_66, B_65), B_29), '#skF_6'(k8_relat_1(A_66, B_65), B_29)), B_65) | ~v1_relat_1(B_65) | r1_tarski(k8_relat_1(A_66, B_65), B_29) | ~v1_relat_1(k8_relat_1(A_66, B_65)))), inference(resolution, [status(thm)], [c_24, c_93])).
% 39.29/25.98  tff(c_32, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 39.29/25.98  tff(c_14, plain, (![D_17, E_18, A_1, B_2]: (r2_hidden(k4_tarski(D_17, E_18), k8_relat_1(A_1, B_2)) | ~r2_hidden(k4_tarski(D_17, E_18), B_2) | ~r2_hidden(E_18, A_1) | ~v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.29/25.98  tff(c_3667, plain, (![D_209, E_211, B_210, C_212, A_208]: (r2_hidden(E_211, B_210) | ~r2_hidden(k4_tarski(D_209, E_211), k8_relat_1(A_208, C_212)) | ~v1_relat_1(k8_relat_1(B_210, k8_relat_1(A_208, C_212))) | ~v1_relat_1(k8_relat_1(A_208, C_212)) | ~r1_tarski(A_208, B_210) | ~v1_relat_1(C_212))), inference(superposition, [status(thm), theory('equality')], [c_28, c_70])).
% 39.29/25.98  tff(c_48809, plain, (![D_455, E_453, B_456, B_454, A_457]: (r2_hidden(E_453, B_454) | ~v1_relat_1(k8_relat_1(B_454, k8_relat_1(A_457, B_456))) | ~r1_tarski(A_457, B_454) | ~r2_hidden(k4_tarski(D_455, E_453), B_456) | ~r2_hidden(E_453, A_457) | ~v1_relat_1(k8_relat_1(A_457, B_456)) | ~v1_relat_1(B_456))), inference(resolution, [status(thm)], [c_14, c_3667])).
% 39.29/25.98  tff(c_61982, plain, (![A_517, E_516, D_519, B_518, A_520]: (r2_hidden(E_516, A_520) | ~r1_tarski(A_517, A_520) | ~r2_hidden(k4_tarski(D_519, E_516), B_518) | ~r2_hidden(E_516, A_517) | ~v1_relat_1(B_518) | ~v1_relat_1(k8_relat_1(A_517, B_518)))), inference(resolution, [status(thm)], [c_26, c_48809])).
% 39.29/25.98  tff(c_62013, plain, (![E_521, D_522, B_523]: (r2_hidden(E_521, '#skF_8') | ~r2_hidden(k4_tarski(D_522, E_521), B_523) | ~r2_hidden(E_521, '#skF_7') | ~v1_relat_1(B_523) | ~v1_relat_1(k8_relat_1('#skF_7', B_523)))), inference(resolution, [status(thm)], [c_32, c_61982])).
% 39.29/25.98  tff(c_91121, plain, (![A_632, B_633, B_634]: (r2_hidden('#skF_6'(k8_relat_1(A_632, B_633), B_634), '#skF_8') | ~r2_hidden('#skF_6'(k8_relat_1(A_632, B_633), B_634), '#skF_7') | ~v1_relat_1(k8_relat_1('#skF_7', B_633)) | ~v1_relat_1(B_633) | r1_tarski(k8_relat_1(A_632, B_633), B_634) | ~v1_relat_1(k8_relat_1(A_632, B_633)))), inference(resolution, [status(thm)], [c_106, c_62013])).
% 39.29/25.98  tff(c_91385, plain, (![B_635, B_636]: (r2_hidden('#skF_6'(k8_relat_1('#skF_7', B_635), B_636), '#skF_8') | ~v1_relat_1(B_635) | r1_tarski(k8_relat_1('#skF_7', B_635), B_636) | ~v1_relat_1(k8_relat_1('#skF_7', B_635)))), inference(resolution, [status(thm)], [c_78, c_91121])).
% 39.29/25.98  tff(c_349, plain, (![A_95, B_96]: (r2_hidden(k4_tarski('#skF_5'(A_95, B_96), '#skF_6'(A_95, B_96)), '#skF_10') | ~r1_tarski(A_95, '#skF_9') | r1_tarski(A_95, B_96) | ~v1_relat_1(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_343])).
% 39.29/25.98  tff(c_111, plain, (![D_70, E_71, A_72, B_73]: (r2_hidden(k4_tarski(D_70, E_71), k8_relat_1(A_72, B_73)) | ~r2_hidden(k4_tarski(D_70, E_71), B_73) | ~r2_hidden(E_71, A_72) | ~v1_relat_1(k8_relat_1(A_72, B_73)) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_39])).
% 39.29/25.98  tff(c_15356, plain, (![A_292, A_293, B_294]: (r1_tarski(A_292, k8_relat_1(A_293, B_294)) | ~v1_relat_1(A_292) | ~r2_hidden(k4_tarski('#skF_5'(A_292, k8_relat_1(A_293, B_294)), '#skF_6'(A_292, k8_relat_1(A_293, B_294))), B_294) | ~r2_hidden('#skF_6'(A_292, k8_relat_1(A_293, B_294)), A_293) | ~v1_relat_1(k8_relat_1(A_293, B_294)) | ~v1_relat_1(B_294))), inference(resolution, [status(thm)], [c_111, c_22])).
% 39.29/25.98  tff(c_15574, plain, (![A_95, A_293]: (~r2_hidden('#skF_6'(A_95, k8_relat_1(A_293, '#skF_10')), A_293) | ~v1_relat_1(k8_relat_1(A_293, '#skF_10')) | ~v1_relat_1('#skF_10') | ~r1_tarski(A_95, '#skF_9') | r1_tarski(A_95, k8_relat_1(A_293, '#skF_10')) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_349, c_15356])).
% 39.29/25.98  tff(c_15621, plain, (![A_95, A_293]: (~r2_hidden('#skF_6'(A_95, k8_relat_1(A_293, '#skF_10')), A_293) | ~v1_relat_1(k8_relat_1(A_293, '#skF_10')) | ~r1_tarski(A_95, '#skF_9') | r1_tarski(A_95, k8_relat_1(A_293, '#skF_10')) | ~v1_relat_1(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_15574])).
% 39.29/25.98  tff(c_91546, plain, (![B_635]: (~v1_relat_1(k8_relat_1('#skF_8', '#skF_10')) | ~r1_tarski(k8_relat_1('#skF_7', B_635), '#skF_9') | ~v1_relat_1(B_635) | r1_tarski(k8_relat_1('#skF_7', B_635), k8_relat_1('#skF_8', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_7', B_635)))), inference(resolution, [status(thm)], [c_91385, c_15621])).
% 39.29/25.98  tff(c_125487, plain, (~v1_relat_1(k8_relat_1('#skF_8', '#skF_10'))), inference(splitLeft, [status(thm)], [c_91546])).
% 39.29/25.98  tff(c_126079, plain, (~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_26, c_125487])).
% 39.29/25.98  tff(c_126083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_126079])).
% 39.29/25.98  tff(c_126086, plain, (![B_790]: (~r1_tarski(k8_relat_1('#skF_7', B_790), '#skF_9') | ~v1_relat_1(B_790) | r1_tarski(k8_relat_1('#skF_7', B_790), k8_relat_1('#skF_8', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_7', B_790)))), inference(splitRight, [status(thm)], [c_91546])).
% 39.29/25.98  tff(c_126125, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), '#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_126086, c_30])).
% 39.29/25.98  tff(c_126314, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_53967, c_38, c_126125])).
% 39.29/25.98  tff(c_126317, plain, (~r1_tarski('#skF_9', '#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_53734, c_126314])).
% 39.29/25.98  tff(c_126324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53967, c_38, c_11815, c_126317])).
% 39.29/25.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.29/25.98  
% 39.29/25.98  Inference rules
% 39.29/25.98  ----------------------
% 39.29/25.98  #Ref     : 0
% 39.29/25.98  #Sup     : 34437
% 39.29/25.98  #Fact    : 0
% 39.29/25.98  #Define  : 0
% 39.29/25.98  #Split   : 28
% 39.29/25.98  #Chain   : 0
% 39.29/25.98  #Close   : 0
% 39.29/25.98  
% 39.29/25.98  Ordering : KBO
% 39.29/25.98  
% 39.29/25.98  Simplification rules
% 39.29/25.98  ----------------------
% 39.29/25.98  #Subsume      : 13818
% 39.29/25.98  #Demod        : 7627
% 39.29/25.98  #Tautology    : 514
% 39.29/25.98  #SimpNegUnit  : 13
% 39.29/25.98  #BackRed      : 12
% 39.29/25.98  
% 39.29/25.98  #Partial instantiations: 0
% 39.29/25.98  #Strategies tried      : 1
% 39.29/25.98  
% 39.29/25.98  Timing (in seconds)
% 39.29/25.98  ----------------------
% 39.29/25.98  Preprocessing        : 0.29
% 39.29/25.98  Parsing              : 0.15
% 39.29/25.98  CNF conversion       : 0.03
% 39.29/25.98  Main loop            : 24.89
% 39.29/25.98  Inferencing          : 4.06
% 39.29/25.98  Reduction            : 4.23
% 39.29/25.98  Demodulation         : 2.80
% 39.29/25.98  BG Simplification    : 0.68
% 39.29/25.98  Subsumption          : 14.91
% 39.29/25.98  Abstraction          : 0.86
% 39.29/25.98  MUC search           : 0.00
% 39.29/25.98  Cooper               : 0.00
% 39.29/25.98  Total                : 25.23
% 39.29/25.98  Index Insertion      : 0.00
% 39.29/25.98  Index Deletion       : 0.00
% 39.29/25.98  Index Matching       : 0.00
% 39.29/25.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
