%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:47 EST 2020

% Result     : Theorem 10.24s
% Output     : CNFRefutation 10.31s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 658 expanded)
%              Number of leaves         :   37 ( 254 expanded)
%              Depth                    :   15
%              Number of atoms          :  232 (1900 expanded)
%              Number of equality atoms :   65 ( 590 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_138,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_58,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_64,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_160,plain,(
    ! [A_58] :
      ( k4_relat_1(A_58) = k2_funct_1(A_58)
      | ~ v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_163,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_160])).

tff(c_166,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_163])).

tff(c_14,plain,(
    ! [A_20] :
      ( v1_relat_1(k4_relat_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_179,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_14])).

tff(c_189,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_179])).

tff(c_16,plain,(
    ! [A_21] :
      ( k4_relat_1(k4_relat_1(A_21)) = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_176,plain,
    ( k4_relat_1(k2_funct_1('#skF_6')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_16])).

tff(c_187,plain,(
    k4_relat_1(k2_funct_1('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_176])).

tff(c_26,plain,(
    ! [A_28] :
      ( k1_relat_1(k4_relat_1(A_28)) = k2_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_170,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_26])).

tff(c_183,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_170])).

tff(c_24,plain,(
    ! [A_28] :
      ( k2_relat_1(k4_relat_1(A_28)) = k1_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_447,plain,(
    ! [A_75,C_76] :
      ( r2_hidden(k4_tarski('#skF_4'(A_75,k2_relat_1(A_75),C_76),C_76),A_75)
      | ~ r2_hidden(C_76,k2_relat_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ! [C_42,A_40,B_41] :
      ( k1_funct_1(C_42,A_40) = B_41
      | ~ r2_hidden(k4_tarski(A_40,B_41),C_42)
      | ~ v1_funct_1(C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1239,plain,(
    ! [A_125,C_126] :
      ( k1_funct_1(A_125,'#skF_4'(A_125,k2_relat_1(A_125),C_126)) = C_126
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125)
      | ~ r2_hidden(C_126,k2_relat_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_447,c_52])).

tff(c_12694,plain,(
    ! [A_312,C_313] :
      ( k1_funct_1(k4_relat_1(A_312),'#skF_4'(k4_relat_1(A_312),k1_relat_1(A_312),C_313)) = C_313
      | ~ v1_funct_1(k4_relat_1(A_312))
      | ~ v1_relat_1(k4_relat_1(A_312))
      | ~ r2_hidden(C_313,k2_relat_1(k4_relat_1(A_312)))
      | ~ v1_relat_1(A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1239])).

tff(c_12842,plain,(
    ! [C_313] :
      ( k1_funct_1(k4_relat_1(k2_funct_1('#skF_6')),'#skF_4'(k4_relat_1(k2_funct_1('#skF_6')),k2_relat_1('#skF_6'),C_313)) = C_313
      | ~ v1_funct_1(k4_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))
      | ~ r2_hidden(C_313,k2_relat_1(k4_relat_1(k2_funct_1('#skF_6'))))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_12694])).

tff(c_12878,plain,(
    ! [C_313] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_313)) = C_313
      | ~ r2_hidden(C_313,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_187,c_64,c_187,c_62,c_187,c_187,c_187,c_12842])).

tff(c_2107,plain,(
    ! [A_147,C_148] :
      ( r2_hidden(k4_tarski('#skF_4'(k4_relat_1(A_147),k1_relat_1(A_147),C_148),C_148),k4_relat_1(A_147))
      | ~ r2_hidden(C_148,k2_relat_1(k4_relat_1(A_147)))
      | ~ v1_relat_1(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_447])).

tff(c_22,plain,(
    ! [A_25,C_27,B_26] :
      ( r2_hidden(A_25,k1_relat_1(C_27))
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5996,plain,(
    ! [A_230,C_231] :
      ( r2_hidden('#skF_4'(k4_relat_1(A_230),k1_relat_1(A_230),C_231),k1_relat_1(k4_relat_1(A_230)))
      | ~ v1_relat_1(k4_relat_1(A_230))
      | ~ r2_hidden(C_231,k2_relat_1(k4_relat_1(A_230)))
      | ~ v1_relat_1(A_230) ) ),
    inference(resolution,[status(thm)],[c_2107,c_22])).

tff(c_6086,plain,(
    ! [C_231] :
      ( r2_hidden('#skF_4'(k4_relat_1(k2_funct_1('#skF_6')),k2_relat_1('#skF_6'),C_231),k1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))))
      | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))
      | ~ r2_hidden(C_231,k2_relat_1(k4_relat_1(k2_funct_1('#skF_6'))))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_5996])).

tff(c_6123,plain,(
    ! [C_231] :
      ( r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_231),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_231,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_187,c_64,c_187,c_187,c_187,c_6086])).

tff(c_12889,plain,(
    ! [C_314] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_314)) = C_314
      | ~ r2_hidden(C_314,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_187,c_64,c_187,c_62,c_187,c_187,c_187,c_12842])).

tff(c_48,plain,(
    ! [B_39,A_38] :
      ( k1_funct_1(k2_funct_1(B_39),k1_funct_1(B_39,A_38)) = A_38
      | ~ r2_hidden(A_38,k1_relat_1(B_39))
      | ~ v2_funct_1(B_39)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12928,plain,(
    ! [C_314] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_314) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_314)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_314),k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_314,k2_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12889,c_48])).

tff(c_13235,plain,(
    ! [C_319] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_319) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_319)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_319),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_319,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_12928])).

tff(c_13247,plain,(
    ! [C_320] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_320) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_320)
      | ~ r2_hidden(C_320,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6123,c_13235])).

tff(c_13432,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_13247])).

tff(c_56,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_86,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_13433,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13432,c_86])).

tff(c_13480,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12878,c_13433])).

tff(c_13487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13480])).

tff(c_13489,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_13567,plain,(
    ! [A_331] :
      ( k4_relat_1(A_331) = k2_funct_1(A_331)
      | ~ v2_funct_1(A_331)
      | ~ v1_funct_1(A_331)
      | ~ v1_relat_1(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_13570,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_13567])).

tff(c_13573,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_13570])).

tff(c_13586,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_13573,c_14])).

tff(c_13596,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_13586])).

tff(c_36,plain,(
    ! [A_32] :
      ( v1_funct_1(k2_funct_1(A_32))
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_13577,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_13573,c_26])).

tff(c_13590,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_13577])).

tff(c_13580,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_13573,c_24])).

tff(c_13592,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_13580])).

tff(c_13878,plain,(
    ! [A_350,C_351] :
      ( r2_hidden(k4_tarski(A_350,k1_funct_1(C_351,A_350)),C_351)
      | ~ r2_hidden(A_350,k1_relat_1(C_351))
      | ~ v1_funct_1(C_351)
      | ~ v1_relat_1(C_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14301,plain,(
    ! [C_380,A_381] :
      ( r2_hidden(k1_funct_1(C_380,A_381),k2_relat_1(C_380))
      | ~ r2_hidden(A_381,k1_relat_1(C_380))
      | ~ v1_funct_1(C_380)
      | ~ v1_relat_1(C_380) ) ),
    inference(resolution,[status(thm)],[c_13878,c_4])).

tff(c_14307,plain,(
    ! [A_381] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_381),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_381,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13592,c_14301])).

tff(c_14320,plain,(
    ! [A_381] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_381),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_381,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13596,c_13590,c_14307])).

tff(c_14329,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_14320])).

tff(c_14332,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_14329])).

tff(c_14336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_14332])).

tff(c_14338,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_14320])).

tff(c_32,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k6_relat_1(k2_relat_1(A_30))) = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_13630,plain,
    ( k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13592,c_32])).

tff(c_13634,plain,(
    k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13596,c_13630])).

tff(c_40,plain,(
    ! [A_33] : v1_relat_1(k6_relat_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_13642,plain,(
    ! [A_335,B_336] :
      ( k10_relat_1(A_335,k1_relat_1(B_336)) = k1_relat_1(k5_relat_1(A_335,B_336))
      | ~ v1_relat_1(B_336)
      | ~ v1_relat_1(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_13657,plain,(
    ! [A_335,A_29] :
      ( k1_relat_1(k5_relat_1(A_335,k6_relat_1(A_29))) = k10_relat_1(A_335,A_29)
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(A_335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_13642])).

tff(c_13664,plain,(
    ! [A_337,A_338] :
      ( k1_relat_1(k5_relat_1(A_337,k6_relat_1(A_338))) = k10_relat_1(A_337,A_338)
      | ~ v1_relat_1(A_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_13657])).

tff(c_13676,plain,
    ( k10_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13634,c_13664])).

tff(c_13686,plain,(
    k10_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13596,c_13590,c_13676])).

tff(c_18,plain,(
    ! [A_22,B_24] :
      ( k10_relat_1(A_22,k1_relat_1(B_24)) = k1_relat_1(k5_relat_1(A_22,B_24))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_13713,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13686,c_18])).

tff(c_13720,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13596,c_64,c_13713])).

tff(c_15346,plain,(
    ! [C_425,B_426,A_427] :
      ( k1_funct_1(k5_relat_1(C_425,B_426),A_427) = k1_funct_1(B_426,k1_funct_1(C_425,A_427))
      | ~ r2_hidden(A_427,k1_relat_1(k5_relat_1(C_425,B_426)))
      | ~ v1_funct_1(C_425)
      | ~ v1_relat_1(C_425)
      | ~ v1_funct_1(B_426)
      | ~ v1_relat_1(B_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_15451,plain,(
    ! [A_427] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),A_427) = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_427))
      | ~ r2_hidden(A_427,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13720,c_15346])).

tff(c_15849,plain,(
    ! [A_434] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),A_434) = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_434))
      | ~ r2_hidden(A_434,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_13596,c_14338,c_15451])).

tff(c_13488,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_15868,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15849,c_13488])).

tff(c_15882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13489,c_15868])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.24/3.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.31/4.00  
% 10.31/4.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.31/4.00  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 10.31/4.00  
% 10.31/4.00  %Foreground sorts:
% 10.31/4.00  
% 10.31/4.00  
% 10.31/4.00  %Background operators:
% 10.31/4.00  
% 10.31/4.00  
% 10.31/4.00  %Foreground operators:
% 10.31/4.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.31/4.00  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.31/4.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.31/4.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.31/4.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.31/4.00  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.31/4.00  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.31/4.00  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.31/4.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.31/4.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.31/4.00  tff('#skF_5', type, '#skF_5': $i).
% 10.31/4.00  tff('#skF_6', type, '#skF_6': $i).
% 10.31/4.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.31/4.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.31/4.00  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.31/4.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.31/4.00  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.31/4.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.31/4.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.31/4.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.31/4.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.31/4.00  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 10.31/4.00  
% 10.31/4.02  tff(f_138, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 10.31/4.02  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 10.31/4.02  tff(f_37, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 10.31/4.02  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 10.31/4.02  tff(f_62, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 10.31/4.02  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 10.31/4.02  tff(f_125, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 10.31/4.02  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 10.31/4.02  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 10.31/4.02  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.31/4.02  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 10.31/4.02  tff(f_90, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.31/4.02  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.31/4.02  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 10.31/4.02  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 10.31/4.02  tff(c_58, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.31/4.02  tff(c_64, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.31/4.02  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.31/4.02  tff(c_60, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.31/4.02  tff(c_160, plain, (![A_58]: (k4_relat_1(A_58)=k2_funct_1(A_58) | ~v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.31/4.02  tff(c_163, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_160])).
% 10.31/4.02  tff(c_166, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_163])).
% 10.31/4.02  tff(c_14, plain, (![A_20]: (v1_relat_1(k4_relat_1(A_20)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.31/4.02  tff(c_179, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_166, c_14])).
% 10.31/4.02  tff(c_189, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_179])).
% 10.31/4.02  tff(c_16, plain, (![A_21]: (k4_relat_1(k4_relat_1(A_21))=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.31/4.02  tff(c_176, plain, (k4_relat_1(k2_funct_1('#skF_6'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_166, c_16])).
% 10.31/4.02  tff(c_187, plain, (k4_relat_1(k2_funct_1('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_176])).
% 10.31/4.02  tff(c_26, plain, (![A_28]: (k1_relat_1(k4_relat_1(A_28))=k2_relat_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.31/4.02  tff(c_170, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_166, c_26])).
% 10.31/4.02  tff(c_183, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_170])).
% 10.31/4.02  tff(c_24, plain, (![A_28]: (k2_relat_1(k4_relat_1(A_28))=k1_relat_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.31/4.02  tff(c_447, plain, (![A_75, C_76]: (r2_hidden(k4_tarski('#skF_4'(A_75, k2_relat_1(A_75), C_76), C_76), A_75) | ~r2_hidden(C_76, k2_relat_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.31/4.02  tff(c_52, plain, (![C_42, A_40, B_41]: (k1_funct_1(C_42, A_40)=B_41 | ~r2_hidden(k4_tarski(A_40, B_41), C_42) | ~v1_funct_1(C_42) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.31/4.02  tff(c_1239, plain, (![A_125, C_126]: (k1_funct_1(A_125, '#skF_4'(A_125, k2_relat_1(A_125), C_126))=C_126 | ~v1_funct_1(A_125) | ~v1_relat_1(A_125) | ~r2_hidden(C_126, k2_relat_1(A_125)))), inference(resolution, [status(thm)], [c_447, c_52])).
% 10.31/4.02  tff(c_12694, plain, (![A_312, C_313]: (k1_funct_1(k4_relat_1(A_312), '#skF_4'(k4_relat_1(A_312), k1_relat_1(A_312), C_313))=C_313 | ~v1_funct_1(k4_relat_1(A_312)) | ~v1_relat_1(k4_relat_1(A_312)) | ~r2_hidden(C_313, k2_relat_1(k4_relat_1(A_312))) | ~v1_relat_1(A_312))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1239])).
% 10.31/4.02  tff(c_12842, plain, (![C_313]: (k1_funct_1(k4_relat_1(k2_funct_1('#skF_6')), '#skF_4'(k4_relat_1(k2_funct_1('#skF_6')), k2_relat_1('#skF_6'), C_313))=C_313 | ~v1_funct_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden(C_313, k2_relat_1(k4_relat_1(k2_funct_1('#skF_6')))) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_183, c_12694])).
% 10.31/4.02  tff(c_12878, plain, (![C_313]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_313))=C_313 | ~r2_hidden(C_313, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_187, c_64, c_187, c_62, c_187, c_187, c_187, c_12842])).
% 10.31/4.02  tff(c_2107, plain, (![A_147, C_148]: (r2_hidden(k4_tarski('#skF_4'(k4_relat_1(A_147), k1_relat_1(A_147), C_148), C_148), k4_relat_1(A_147)) | ~r2_hidden(C_148, k2_relat_1(k4_relat_1(A_147))) | ~v1_relat_1(A_147))), inference(superposition, [status(thm), theory('equality')], [c_24, c_447])).
% 10.31/4.02  tff(c_22, plain, (![A_25, C_27, B_26]: (r2_hidden(A_25, k1_relat_1(C_27)) | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.31/4.02  tff(c_5996, plain, (![A_230, C_231]: (r2_hidden('#skF_4'(k4_relat_1(A_230), k1_relat_1(A_230), C_231), k1_relat_1(k4_relat_1(A_230))) | ~v1_relat_1(k4_relat_1(A_230)) | ~r2_hidden(C_231, k2_relat_1(k4_relat_1(A_230))) | ~v1_relat_1(A_230))), inference(resolution, [status(thm)], [c_2107, c_22])).
% 10.31/4.02  tff(c_6086, plain, (![C_231]: (r2_hidden('#skF_4'(k4_relat_1(k2_funct_1('#skF_6')), k2_relat_1('#skF_6'), C_231), k1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden(C_231, k2_relat_1(k4_relat_1(k2_funct_1('#skF_6')))) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_183, c_5996])).
% 10.31/4.02  tff(c_6123, plain, (![C_231]: (r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_231), k1_relat_1('#skF_6')) | ~r2_hidden(C_231, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_187, c_64, c_187, c_187, c_187, c_6086])).
% 10.31/4.02  tff(c_12889, plain, (![C_314]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_314))=C_314 | ~r2_hidden(C_314, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_187, c_64, c_187, c_62, c_187, c_187, c_187, c_12842])).
% 10.31/4.02  tff(c_48, plain, (![B_39, A_38]: (k1_funct_1(k2_funct_1(B_39), k1_funct_1(B_39, A_38))=A_38 | ~r2_hidden(A_38, k1_relat_1(B_39)) | ~v2_funct_1(B_39) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.31/4.02  tff(c_12928, plain, (![C_314]: (k1_funct_1(k2_funct_1('#skF_6'), C_314)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_314) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_314), k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(C_314, k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_12889, c_48])).
% 10.31/4.02  tff(c_13235, plain, (![C_319]: (k1_funct_1(k2_funct_1('#skF_6'), C_319)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_319) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_319), k1_relat_1('#skF_6')) | ~r2_hidden(C_319, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_12928])).
% 10.31/4.02  tff(c_13247, plain, (![C_320]: (k1_funct_1(k2_funct_1('#skF_6'), C_320)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_320) | ~r2_hidden(C_320, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_6123, c_13235])).
% 10.31/4.02  tff(c_13432, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_58, c_13247])).
% 10.31/4.02  tff(c_56, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.31/4.02  tff(c_86, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_56])).
% 10.31/4.02  tff(c_13433, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13432, c_86])).
% 10.31/4.02  tff(c_13480, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12878, c_13433])).
% 10.31/4.02  tff(c_13487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_13480])).
% 10.31/4.02  tff(c_13489, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_56])).
% 10.31/4.02  tff(c_13567, plain, (![A_331]: (k4_relat_1(A_331)=k2_funct_1(A_331) | ~v2_funct_1(A_331) | ~v1_funct_1(A_331) | ~v1_relat_1(A_331))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.31/4.02  tff(c_13570, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_13567])).
% 10.31/4.02  tff(c_13573, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_13570])).
% 10.31/4.02  tff(c_13586, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_13573, c_14])).
% 10.31/4.02  tff(c_13596, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_13586])).
% 10.31/4.02  tff(c_36, plain, (![A_32]: (v1_funct_1(k2_funct_1(A_32)) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.31/4.02  tff(c_13577, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_13573, c_26])).
% 10.31/4.02  tff(c_13590, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_13577])).
% 10.31/4.02  tff(c_13580, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_13573, c_24])).
% 10.31/4.02  tff(c_13592, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_13580])).
% 10.31/4.02  tff(c_13878, plain, (![A_350, C_351]: (r2_hidden(k4_tarski(A_350, k1_funct_1(C_351, A_350)), C_351) | ~r2_hidden(A_350, k1_relat_1(C_351)) | ~v1_funct_1(C_351) | ~v1_relat_1(C_351))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.31/4.02  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k2_relat_1(A_1)) | ~r2_hidden(k4_tarski(D_19, C_16), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.31/4.02  tff(c_14301, plain, (![C_380, A_381]: (r2_hidden(k1_funct_1(C_380, A_381), k2_relat_1(C_380)) | ~r2_hidden(A_381, k1_relat_1(C_380)) | ~v1_funct_1(C_380) | ~v1_relat_1(C_380))), inference(resolution, [status(thm)], [c_13878, c_4])).
% 10.31/4.02  tff(c_14307, plain, (![A_381]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_381), k1_relat_1('#skF_6')) | ~r2_hidden(A_381, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_13592, c_14301])).
% 10.31/4.02  tff(c_14320, plain, (![A_381]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_381), k1_relat_1('#skF_6')) | ~r2_hidden(A_381, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_13596, c_13590, c_14307])).
% 10.31/4.02  tff(c_14329, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_14320])).
% 10.31/4.02  tff(c_14332, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_14329])).
% 10.31/4.02  tff(c_14336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_14332])).
% 10.31/4.02  tff(c_14338, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_14320])).
% 10.31/4.02  tff(c_32, plain, (![A_30]: (k5_relat_1(A_30, k6_relat_1(k2_relat_1(A_30)))=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.31/4.02  tff(c_13630, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13592, c_32])).
% 10.31/4.02  tff(c_13634, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13596, c_13630])).
% 10.31/4.02  tff(c_40, plain, (![A_33]: (v1_relat_1(k6_relat_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.31/4.02  tff(c_28, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.31/4.02  tff(c_13642, plain, (![A_335, B_336]: (k10_relat_1(A_335, k1_relat_1(B_336))=k1_relat_1(k5_relat_1(A_335, B_336)) | ~v1_relat_1(B_336) | ~v1_relat_1(A_335))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.31/4.02  tff(c_13657, plain, (![A_335, A_29]: (k1_relat_1(k5_relat_1(A_335, k6_relat_1(A_29)))=k10_relat_1(A_335, A_29) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(A_335))), inference(superposition, [status(thm), theory('equality')], [c_28, c_13642])).
% 10.31/4.02  tff(c_13664, plain, (![A_337, A_338]: (k1_relat_1(k5_relat_1(A_337, k6_relat_1(A_338)))=k10_relat_1(A_337, A_338) | ~v1_relat_1(A_337))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_13657])).
% 10.31/4.02  tff(c_13676, plain, (k10_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13634, c_13664])).
% 10.31/4.02  tff(c_13686, plain, (k10_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13596, c_13590, c_13676])).
% 10.31/4.02  tff(c_18, plain, (![A_22, B_24]: (k10_relat_1(A_22, k1_relat_1(B_24))=k1_relat_1(k5_relat_1(A_22, B_24)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.31/4.02  tff(c_13713, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13686, c_18])).
% 10.31/4.02  tff(c_13720, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13596, c_64, c_13713])).
% 10.31/4.02  tff(c_15346, plain, (![C_425, B_426, A_427]: (k1_funct_1(k5_relat_1(C_425, B_426), A_427)=k1_funct_1(B_426, k1_funct_1(C_425, A_427)) | ~r2_hidden(A_427, k1_relat_1(k5_relat_1(C_425, B_426))) | ~v1_funct_1(C_425) | ~v1_relat_1(C_425) | ~v1_funct_1(B_426) | ~v1_relat_1(B_426))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.31/4.02  tff(c_15451, plain, (![A_427]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), A_427)=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_427)) | ~r2_hidden(A_427, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13720, c_15346])).
% 10.31/4.02  tff(c_15849, plain, (![A_434]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), A_434)=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_434)) | ~r2_hidden(A_434, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_13596, c_14338, c_15451])).
% 10.31/4.02  tff(c_13488, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_56])).
% 10.31/4.02  tff(c_15868, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_15849, c_13488])).
% 10.31/4.02  tff(c_15882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_13489, c_15868])).
% 10.31/4.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.31/4.02  
% 10.31/4.02  Inference rules
% 10.31/4.02  ----------------------
% 10.31/4.02  #Ref     : 0
% 10.31/4.02  #Sup     : 3787
% 10.31/4.02  #Fact    : 0
% 10.31/4.02  #Define  : 0
% 10.31/4.02  #Split   : 19
% 10.31/4.02  #Chain   : 0
% 10.31/4.02  #Close   : 0
% 10.31/4.02  
% 10.31/4.02  Ordering : KBO
% 10.31/4.02  
% 10.31/4.02  Simplification rules
% 10.31/4.02  ----------------------
% 10.31/4.02  #Subsume      : 592
% 10.31/4.02  #Demod        : 6706
% 10.31/4.02  #Tautology    : 1010
% 10.31/4.02  #SimpNegUnit  : 0
% 10.31/4.02  #BackRed      : 3
% 10.31/4.02  
% 10.31/4.02  #Partial instantiations: 0
% 10.31/4.02  #Strategies tried      : 1
% 10.31/4.02  
% 10.31/4.02  Timing (in seconds)
% 10.31/4.02  ----------------------
% 10.31/4.02  Preprocessing        : 0.36
% 10.31/4.02  Parsing              : 0.19
% 10.31/4.02  CNF conversion       : 0.03
% 10.31/4.02  Main loop            : 2.83
% 10.31/4.02  Inferencing          : 0.84
% 10.31/4.02  Reduction            : 1.11
% 10.31/4.02  Demodulation         : 0.86
% 10.31/4.02  BG Simplification    : 0.13
% 10.31/4.02  Subsumption          : 0.60
% 10.31/4.02  Abstraction          : 0.18
% 10.31/4.02  MUC search           : 0.00
% 10.31/4.02  Cooper               : 0.00
% 10.31/4.02  Total                : 3.22
% 10.31/4.02  Index Insertion      : 0.00
% 10.31/4.02  Index Deletion       : 0.00
% 10.31/4.02  Index Matching       : 0.00
% 10.31/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
