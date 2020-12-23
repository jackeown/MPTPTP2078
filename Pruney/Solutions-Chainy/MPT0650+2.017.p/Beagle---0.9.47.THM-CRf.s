%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:46 EST 2020

% Result     : Theorem 10.38s
% Output     : CNFRefutation 10.45s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 969 expanded)
%              Number of leaves         :   37 ( 367 expanded)
%              Depth                    :   23
%              Number of atoms          :  322 (2824 expanded)
%              Number of equality atoms :   86 ( 865 expanded)
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

tff(f_136,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_80,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_64,axiom,(
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

tff(f_123,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_56,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_62,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_58,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_157,plain,(
    ! [A_57] :
      ( k4_relat_1(A_57) = k2_funct_1(A_57)
      | ~ v2_funct_1(A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_160,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_157])).

tff(c_163,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_160])).

tff(c_14,plain,(
    ! [A_20] :
      ( v1_relat_1(k4_relat_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_14])).

tff(c_186,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_176])).

tff(c_18,plain,(
    ! [A_22] :
      ( k4_relat_1(k4_relat_1(A_22)) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_173,plain,
    ( k4_relat_1(k2_funct_1('#skF_6')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_18])).

tff(c_184,plain,(
    k4_relat_1(k2_funct_1('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_173])).

tff(c_28,plain,(
    ! [A_29] :
      ( k1_relat_1(k4_relat_1(A_29)) = k2_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_167,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_28])).

tff(c_180,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_167])).

tff(c_26,plain,(
    ! [A_29] :
      ( k2_relat_1(k4_relat_1(A_29)) = k1_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_443,plain,(
    ! [A_71,C_72] :
      ( r2_hidden(k4_tarski('#skF_4'(A_71,k2_relat_1(A_71),C_72),C_72),A_71)
      | ~ r2_hidden(C_72,k2_relat_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2250,plain,(
    ! [A_148,C_149] :
      ( r2_hidden(k4_tarski('#skF_4'(k4_relat_1(A_148),k1_relat_1(A_148),C_149),C_149),k4_relat_1(A_148))
      | ~ r2_hidden(C_149,k2_relat_1(k4_relat_1(A_148)))
      | ~ v1_relat_1(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_443])).

tff(c_50,plain,(
    ! [C_42,A_40,B_41] :
      ( k1_funct_1(C_42,A_40) = B_41
      | ~ r2_hidden(k4_tarski(A_40,B_41),C_42)
      | ~ v1_funct_1(C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_11608,plain,(
    ! [A_288,C_289] :
      ( k1_funct_1(k4_relat_1(A_288),'#skF_4'(k4_relat_1(A_288),k1_relat_1(A_288),C_289)) = C_289
      | ~ v1_funct_1(k4_relat_1(A_288))
      | ~ v1_relat_1(k4_relat_1(A_288))
      | ~ r2_hidden(C_289,k2_relat_1(k4_relat_1(A_288)))
      | ~ v1_relat_1(A_288) ) ),
    inference(resolution,[status(thm)],[c_2250,c_50])).

tff(c_11750,plain,(
    ! [C_289] :
      ( k1_funct_1(k4_relat_1(k2_funct_1('#skF_6')),'#skF_4'(k4_relat_1(k2_funct_1('#skF_6')),k2_relat_1('#skF_6'),C_289)) = C_289
      | ~ v1_funct_1(k4_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))
      | ~ r2_hidden(C_289,k2_relat_1(k4_relat_1(k2_funct_1('#skF_6'))))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_11608])).

tff(c_11786,plain,(
    ! [C_289] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_289)) = C_289
      | ~ r2_hidden(C_289,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_184,c_62,c_184,c_60,c_184,c_184,c_184,c_11750])).

tff(c_24,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(A_26,k1_relat_1(C_28))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_639,plain,(
    ! [A_93,C_94] :
      ( r2_hidden('#skF_4'(A_93,k2_relat_1(A_93),C_94),k1_relat_1(A_93))
      | ~ v1_relat_1(A_93)
      | ~ r2_hidden(C_94,k2_relat_1(A_93)) ) ),
    inference(resolution,[status(thm)],[c_443,c_24])).

tff(c_5759,plain,(
    ! [A_226,C_227] :
      ( r2_hidden('#skF_4'(k4_relat_1(A_226),k1_relat_1(A_226),C_227),k1_relat_1(k4_relat_1(A_226)))
      | ~ v1_relat_1(k4_relat_1(A_226))
      | ~ r2_hidden(C_227,k2_relat_1(k4_relat_1(A_226)))
      | ~ v1_relat_1(A_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_639])).

tff(c_5849,plain,(
    ! [C_227] :
      ( r2_hidden('#skF_4'(k4_relat_1(k2_funct_1('#skF_6')),k2_relat_1('#skF_6'),C_227),k1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))))
      | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))
      | ~ r2_hidden(C_227,k2_relat_1(k4_relat_1(k2_funct_1('#skF_6'))))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_5759])).

tff(c_5886,plain,(
    ! [C_227] :
      ( r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_227),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_227,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_184,c_62,c_184,c_184,c_184,c_5849])).

tff(c_11797,plain,(
    ! [C_290] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_290)) = C_290
      | ~ r2_hidden(C_290,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_184,c_62,c_184,c_60,c_184,c_184,c_184,c_11750])).

tff(c_38,plain,(
    ! [A_33] :
      ( v1_funct_1(k2_funct_1(A_33))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_170,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_26])).

tff(c_182,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_170])).

tff(c_542,plain,(
    ! [A_77,C_78] :
      ( r2_hidden(k4_tarski(A_77,k1_funct_1(C_78,A_77)),C_78)
      | ~ r2_hidden(A_77,k1_relat_1(C_78))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_623,plain,(
    ! [C_86,A_87] :
      ( r2_hidden(k1_funct_1(C_86,A_87),k2_relat_1(C_86))
      | ~ r2_hidden(A_87,k1_relat_1(C_86))
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_542,c_4])).

tff(c_626,plain,(
    ! [A_87] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_87),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_87,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_623])).

tff(c_634,plain,(
    ! [A_87] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_87),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_87,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_180,c_626])).

tff(c_681,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_634])).

tff(c_684,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_681])).

tff(c_688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_684])).

tff(c_690,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_130,plain,(
    ! [A_52] :
      ( k5_relat_1(A_52,k6_relat_1(k2_relat_1(A_52))) = A_52
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_468,plain,(
    ! [A_76] :
      ( k5_relat_1(k4_relat_1(A_76),k6_relat_1(k1_relat_1(A_76))) = k4_relat_1(A_76)
      | ~ v1_relat_1(k4_relat_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_130])).

tff(c_2816,plain,(
    ! [A_168] :
      ( k5_relat_1(A_168,k6_relat_1(k1_relat_1(k4_relat_1(A_168)))) = k4_relat_1(k4_relat_1(A_168))
      | ~ v1_relat_1(k4_relat_1(k4_relat_1(A_168)))
      | ~ v1_relat_1(k4_relat_1(A_168))
      | ~ v1_relat_1(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_468])).

tff(c_3473,plain,(
    ! [A_193] :
      ( k5_relat_1(A_193,k6_relat_1(k2_relat_1(A_193))) = k4_relat_1(k4_relat_1(A_193))
      | ~ v1_relat_1(k4_relat_1(k4_relat_1(A_193)))
      | ~ v1_relat_1(k4_relat_1(A_193))
      | ~ v1_relat_1(A_193)
      | ~ v1_relat_1(A_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2816])).

tff(c_3528,plain,(
    ! [A_196] :
      ( k5_relat_1(A_196,k6_relat_1(k2_relat_1(A_196))) = k4_relat_1(k4_relat_1(A_196))
      | ~ v1_relat_1(A_196)
      | ~ v1_relat_1(k4_relat_1(A_196)) ) ),
    inference(resolution,[status(thm)],[c_14,c_3473])).

tff(c_16,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_30] : k1_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_232,plain,(
    ! [A_61,B_62] :
      ( k10_relat_1(A_61,k1_relat_1(B_62)) = k1_relat_1(k5_relat_1(A_61,B_62))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_247,plain,(
    ! [A_61,A_30] :
      ( k1_relat_1(k5_relat_1(A_61,k6_relat_1(A_30))) = k10_relat_1(A_61,A_30)
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_232])).

tff(c_253,plain,(
    ! [A_61,A_30] :
      ( k1_relat_1(k5_relat_1(A_61,k6_relat_1(A_30))) = k10_relat_1(A_61,A_30)
      | ~ v1_relat_1(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_247])).

tff(c_3582,plain,(
    ! [A_197] :
      ( k1_relat_1(k4_relat_1(k4_relat_1(A_197))) = k10_relat_1(A_197,k2_relat_1(A_197))
      | ~ v1_relat_1(A_197)
      | ~ v1_relat_1(A_197)
      | ~ v1_relat_1(k4_relat_1(A_197)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3528,c_253])).

tff(c_3752,plain,(
    ! [A_199] :
      ( k10_relat_1(A_199,k2_relat_1(A_199)) = k2_relat_1(k4_relat_1(A_199))
      | ~ v1_relat_1(k4_relat_1(A_199))
      | ~ v1_relat_1(A_199)
      | ~ v1_relat_1(A_199)
      | ~ v1_relat_1(k4_relat_1(A_199)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3582,c_28])).

tff(c_3780,plain,(
    ! [A_200] :
      ( k10_relat_1(A_200,k2_relat_1(A_200)) = k2_relat_1(k4_relat_1(A_200))
      | ~ v1_relat_1(k4_relat_1(A_200))
      | ~ v1_relat_1(A_200) ) ),
    inference(resolution,[status(thm)],[c_14,c_3752])).

tff(c_3825,plain,(
    ! [A_203] :
      ( k10_relat_1(A_203,k2_relat_1(A_203)) = k2_relat_1(k4_relat_1(A_203))
      | ~ v1_relat_1(A_203) ) ),
    inference(resolution,[status(thm)],[c_14,c_3780])).

tff(c_3891,plain,(
    ! [A_204] :
      ( k10_relat_1(k4_relat_1(A_204),k1_relat_1(A_204)) = k2_relat_1(k4_relat_1(k4_relat_1(A_204)))
      | ~ v1_relat_1(k4_relat_1(A_204))
      | ~ v1_relat_1(A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3825])).

tff(c_20,plain,(
    ! [A_23,B_25] :
      ( k10_relat_1(A_23,k1_relat_1(B_25)) = k1_relat_1(k5_relat_1(A_23,B_25))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4306,plain,(
    ! [A_209] :
      ( k2_relat_1(k4_relat_1(k4_relat_1(A_209))) = k1_relat_1(k5_relat_1(k4_relat_1(A_209),A_209))
      | ~ v1_relat_1(A_209)
      | ~ v1_relat_1(k4_relat_1(A_209))
      | ~ v1_relat_1(k4_relat_1(A_209))
      | ~ v1_relat_1(A_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3891,c_20])).

tff(c_4460,plain,
    ( k2_relat_1(k4_relat_1(k4_relat_1(k2_funct_1('#skF_6')))) = k1_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_4306])).

tff(c_4498,plain,(
    k1_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6'))) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_62,c_184,c_62,c_184,c_186,c_182,c_163,c_184,c_4460])).

tff(c_42,plain,(
    ! [C_37,B_35,A_34] :
      ( k1_funct_1(k5_relat_1(C_37,B_35),A_34) = k1_funct_1(B_35,k1_funct_1(C_37,A_34))
      | ~ r2_hidden(A_34,k1_relat_1(k5_relat_1(C_37,B_35)))
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4519,plain,(
    ! [A_34] :
      ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),A_34) = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_34))
      | ~ r2_hidden(A_34,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4498,c_42])).

tff(c_4561,plain,(
    ! [A_210] :
      ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),A_210) = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_210))
      | ~ r2_hidden(A_210,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_690,c_62,c_60,c_4519])).

tff(c_44,plain,(
    ! [B_39,A_38] :
      ( k1_funct_1(k5_relat_1(B_39,k2_funct_1(B_39)),A_38) = A_38
      | ~ r2_hidden(A_38,k1_relat_1(B_39))
      | ~ v2_funct_1(B_39)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4584,plain,(
    ! [A_210] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_210)) = A_210
      | ~ r2_hidden(A_210,k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(A_210,k1_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4561,c_44])).

tff(c_4611,plain,(
    ! [A_210] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_210)) = A_210
      | ~ r2_hidden(A_210,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_4584])).

tff(c_11853,plain,(
    ! [C_291] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_291) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_291)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_291),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_291,k2_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11797,c_4611])).

tff(c_11865,plain,(
    ! [C_292] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_292) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_292)
      | ~ r2_hidden(C_292,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_5886,c_11853])).

tff(c_12048,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_11865])).

tff(c_54,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_103,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_12049,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12048,c_103])).

tff(c_12086,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11786,c_12049])).

tff(c_12093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12086])).

tff(c_12095,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_12153,plain,(
    ! [A_302] :
      ( k4_relat_1(A_302) = k2_funct_1(A_302)
      | ~ v2_funct_1(A_302)
      | ~ v1_funct_1(A_302)
      | ~ v1_relat_1(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12156,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_12153])).

tff(c_12159,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_12156])).

tff(c_12172,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12159,c_14])).

tff(c_12182,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12172])).

tff(c_12163,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12159,c_28])).

tff(c_12176,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12163])).

tff(c_12166,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12159,c_26])).

tff(c_12178,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12166])).

tff(c_12628,plain,(
    ! [A_329,C_330] :
      ( r2_hidden(k4_tarski(A_329,k1_funct_1(C_330,A_329)),C_330)
      | ~ r2_hidden(A_329,k1_relat_1(C_330))
      | ~ v1_funct_1(C_330)
      | ~ v1_relat_1(C_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12648,plain,(
    ! [C_332,A_333] :
      ( r2_hidden(k1_funct_1(C_332,A_333),k2_relat_1(C_332))
      | ~ r2_hidden(A_333,k1_relat_1(C_332))
      | ~ v1_funct_1(C_332)
      | ~ v1_relat_1(C_332) ) ),
    inference(resolution,[status(thm)],[c_12628,c_4])).

tff(c_12651,plain,(
    ! [A_333] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_333),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_333,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12178,c_12648])).

tff(c_12662,plain,(
    ! [A_333] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_333),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_333,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12182,c_12176,c_12651])).

tff(c_12707,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_12662])).

tff(c_12710,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_12707])).

tff(c_12714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_12710])).

tff(c_12716,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_12662])).

tff(c_34,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k6_relat_1(k2_relat_1(A_31))) = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12216,plain,
    ( k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12178,c_34])).

tff(c_12220,plain,(
    k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12182,c_12216])).

tff(c_12228,plain,(
    ! [A_306,B_307] :
      ( k10_relat_1(A_306,k1_relat_1(B_307)) = k1_relat_1(k5_relat_1(A_306,B_307))
      | ~ v1_relat_1(B_307)
      | ~ v1_relat_1(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12243,plain,(
    ! [A_306,A_30] :
      ( k1_relat_1(k5_relat_1(A_306,k6_relat_1(A_30))) = k10_relat_1(A_306,A_30)
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(A_306) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_12228])).

tff(c_12250,plain,(
    ! [A_308,A_309] :
      ( k1_relat_1(k5_relat_1(A_308,k6_relat_1(A_309))) = k10_relat_1(A_308,A_309)
      | ~ v1_relat_1(A_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12243])).

tff(c_12262,plain,
    ( k10_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12220,c_12250])).

tff(c_12272,plain,(
    k10_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12182,c_12176,c_12262])).

tff(c_12300,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12272,c_20])).

tff(c_12307,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12182,c_62,c_12300])).

tff(c_13852,plain,(
    ! [C_393,B_394,A_395] :
      ( k1_funct_1(k5_relat_1(C_393,B_394),A_395) = k1_funct_1(B_394,k1_funct_1(C_393,A_395))
      | ~ r2_hidden(A_395,k1_relat_1(k5_relat_1(C_393,B_394)))
      | ~ v1_funct_1(C_393)
      | ~ v1_relat_1(C_393)
      | ~ v1_funct_1(B_394)
      | ~ v1_relat_1(B_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_13967,plain,(
    ! [A_395] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),A_395) = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_395))
      | ~ r2_hidden(A_395,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12307,c_13852])).

tff(c_14113,plain,(
    ! [A_400] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),A_400) = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_400))
      | ~ r2_hidden(A_400,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_12182,c_12716,c_13967])).

tff(c_12094,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_14132,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14113,c_12094])).

tff(c_14146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12095,c_14132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.38/3.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.40/3.72  
% 10.40/3.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.45/3.73  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 10.45/3.73  
% 10.45/3.73  %Foreground sorts:
% 10.45/3.73  
% 10.45/3.73  
% 10.45/3.73  %Background operators:
% 10.45/3.73  
% 10.45/3.73  
% 10.45/3.73  %Foreground operators:
% 10.45/3.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.45/3.73  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.45/3.73  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.45/3.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.45/3.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.45/3.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.45/3.73  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.45/3.73  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.45/3.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.45/3.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.45/3.73  tff('#skF_5', type, '#skF_5': $i).
% 10.45/3.73  tff('#skF_6', type, '#skF_6': $i).
% 10.45/3.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.45/3.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.45/3.73  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.45/3.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.45/3.73  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.45/3.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.45/3.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.45/3.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.45/3.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.45/3.73  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 10.45/3.73  
% 10.45/3.75  tff(f_136, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 10.45/3.75  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 10.45/3.75  tff(f_37, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 10.45/3.75  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 10.45/3.75  tff(f_64, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 10.45/3.75  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 10.45/3.75  tff(f_123, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 10.45/3.75  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 10.45/3.75  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.45/3.75  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 10.45/3.75  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 10.45/3.75  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.45/3.75  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 10.45/3.75  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 10.45/3.75  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 10.45/3.75  tff(c_56, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.45/3.75  tff(c_62, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.45/3.75  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.45/3.75  tff(c_58, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.45/3.75  tff(c_157, plain, (![A_57]: (k4_relat_1(A_57)=k2_funct_1(A_57) | ~v2_funct_1(A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.45/3.75  tff(c_160, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_157])).
% 10.45/3.75  tff(c_163, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_160])).
% 10.45/3.75  tff(c_14, plain, (![A_20]: (v1_relat_1(k4_relat_1(A_20)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.45/3.75  tff(c_176, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_163, c_14])).
% 10.45/3.75  tff(c_186, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_176])).
% 10.45/3.75  tff(c_18, plain, (![A_22]: (k4_relat_1(k4_relat_1(A_22))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.45/3.75  tff(c_173, plain, (k4_relat_1(k2_funct_1('#skF_6'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_163, c_18])).
% 10.45/3.75  tff(c_184, plain, (k4_relat_1(k2_funct_1('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_173])).
% 10.45/3.75  tff(c_28, plain, (![A_29]: (k1_relat_1(k4_relat_1(A_29))=k2_relat_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.45/3.75  tff(c_167, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_163, c_28])).
% 10.45/3.75  tff(c_180, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_167])).
% 10.45/3.75  tff(c_26, plain, (![A_29]: (k2_relat_1(k4_relat_1(A_29))=k1_relat_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.45/3.75  tff(c_443, plain, (![A_71, C_72]: (r2_hidden(k4_tarski('#skF_4'(A_71, k2_relat_1(A_71), C_72), C_72), A_71) | ~r2_hidden(C_72, k2_relat_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.45/3.75  tff(c_2250, plain, (![A_148, C_149]: (r2_hidden(k4_tarski('#skF_4'(k4_relat_1(A_148), k1_relat_1(A_148), C_149), C_149), k4_relat_1(A_148)) | ~r2_hidden(C_149, k2_relat_1(k4_relat_1(A_148))) | ~v1_relat_1(A_148))), inference(superposition, [status(thm), theory('equality')], [c_26, c_443])).
% 10.45/3.75  tff(c_50, plain, (![C_42, A_40, B_41]: (k1_funct_1(C_42, A_40)=B_41 | ~r2_hidden(k4_tarski(A_40, B_41), C_42) | ~v1_funct_1(C_42) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.45/3.75  tff(c_11608, plain, (![A_288, C_289]: (k1_funct_1(k4_relat_1(A_288), '#skF_4'(k4_relat_1(A_288), k1_relat_1(A_288), C_289))=C_289 | ~v1_funct_1(k4_relat_1(A_288)) | ~v1_relat_1(k4_relat_1(A_288)) | ~r2_hidden(C_289, k2_relat_1(k4_relat_1(A_288))) | ~v1_relat_1(A_288))), inference(resolution, [status(thm)], [c_2250, c_50])).
% 10.45/3.75  tff(c_11750, plain, (![C_289]: (k1_funct_1(k4_relat_1(k2_funct_1('#skF_6')), '#skF_4'(k4_relat_1(k2_funct_1('#skF_6')), k2_relat_1('#skF_6'), C_289))=C_289 | ~v1_funct_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden(C_289, k2_relat_1(k4_relat_1(k2_funct_1('#skF_6')))) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_180, c_11608])).
% 10.45/3.75  tff(c_11786, plain, (![C_289]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_289))=C_289 | ~r2_hidden(C_289, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_184, c_62, c_184, c_60, c_184, c_184, c_184, c_11750])).
% 10.45/3.75  tff(c_24, plain, (![A_26, C_28, B_27]: (r2_hidden(A_26, k1_relat_1(C_28)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.45/3.75  tff(c_639, plain, (![A_93, C_94]: (r2_hidden('#skF_4'(A_93, k2_relat_1(A_93), C_94), k1_relat_1(A_93)) | ~v1_relat_1(A_93) | ~r2_hidden(C_94, k2_relat_1(A_93)))), inference(resolution, [status(thm)], [c_443, c_24])).
% 10.45/3.75  tff(c_5759, plain, (![A_226, C_227]: (r2_hidden('#skF_4'(k4_relat_1(A_226), k1_relat_1(A_226), C_227), k1_relat_1(k4_relat_1(A_226))) | ~v1_relat_1(k4_relat_1(A_226)) | ~r2_hidden(C_227, k2_relat_1(k4_relat_1(A_226))) | ~v1_relat_1(A_226))), inference(superposition, [status(thm), theory('equality')], [c_26, c_639])).
% 10.45/3.75  tff(c_5849, plain, (![C_227]: (r2_hidden('#skF_4'(k4_relat_1(k2_funct_1('#skF_6')), k2_relat_1('#skF_6'), C_227), k1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden(C_227, k2_relat_1(k4_relat_1(k2_funct_1('#skF_6')))) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_180, c_5759])).
% 10.45/3.75  tff(c_5886, plain, (![C_227]: (r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_227), k1_relat_1('#skF_6')) | ~r2_hidden(C_227, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_184, c_62, c_184, c_184, c_184, c_5849])).
% 10.45/3.75  tff(c_11797, plain, (![C_290]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_290))=C_290 | ~r2_hidden(C_290, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_184, c_62, c_184, c_60, c_184, c_184, c_184, c_11750])).
% 10.45/3.75  tff(c_38, plain, (![A_33]: (v1_funct_1(k2_funct_1(A_33)) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.45/3.75  tff(c_170, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_163, c_26])).
% 10.45/3.75  tff(c_182, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_170])).
% 10.45/3.75  tff(c_542, plain, (![A_77, C_78]: (r2_hidden(k4_tarski(A_77, k1_funct_1(C_78, A_77)), C_78) | ~r2_hidden(A_77, k1_relat_1(C_78)) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.45/3.75  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k2_relat_1(A_1)) | ~r2_hidden(k4_tarski(D_19, C_16), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.45/3.75  tff(c_623, plain, (![C_86, A_87]: (r2_hidden(k1_funct_1(C_86, A_87), k2_relat_1(C_86)) | ~r2_hidden(A_87, k1_relat_1(C_86)) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_542, c_4])).
% 10.45/3.75  tff(c_626, plain, (![A_87]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_87), k1_relat_1('#skF_6')) | ~r2_hidden(A_87, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_182, c_623])).
% 10.45/3.75  tff(c_634, plain, (![A_87]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_87), k1_relat_1('#skF_6')) | ~r2_hidden(A_87, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_180, c_626])).
% 10.45/3.75  tff(c_681, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_634])).
% 10.45/3.75  tff(c_684, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_681])).
% 10.45/3.75  tff(c_688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_684])).
% 10.45/3.75  tff(c_690, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_634])).
% 10.45/3.75  tff(c_130, plain, (![A_52]: (k5_relat_1(A_52, k6_relat_1(k2_relat_1(A_52)))=A_52 | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.45/3.75  tff(c_468, plain, (![A_76]: (k5_relat_1(k4_relat_1(A_76), k6_relat_1(k1_relat_1(A_76)))=k4_relat_1(A_76) | ~v1_relat_1(k4_relat_1(A_76)) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_26, c_130])).
% 10.45/3.75  tff(c_2816, plain, (![A_168]: (k5_relat_1(A_168, k6_relat_1(k1_relat_1(k4_relat_1(A_168))))=k4_relat_1(k4_relat_1(A_168)) | ~v1_relat_1(k4_relat_1(k4_relat_1(A_168))) | ~v1_relat_1(k4_relat_1(A_168)) | ~v1_relat_1(A_168))), inference(superposition, [status(thm), theory('equality')], [c_18, c_468])).
% 10.45/3.75  tff(c_3473, plain, (![A_193]: (k5_relat_1(A_193, k6_relat_1(k2_relat_1(A_193)))=k4_relat_1(k4_relat_1(A_193)) | ~v1_relat_1(k4_relat_1(k4_relat_1(A_193))) | ~v1_relat_1(k4_relat_1(A_193)) | ~v1_relat_1(A_193) | ~v1_relat_1(A_193))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2816])).
% 10.45/3.75  tff(c_3528, plain, (![A_196]: (k5_relat_1(A_196, k6_relat_1(k2_relat_1(A_196)))=k4_relat_1(k4_relat_1(A_196)) | ~v1_relat_1(A_196) | ~v1_relat_1(k4_relat_1(A_196)))), inference(resolution, [status(thm)], [c_14, c_3473])).
% 10.45/3.75  tff(c_16, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.45/3.75  tff(c_30, plain, (![A_30]: (k1_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.45/3.75  tff(c_232, plain, (![A_61, B_62]: (k10_relat_1(A_61, k1_relat_1(B_62))=k1_relat_1(k5_relat_1(A_61, B_62)) | ~v1_relat_1(B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.45/3.75  tff(c_247, plain, (![A_61, A_30]: (k1_relat_1(k5_relat_1(A_61, k6_relat_1(A_30)))=k10_relat_1(A_61, A_30) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(A_61))), inference(superposition, [status(thm), theory('equality')], [c_30, c_232])).
% 10.45/3.75  tff(c_253, plain, (![A_61, A_30]: (k1_relat_1(k5_relat_1(A_61, k6_relat_1(A_30)))=k10_relat_1(A_61, A_30) | ~v1_relat_1(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_247])).
% 10.45/3.75  tff(c_3582, plain, (![A_197]: (k1_relat_1(k4_relat_1(k4_relat_1(A_197)))=k10_relat_1(A_197, k2_relat_1(A_197)) | ~v1_relat_1(A_197) | ~v1_relat_1(A_197) | ~v1_relat_1(k4_relat_1(A_197)))), inference(superposition, [status(thm), theory('equality')], [c_3528, c_253])).
% 10.45/3.75  tff(c_3752, plain, (![A_199]: (k10_relat_1(A_199, k2_relat_1(A_199))=k2_relat_1(k4_relat_1(A_199)) | ~v1_relat_1(k4_relat_1(A_199)) | ~v1_relat_1(A_199) | ~v1_relat_1(A_199) | ~v1_relat_1(k4_relat_1(A_199)))), inference(superposition, [status(thm), theory('equality')], [c_3582, c_28])).
% 10.45/3.75  tff(c_3780, plain, (![A_200]: (k10_relat_1(A_200, k2_relat_1(A_200))=k2_relat_1(k4_relat_1(A_200)) | ~v1_relat_1(k4_relat_1(A_200)) | ~v1_relat_1(A_200))), inference(resolution, [status(thm)], [c_14, c_3752])).
% 10.45/3.75  tff(c_3825, plain, (![A_203]: (k10_relat_1(A_203, k2_relat_1(A_203))=k2_relat_1(k4_relat_1(A_203)) | ~v1_relat_1(A_203))), inference(resolution, [status(thm)], [c_14, c_3780])).
% 10.45/3.75  tff(c_3891, plain, (![A_204]: (k10_relat_1(k4_relat_1(A_204), k1_relat_1(A_204))=k2_relat_1(k4_relat_1(k4_relat_1(A_204))) | ~v1_relat_1(k4_relat_1(A_204)) | ~v1_relat_1(A_204))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3825])).
% 10.45/3.75  tff(c_20, plain, (![A_23, B_25]: (k10_relat_1(A_23, k1_relat_1(B_25))=k1_relat_1(k5_relat_1(A_23, B_25)) | ~v1_relat_1(B_25) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.45/3.75  tff(c_4306, plain, (![A_209]: (k2_relat_1(k4_relat_1(k4_relat_1(A_209)))=k1_relat_1(k5_relat_1(k4_relat_1(A_209), A_209)) | ~v1_relat_1(A_209) | ~v1_relat_1(k4_relat_1(A_209)) | ~v1_relat_1(k4_relat_1(A_209)) | ~v1_relat_1(A_209))), inference(superposition, [status(thm), theory('equality')], [c_3891, c_20])).
% 10.45/3.75  tff(c_4460, plain, (k2_relat_1(k4_relat_1(k4_relat_1(k2_funct_1('#skF_6'))))=k1_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_4306])).
% 10.45/3.75  tff(c_4498, plain, (k1_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_62, c_184, c_62, c_184, c_186, c_182, c_163, c_184, c_4460])).
% 10.45/3.75  tff(c_42, plain, (![C_37, B_35, A_34]: (k1_funct_1(k5_relat_1(C_37, B_35), A_34)=k1_funct_1(B_35, k1_funct_1(C_37, A_34)) | ~r2_hidden(A_34, k1_relat_1(k5_relat_1(C_37, B_35))) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.45/3.75  tff(c_4519, plain, (![A_34]: (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), A_34)=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_34)) | ~r2_hidden(A_34, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_4498, c_42])).
% 10.45/3.75  tff(c_4561, plain, (![A_210]: (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), A_210)=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_210)) | ~r2_hidden(A_210, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_690, c_62, c_60, c_4519])).
% 10.45/3.75  tff(c_44, plain, (![B_39, A_38]: (k1_funct_1(k5_relat_1(B_39, k2_funct_1(B_39)), A_38)=A_38 | ~r2_hidden(A_38, k1_relat_1(B_39)) | ~v2_funct_1(B_39) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.45/3.75  tff(c_4584, plain, (![A_210]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_210))=A_210 | ~r2_hidden(A_210, k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(A_210, k1_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_4561, c_44])).
% 10.45/3.75  tff(c_4611, plain, (![A_210]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_210))=A_210 | ~r2_hidden(A_210, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_4584])).
% 10.45/3.75  tff(c_11853, plain, (![C_291]: (k1_funct_1(k2_funct_1('#skF_6'), C_291)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_291) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_291), k1_relat_1('#skF_6')) | ~r2_hidden(C_291, k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_11797, c_4611])).
% 10.45/3.75  tff(c_11865, plain, (![C_292]: (k1_funct_1(k2_funct_1('#skF_6'), C_292)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_292) | ~r2_hidden(C_292, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_5886, c_11853])).
% 10.45/3.75  tff(c_12048, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_56, c_11865])).
% 10.45/3.75  tff(c_54, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.45/3.75  tff(c_103, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_54])).
% 10.45/3.75  tff(c_12049, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12048, c_103])).
% 10.45/3.75  tff(c_12086, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_11786, c_12049])).
% 10.45/3.75  tff(c_12093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_12086])).
% 10.45/3.75  tff(c_12095, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_54])).
% 10.45/3.75  tff(c_12153, plain, (![A_302]: (k4_relat_1(A_302)=k2_funct_1(A_302) | ~v2_funct_1(A_302) | ~v1_funct_1(A_302) | ~v1_relat_1(A_302))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.45/3.75  tff(c_12156, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_12153])).
% 10.45/3.75  tff(c_12159, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_12156])).
% 10.45/3.75  tff(c_12172, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12159, c_14])).
% 10.45/3.75  tff(c_12182, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12172])).
% 10.45/3.75  tff(c_12163, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12159, c_28])).
% 10.45/3.75  tff(c_12176, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12163])).
% 10.45/3.75  tff(c_12166, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12159, c_26])).
% 10.45/3.75  tff(c_12178, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12166])).
% 10.45/3.75  tff(c_12628, plain, (![A_329, C_330]: (r2_hidden(k4_tarski(A_329, k1_funct_1(C_330, A_329)), C_330) | ~r2_hidden(A_329, k1_relat_1(C_330)) | ~v1_funct_1(C_330) | ~v1_relat_1(C_330))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.45/3.75  tff(c_12648, plain, (![C_332, A_333]: (r2_hidden(k1_funct_1(C_332, A_333), k2_relat_1(C_332)) | ~r2_hidden(A_333, k1_relat_1(C_332)) | ~v1_funct_1(C_332) | ~v1_relat_1(C_332))), inference(resolution, [status(thm)], [c_12628, c_4])).
% 10.45/3.75  tff(c_12651, plain, (![A_333]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_333), k1_relat_1('#skF_6')) | ~r2_hidden(A_333, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_12178, c_12648])).
% 10.45/3.75  tff(c_12662, plain, (![A_333]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_333), k1_relat_1('#skF_6')) | ~r2_hidden(A_333, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_12182, c_12176, c_12651])).
% 10.45/3.75  tff(c_12707, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_12662])).
% 10.45/3.75  tff(c_12710, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_12707])).
% 10.45/3.75  tff(c_12714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_12710])).
% 10.45/3.75  tff(c_12716, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_12662])).
% 10.45/3.75  tff(c_34, plain, (![A_31]: (k5_relat_1(A_31, k6_relat_1(k2_relat_1(A_31)))=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.45/3.75  tff(c_12216, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12178, c_34])).
% 10.45/3.75  tff(c_12220, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12182, c_12216])).
% 10.45/3.75  tff(c_12228, plain, (![A_306, B_307]: (k10_relat_1(A_306, k1_relat_1(B_307))=k1_relat_1(k5_relat_1(A_306, B_307)) | ~v1_relat_1(B_307) | ~v1_relat_1(A_306))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.45/3.75  tff(c_12243, plain, (![A_306, A_30]: (k1_relat_1(k5_relat_1(A_306, k6_relat_1(A_30)))=k10_relat_1(A_306, A_30) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(A_306))), inference(superposition, [status(thm), theory('equality')], [c_30, c_12228])).
% 10.45/3.75  tff(c_12250, plain, (![A_308, A_309]: (k1_relat_1(k5_relat_1(A_308, k6_relat_1(A_309)))=k10_relat_1(A_308, A_309) | ~v1_relat_1(A_308))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12243])).
% 10.45/3.75  tff(c_12262, plain, (k10_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12220, c_12250])).
% 10.45/3.75  tff(c_12272, plain, (k10_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12182, c_12176, c_12262])).
% 10.45/3.75  tff(c_12300, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12272, c_20])).
% 10.45/3.75  tff(c_12307, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12182, c_62, c_12300])).
% 10.45/3.75  tff(c_13852, plain, (![C_393, B_394, A_395]: (k1_funct_1(k5_relat_1(C_393, B_394), A_395)=k1_funct_1(B_394, k1_funct_1(C_393, A_395)) | ~r2_hidden(A_395, k1_relat_1(k5_relat_1(C_393, B_394))) | ~v1_funct_1(C_393) | ~v1_relat_1(C_393) | ~v1_funct_1(B_394) | ~v1_relat_1(B_394))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.45/3.75  tff(c_13967, plain, (![A_395]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), A_395)=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_395)) | ~r2_hidden(A_395, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12307, c_13852])).
% 10.45/3.75  tff(c_14113, plain, (![A_400]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), A_400)=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_400)) | ~r2_hidden(A_400, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_12182, c_12716, c_13967])).
% 10.45/3.75  tff(c_12094, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_54])).
% 10.45/3.75  tff(c_14132, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_14113, c_12094])).
% 10.45/3.75  tff(c_14146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_12095, c_14132])).
% 10.45/3.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.45/3.75  
% 10.45/3.75  Inference rules
% 10.45/3.75  ----------------------
% 10.45/3.75  #Ref     : 0
% 10.45/3.75  #Sup     : 3385
% 10.45/3.75  #Fact    : 0
% 10.45/3.75  #Define  : 0
% 10.45/3.75  #Split   : 18
% 10.45/3.75  #Chain   : 0
% 10.45/3.75  #Close   : 0
% 10.45/3.75  
% 10.45/3.75  Ordering : KBO
% 10.45/3.75  
% 10.45/3.75  Simplification rules
% 10.45/3.75  ----------------------
% 10.45/3.75  #Subsume      : 496
% 10.45/3.75  #Demod        : 5388
% 10.45/3.75  #Tautology    : 874
% 10.45/3.75  #SimpNegUnit  : 0
% 10.45/3.75  #BackRed      : 4
% 10.45/3.75  
% 10.45/3.75  #Partial instantiations: 0
% 10.45/3.75  #Strategies tried      : 1
% 10.45/3.75  
% 10.45/3.75  Timing (in seconds)
% 10.45/3.75  ----------------------
% 10.45/3.75  Preprocessing        : 0.34
% 10.45/3.75  Parsing              : 0.18
% 10.45/3.75  CNF conversion       : 0.02
% 10.45/3.75  Main loop            : 2.63
% 10.45/3.75  Inferencing          : 0.77
% 10.45/3.75  Reduction            : 1.05
% 10.45/3.75  Demodulation         : 0.81
% 10.45/3.75  BG Simplification    : 0.12
% 10.45/3.75  Subsumption          : 0.55
% 10.45/3.75  Abstraction          : 0.19
% 10.45/3.75  MUC search           : 0.00
% 10.45/3.75  Cooper               : 0.00
% 10.45/3.75  Total                : 3.02
% 10.45/3.75  Index Insertion      : 0.00
% 10.45/3.75  Index Deletion       : 0.00
% 10.45/3.75  Index Matching       : 0.00
% 10.45/3.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
