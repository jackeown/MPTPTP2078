%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:44 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 232 expanded)
%              Number of leaves         :   26 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  216 ( 964 expanded)
%              Number of equality atoms :   30 ( 249 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k1_relat_1(B)) )
         => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
            & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_48,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_relat_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_5] :
      ( v1_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_169,plain,(
    ! [A_43,D_44] :
      ( k1_funct_1(k2_funct_1(A_43),k1_funct_1(A_43,D_44)) = D_44
      | ~ r2_hidden(D_44,k1_relat_1(A_43))
      | ~ v1_funct_1(k2_funct_1(A_43))
      | ~ v1_relat_1(k2_funct_1(A_43))
      | ~ v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,
    ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5'
    | k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_85,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_184,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_85])).

tff(c_194,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_184])).

tff(c_196,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_199,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_196])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_199])).

tff(c_204,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_208,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_204])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_208])).

tff(c_214,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_265,plain,(
    ! [A_50,D_51] :
      ( r2_hidden(k1_funct_1(A_50,D_51),k2_relat_1(A_50))
      | ~ r2_hidden(D_51,k1_relat_1(A_50))
      | ~ v1_funct_1(k2_funct_1(A_50))
      | ~ v1_relat_1(k2_funct_1(A_50))
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_268,plain,
    ( r2_hidden('#skF_5',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_265])).

tff(c_272,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_275,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_272])).

tff(c_279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_275])).

tff(c_281,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_305,plain,(
    ! [A_53,D_54] :
      ( k1_funct_1(k2_funct_1(A_53),k1_funct_1(A_53,D_54)) = D_54
      | ~ r2_hidden(D_54,k1_relat_1(A_53))
      | ~ v1_funct_1(k2_funct_1(A_53))
      | ~ v1_relat_1(k2_funct_1(A_53))
      | ~ v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_326,plain,
    ( k1_funct_1(k2_funct_1(k2_funct_1('#skF_6')),'#skF_5') = k1_funct_1('#skF_6','#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_305])).

tff(c_336,plain,
    ( k1_funct_1(k2_funct_1(k2_funct_1('#skF_6')),'#skF_5') = k1_funct_1('#skF_6','#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_326])).

tff(c_409,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_412,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_409])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_412])).

tff(c_418,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_38,plain,(
    ! [A_10,D_26] :
      ( r2_hidden(k1_funct_1(A_10,D_26),k2_relat_1(A_10))
      | ~ r2_hidden(D_26,k1_relat_1(A_10))
      | ~ v1_funct_1(k2_funct_1(A_10))
      | ~ v1_relat_1(k2_funct_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    ! [A_27] :
      ( k1_relat_1(k2_funct_1(A_27)) = k2_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_280,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | r2_hidden('#skF_5',k2_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_408,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_421,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_408])).

tff(c_423,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_421])).

tff(c_426,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_423])).

tff(c_430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_281,c_418,c_46,c_426])).

tff(c_431,plain,
    ( ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_6')))
    | ~ v2_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | r2_hidden('#skF_5',k2_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_442,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_445,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_442])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_445])).

tff(c_451,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_2,plain,(
    ! [A_1] :
      ( k10_relat_1(A_1,k2_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_219,plain,(
    ! [A_45,B_46] :
      ( k10_relat_1(A_45,k1_relat_1(B_46)) = k1_relat_1(k5_relat_1(A_45,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_228,plain,(
    ! [A_45,A_27] :
      ( k1_relat_1(k5_relat_1(A_45,k2_funct_1(A_27))) = k10_relat_1(A_45,k2_relat_1(A_27))
      | ~ v1_relat_1(k2_funct_1(A_27))
      | ~ v1_relat_1(A_45)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_219])).

tff(c_396,plain,(
    ! [C_59,B_60,A_61] :
      ( k1_funct_1(k5_relat_1(C_59,B_60),A_61) = k1_funct_1(B_60,k1_funct_1(C_59,A_61))
      | ~ r2_hidden(A_61,k1_relat_1(k5_relat_1(C_59,B_60)))
      | ~ v1_funct_1(C_59)
      | ~ v1_relat_1(C_59)
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_808,plain,(
    ! [A_90,A_91,A_92] :
      ( k1_funct_1(k5_relat_1(A_90,k2_funct_1(A_91)),A_92) = k1_funct_1(k2_funct_1(A_91),k1_funct_1(A_90,A_92))
      | ~ r2_hidden(A_92,k10_relat_1(A_90,k2_relat_1(A_91)))
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90)
      | ~ v1_funct_1(k2_funct_1(A_91))
      | ~ v1_relat_1(k2_funct_1(A_91))
      | ~ v1_relat_1(k2_funct_1(A_91))
      | ~ v1_relat_1(A_90)
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_396])).

tff(c_818,plain,(
    ! [A_93,A_94] :
      ( k1_funct_1(k5_relat_1(A_93,k2_funct_1(A_93)),A_94) = k1_funct_1(k2_funct_1(A_93),k1_funct_1(A_93,A_94))
      | ~ r2_hidden(A_94,k1_relat_1(A_93))
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93)
      | ~ v1_funct_1(k2_funct_1(A_93))
      | ~ v1_relat_1(k2_funct_1(A_93))
      | ~ v1_relat_1(k2_funct_1(A_93))
      | ~ v1_relat_1(A_93)
      | ~ v2_funct_1(A_93)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_808])).

tff(c_213,plain,(
    k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_849,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_213])).

tff(c_872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_50,c_48,c_52,c_281,c_281,c_451,c_52,c_50,c_46,c_214,c_849])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.56  
% 3.42/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.56  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 3.42/1.56  
% 3.42/1.56  %Foreground sorts:
% 3.42/1.56  
% 3.42/1.56  
% 3.42/1.56  %Background operators:
% 3.42/1.56  
% 3.42/1.56  
% 3.42/1.56  %Foreground operators:
% 3.42/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.42/1.56  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.42/1.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.42/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.42/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.42/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.42/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.42/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.56  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.42/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.42/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.42/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.42/1.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.42/1.56  
% 3.62/1.58  tff(f_112, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 3.62/1.58  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.62/1.58  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 3.62/1.58  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.62/1.58  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.62/1.58  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.62/1.58  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 3.62/1.58  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.58  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.58  tff(c_48, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.58  tff(c_8, plain, (![A_5]: (v1_relat_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.58  tff(c_6, plain, (![A_5]: (v1_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.58  tff(c_46, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.58  tff(c_169, plain, (![A_43, D_44]: (k1_funct_1(k2_funct_1(A_43), k1_funct_1(A_43, D_44))=D_44 | ~r2_hidden(D_44, k1_relat_1(A_43)) | ~v1_funct_1(k2_funct_1(A_43)) | ~v1_relat_1(k2_funct_1(A_43)) | ~v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.62/1.58  tff(c_44, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5' | k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.58  tff(c_85, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_44])).
% 3.62/1.58  tff(c_184, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_169, c_85])).
% 3.62/1.58  tff(c_194, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_184])).
% 3.62/1.58  tff(c_196, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_194])).
% 3.62/1.58  tff(c_199, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8, c_196])).
% 3.62/1.58  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_199])).
% 3.62/1.58  tff(c_204, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_194])).
% 3.62/1.58  tff(c_208, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6, c_204])).
% 3.62/1.58  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_208])).
% 3.62/1.58  tff(c_214, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 3.62/1.58  tff(c_265, plain, (![A_50, D_51]: (r2_hidden(k1_funct_1(A_50, D_51), k2_relat_1(A_50)) | ~r2_hidden(D_51, k1_relat_1(A_50)) | ~v1_funct_1(k2_funct_1(A_50)) | ~v1_relat_1(k2_funct_1(A_50)) | ~v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.62/1.58  tff(c_268, plain, (r2_hidden('#skF_5', k2_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_265])).
% 3.62/1.58  tff(c_272, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_268])).
% 3.62/1.58  tff(c_275, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8, c_272])).
% 3.62/1.58  tff(c_279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_275])).
% 3.62/1.58  tff(c_281, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_268])).
% 3.62/1.58  tff(c_305, plain, (![A_53, D_54]: (k1_funct_1(k2_funct_1(A_53), k1_funct_1(A_53, D_54))=D_54 | ~r2_hidden(D_54, k1_relat_1(A_53)) | ~v1_funct_1(k2_funct_1(A_53)) | ~v1_relat_1(k2_funct_1(A_53)) | ~v2_funct_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.62/1.58  tff(c_326, plain, (k1_funct_1(k2_funct_1(k2_funct_1('#skF_6')), '#skF_5')=k1_funct_1('#skF_6', '#skF_5') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_305])).
% 3.62/1.58  tff(c_336, plain, (k1_funct_1(k2_funct_1(k2_funct_1('#skF_6')), '#skF_5')=k1_funct_1('#skF_6', '#skF_5') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_326])).
% 3.62/1.58  tff(c_409, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_336])).
% 3.62/1.58  tff(c_412, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6, c_409])).
% 3.62/1.58  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_412])).
% 3.62/1.58  tff(c_418, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_336])).
% 3.62/1.58  tff(c_38, plain, (![A_10, D_26]: (r2_hidden(k1_funct_1(A_10, D_26), k2_relat_1(A_10)) | ~r2_hidden(D_26, k1_relat_1(A_10)) | ~v1_funct_1(k2_funct_1(A_10)) | ~v1_relat_1(k2_funct_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.62/1.58  tff(c_42, plain, (![A_27]: (k1_relat_1(k2_funct_1(A_27))=k2_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.62/1.58  tff(c_280, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | r2_hidden('#skF_5', k2_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_268])).
% 3.62/1.58  tff(c_408, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_280])).
% 3.62/1.58  tff(c_421, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_42, c_408])).
% 3.62/1.58  tff(c_423, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_421])).
% 3.62/1.58  tff(c_426, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_423])).
% 3.62/1.58  tff(c_430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_281, c_418, c_46, c_426])).
% 3.62/1.58  tff(c_431, plain, (~v1_funct_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_6'))) | ~v2_funct_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | r2_hidden('#skF_5', k2_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_280])).
% 3.62/1.58  tff(c_442, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_431])).
% 3.62/1.58  tff(c_445, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6, c_442])).
% 3.62/1.58  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_445])).
% 3.62/1.58  tff(c_451, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_431])).
% 3.62/1.58  tff(c_2, plain, (![A_1]: (k10_relat_1(A_1, k2_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.62/1.58  tff(c_219, plain, (![A_45, B_46]: (k10_relat_1(A_45, k1_relat_1(B_46))=k1_relat_1(k5_relat_1(A_45, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.62/1.58  tff(c_228, plain, (![A_45, A_27]: (k1_relat_1(k5_relat_1(A_45, k2_funct_1(A_27)))=k10_relat_1(A_45, k2_relat_1(A_27)) | ~v1_relat_1(k2_funct_1(A_27)) | ~v1_relat_1(A_45) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(superposition, [status(thm), theory('equality')], [c_42, c_219])).
% 3.62/1.58  tff(c_396, plain, (![C_59, B_60, A_61]: (k1_funct_1(k5_relat_1(C_59, B_60), A_61)=k1_funct_1(B_60, k1_funct_1(C_59, A_61)) | ~r2_hidden(A_61, k1_relat_1(k5_relat_1(C_59, B_60))) | ~v1_funct_1(C_59) | ~v1_relat_1(C_59) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.62/1.58  tff(c_808, plain, (![A_90, A_91, A_92]: (k1_funct_1(k5_relat_1(A_90, k2_funct_1(A_91)), A_92)=k1_funct_1(k2_funct_1(A_91), k1_funct_1(A_90, A_92)) | ~r2_hidden(A_92, k10_relat_1(A_90, k2_relat_1(A_91))) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90) | ~v1_funct_1(k2_funct_1(A_91)) | ~v1_relat_1(k2_funct_1(A_91)) | ~v1_relat_1(k2_funct_1(A_91)) | ~v1_relat_1(A_90) | ~v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_228, c_396])).
% 3.62/1.58  tff(c_818, plain, (![A_93, A_94]: (k1_funct_1(k5_relat_1(A_93, k2_funct_1(A_93)), A_94)=k1_funct_1(k2_funct_1(A_93), k1_funct_1(A_93, A_94)) | ~r2_hidden(A_94, k1_relat_1(A_93)) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93) | ~v1_funct_1(k2_funct_1(A_93)) | ~v1_relat_1(k2_funct_1(A_93)) | ~v1_relat_1(k2_funct_1(A_93)) | ~v1_relat_1(A_93) | ~v2_funct_1(A_93) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93) | ~v1_relat_1(A_93))), inference(superposition, [status(thm), theory('equality')], [c_2, c_808])).
% 3.62/1.58  tff(c_213, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 3.62/1.58  tff(c_849, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_818, c_213])).
% 3.62/1.58  tff(c_872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_50, c_48, c_52, c_281, c_281, c_451, c_52, c_50, c_46, c_214, c_849])).
% 3.62/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.58  
% 3.62/1.58  Inference rules
% 3.62/1.58  ----------------------
% 3.62/1.58  #Ref     : 0
% 3.62/1.58  #Sup     : 199
% 3.62/1.58  #Fact    : 0
% 3.62/1.58  #Define  : 0
% 3.62/1.58  #Split   : 10
% 3.62/1.58  #Chain   : 0
% 3.62/1.58  #Close   : 0
% 3.62/1.58  
% 3.62/1.58  Ordering : KBO
% 3.62/1.58  
% 3.62/1.58  Simplification rules
% 3.62/1.58  ----------------------
% 3.62/1.58  #Subsume      : 5
% 3.62/1.58  #Demod        : 75
% 3.62/1.58  #Tautology    : 58
% 3.62/1.58  #SimpNegUnit  : 0
% 3.62/1.58  #BackRed      : 0
% 3.62/1.58  
% 3.62/1.58  #Partial instantiations: 0
% 3.62/1.58  #Strategies tried      : 1
% 3.62/1.58  
% 3.62/1.58  Timing (in seconds)
% 3.62/1.58  ----------------------
% 3.62/1.58  Preprocessing        : 0.34
% 3.62/1.58  Parsing              : 0.17
% 3.62/1.58  CNF conversion       : 0.02
% 3.62/1.58  Main loop            : 0.47
% 3.62/1.58  Inferencing          : 0.18
% 3.62/1.58  Reduction            : 0.13
% 3.62/1.58  Demodulation         : 0.09
% 3.62/1.58  BG Simplification    : 0.04
% 3.62/1.58  Subsumption          : 0.10
% 3.62/1.58  Abstraction          : 0.03
% 3.62/1.58  MUC search           : 0.00
% 3.62/1.58  Cooper               : 0.00
% 3.62/1.58  Total                : 0.85
% 3.62/1.58  Index Insertion      : 0.00
% 3.62/1.58  Index Deletion       : 0.00
% 3.62/1.58  Index Matching       : 0.00
% 3.62/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
