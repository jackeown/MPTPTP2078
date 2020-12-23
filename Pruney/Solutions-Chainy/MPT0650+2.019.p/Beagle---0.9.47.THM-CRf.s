%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:47 EST 2020

% Result     : Theorem 13.12s
% Output     : CNFRefutation 13.12s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 317 expanded)
%              Number of leaves         :   36 ( 128 expanded)
%              Depth                    :   15
%              Number of atoms          :  201 ( 895 expanded)
%              Number of equality atoms :   53 ( 258 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_134,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_74,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_56,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_62,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2,plain,(
    ! [A_1,C_16] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1,k2_relat_1(A_1),C_16),C_16),A_1)
      | ~ r2_hidden(C_16,k2_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_426,plain,(
    ! [C_74,A_75,B_76] :
      ( k1_funct_1(C_74,A_75) = B_76
      | ~ r2_hidden(k4_tarski(A_75,B_76),C_74)
      | ~ v1_funct_1(C_74)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_436,plain,(
    ! [A_1,C_16] :
      ( k1_funct_1(A_1,'#skF_4'(A_1,k2_relat_1(A_1),C_16)) = C_16
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1)
      | ~ r2_hidden(C_16,k2_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_2,c_426])).

tff(c_58,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_394,plain,(
    ! [A_71,C_72] :
      ( r2_hidden(k4_tarski('#skF_4'(A_71,k2_relat_1(A_71),C_72),C_72),A_71)
      | ~ r2_hidden(C_72,k2_relat_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_24,C_26,B_25] :
      ( r2_hidden(A_24,k1_relat_1(C_26))
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_410,plain,(
    ! [A_71,C_72] :
      ( r2_hidden('#skF_4'(A_71,k2_relat_1(A_71),C_72),k1_relat_1(A_71))
      | ~ v1_relat_1(A_71)
      | ~ r2_hidden(C_72,k2_relat_1(A_71)) ) ),
    inference(resolution,[status(thm)],[c_394,c_20])).

tff(c_1187,plain,(
    ! [A_115,C_116] :
      ( k1_funct_1(A_115,'#skF_4'(A_115,k2_relat_1(A_115),C_116)) = C_116
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115)
      | ~ r2_hidden(C_116,k2_relat_1(A_115)) ) ),
    inference(resolution,[status(thm)],[c_2,c_426])).

tff(c_46,plain,(
    ! [B_38,A_37] :
      ( k1_funct_1(k2_funct_1(B_38),k1_funct_1(B_38,A_37)) = A_37
      | ~ r2_hidden(A_37,k1_relat_1(B_38))
      | ~ v2_funct_1(B_38)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16716,plain,(
    ! [A_317,C_318] :
      ( k1_funct_1(k2_funct_1(A_317),C_318) = '#skF_4'(A_317,k2_relat_1(A_317),C_318)
      | ~ r2_hidden('#skF_4'(A_317,k2_relat_1(A_317),C_318),k1_relat_1(A_317))
      | ~ v2_funct_1(A_317)
      | ~ v1_funct_1(A_317)
      | ~ v1_relat_1(A_317)
      | ~ v1_funct_1(A_317)
      | ~ v1_relat_1(A_317)
      | ~ r2_hidden(C_318,k2_relat_1(A_317)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_46])).

tff(c_18316,plain,(
    ! [A_333,C_334] :
      ( k1_funct_1(k2_funct_1(A_333),C_334) = '#skF_4'(A_333,k2_relat_1(A_333),C_334)
      | ~ v2_funct_1(A_333)
      | ~ v1_funct_1(A_333)
      | ~ v1_relat_1(A_333)
      | ~ r2_hidden(C_334,k2_relat_1(A_333)) ) ),
    inference(resolution,[status(thm)],[c_410,c_16716])).

tff(c_18449,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_18316])).

tff(c_18523,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_18449])).

tff(c_54,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_84,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_18524,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18523,c_84])).

tff(c_18939,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_18524])).

tff(c_18943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_62,c_60,c_18939])).

tff(c_18945,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_18997,plain,(
    ! [A_346] :
      ( k4_relat_1(A_346) = k2_funct_1(A_346)
      | ~ v2_funct_1(A_346)
      | ~ v1_funct_1(A_346)
      | ~ v1_relat_1(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_19003,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_18997])).

tff(c_19009,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_19003])).

tff(c_14,plain,(
    ! [A_20] :
      ( v1_relat_1(k4_relat_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_19019,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_19009,c_14])).

tff(c_19027,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_19019])).

tff(c_34,plain,(
    ! [A_31] :
      ( v1_funct_1(k2_funct_1(A_31))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [A_27] :
      ( k1_relat_1(k4_relat_1(A_27)) = k2_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_19016,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_19009,c_24])).

tff(c_19025,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_19016])).

tff(c_22,plain,(
    ! [A_27] :
      ( k2_relat_1(k4_relat_1(A_27)) = k1_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_19013,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_19009,c_22])).

tff(c_19023,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_19013])).

tff(c_19427,plain,(
    ! [A_378,C_379] :
      ( r2_hidden(k4_tarski(A_378,k1_funct_1(C_379,A_378)),C_379)
      | ~ r2_hidden(A_378,k1_relat_1(C_379))
      | ~ v1_funct_1(C_379)
      | ~ v1_relat_1(C_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19446,plain,(
    ! [C_380,A_381] :
      ( r2_hidden(k1_funct_1(C_380,A_381),k2_relat_1(C_380))
      | ~ r2_hidden(A_381,k1_relat_1(C_380))
      | ~ v1_funct_1(C_380)
      | ~ v1_relat_1(C_380) ) ),
    inference(resolution,[status(thm)],[c_19427,c_4])).

tff(c_19449,plain,(
    ! [A_381] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_381),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_381,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19023,c_19446])).

tff(c_19460,plain,(
    ! [A_381] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_381),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_381,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19027,c_19025,c_19449])).

tff(c_19466,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_19460])).

tff(c_19482,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_19466])).

tff(c_19486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_19482])).

tff(c_19488,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_19460])).

tff(c_30,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k6_relat_1(k2_relat_1(A_29))) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_19032,plain,
    ( k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19023,c_30])).

tff(c_19036,plain,(
    k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19027,c_19032])).

tff(c_38,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [A_28] : k1_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_19048,plain,(
    ! [A_351,B_352] :
      ( k10_relat_1(A_351,k1_relat_1(B_352)) = k1_relat_1(k5_relat_1(A_351,B_352))
      | ~ v1_relat_1(B_352)
      | ~ v1_relat_1(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19063,plain,(
    ! [A_351,A_28] :
      ( k1_relat_1(k5_relat_1(A_351,k6_relat_1(A_28))) = k10_relat_1(A_351,A_28)
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(A_351) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_19048])).

tff(c_19090,plain,(
    ! [A_355,A_356] :
      ( k1_relat_1(k5_relat_1(A_355,k6_relat_1(A_356))) = k10_relat_1(A_355,A_356)
      | ~ v1_relat_1(A_355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_19063])).

tff(c_19102,plain,
    ( k10_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19036,c_19090])).

tff(c_19112,plain,(
    k10_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19027,c_19025,c_19102])).

tff(c_16,plain,(
    ! [A_21,B_23] :
      ( k10_relat_1(A_21,k1_relat_1(B_23)) = k1_relat_1(k5_relat_1(A_21,B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19139,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19112,c_16])).

tff(c_19146,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19027,c_62,c_19139])).

tff(c_20826,plain,(
    ! [C_433,B_434,A_435] :
      ( k1_funct_1(k5_relat_1(C_433,B_434),A_435) = k1_funct_1(B_434,k1_funct_1(C_433,A_435))
      | ~ r2_hidden(A_435,k1_relat_1(k5_relat_1(C_433,B_434)))
      | ~ v1_funct_1(C_433)
      | ~ v1_relat_1(C_433)
      | ~ v1_funct_1(B_434)
      | ~ v1_relat_1(B_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20934,plain,(
    ! [A_435] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),A_435) = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_435))
      | ~ r2_hidden(A_435,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19146,c_20826])).

tff(c_21057,plain,(
    ! [A_436] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),A_436) = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_436))
      | ~ r2_hidden(A_436,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_19027,c_19488,c_20934])).

tff(c_18944,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_21076,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21057,c_18944])).

tff(c_21090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_18945,c_21076])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:17:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.12/5.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.12/5.33  
% 13.12/5.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.12/5.33  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 13.12/5.33  
% 13.12/5.33  %Foreground sorts:
% 13.12/5.33  
% 13.12/5.33  
% 13.12/5.33  %Background operators:
% 13.12/5.33  
% 13.12/5.33  
% 13.12/5.33  %Foreground operators:
% 13.12/5.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.12/5.33  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.12/5.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.12/5.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.12/5.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.12/5.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.12/5.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.12/5.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.12/5.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.12/5.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.12/5.33  tff('#skF_5', type, '#skF_5': $i).
% 13.12/5.33  tff('#skF_6', type, '#skF_6': $i).
% 13.12/5.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.12/5.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.12/5.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.12/5.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.12/5.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.12/5.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.12/5.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.12/5.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.12/5.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.12/5.34  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 13.12/5.34  
% 13.12/5.35  tff(f_134, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 13.12/5.35  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 13.12/5.35  tff(f_121, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 13.12/5.35  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 13.12/5.35  tff(f_111, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 13.12/5.35  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 13.12/5.35  tff(f_37, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 13.12/5.35  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 13.12/5.35  tff(f_58, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 13.12/5.35  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 13.12/5.35  tff(f_86, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 13.12/5.35  tff(f_62, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 13.12/5.35  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 13.12/5.35  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 13.12/5.35  tff(c_56, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 13.12/5.35  tff(c_62, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 13.12/5.35  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 13.12/5.35  tff(c_2, plain, (![A_1, C_16]: (r2_hidden(k4_tarski('#skF_4'(A_1, k2_relat_1(A_1), C_16), C_16), A_1) | ~r2_hidden(C_16, k2_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.12/5.35  tff(c_426, plain, (![C_74, A_75, B_76]: (k1_funct_1(C_74, A_75)=B_76 | ~r2_hidden(k4_tarski(A_75, B_76), C_74) | ~v1_funct_1(C_74) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_121])).
% 13.12/5.35  tff(c_436, plain, (![A_1, C_16]: (k1_funct_1(A_1, '#skF_4'(A_1, k2_relat_1(A_1), C_16))=C_16 | ~v1_funct_1(A_1) | ~v1_relat_1(A_1) | ~r2_hidden(C_16, k2_relat_1(A_1)))), inference(resolution, [status(thm)], [c_2, c_426])).
% 13.12/5.35  tff(c_58, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 13.12/5.35  tff(c_394, plain, (![A_71, C_72]: (r2_hidden(k4_tarski('#skF_4'(A_71, k2_relat_1(A_71), C_72), C_72), A_71) | ~r2_hidden(C_72, k2_relat_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.12/5.35  tff(c_20, plain, (![A_24, C_26, B_25]: (r2_hidden(A_24, k1_relat_1(C_26)) | ~r2_hidden(k4_tarski(A_24, B_25), C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.12/5.35  tff(c_410, plain, (![A_71, C_72]: (r2_hidden('#skF_4'(A_71, k2_relat_1(A_71), C_72), k1_relat_1(A_71)) | ~v1_relat_1(A_71) | ~r2_hidden(C_72, k2_relat_1(A_71)))), inference(resolution, [status(thm)], [c_394, c_20])).
% 13.12/5.35  tff(c_1187, plain, (![A_115, C_116]: (k1_funct_1(A_115, '#skF_4'(A_115, k2_relat_1(A_115), C_116))=C_116 | ~v1_funct_1(A_115) | ~v1_relat_1(A_115) | ~r2_hidden(C_116, k2_relat_1(A_115)))), inference(resolution, [status(thm)], [c_2, c_426])).
% 13.12/5.35  tff(c_46, plain, (![B_38, A_37]: (k1_funct_1(k2_funct_1(B_38), k1_funct_1(B_38, A_37))=A_37 | ~r2_hidden(A_37, k1_relat_1(B_38)) | ~v2_funct_1(B_38) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.12/5.35  tff(c_16716, plain, (![A_317, C_318]: (k1_funct_1(k2_funct_1(A_317), C_318)='#skF_4'(A_317, k2_relat_1(A_317), C_318) | ~r2_hidden('#skF_4'(A_317, k2_relat_1(A_317), C_318), k1_relat_1(A_317)) | ~v2_funct_1(A_317) | ~v1_funct_1(A_317) | ~v1_relat_1(A_317) | ~v1_funct_1(A_317) | ~v1_relat_1(A_317) | ~r2_hidden(C_318, k2_relat_1(A_317)))), inference(superposition, [status(thm), theory('equality')], [c_1187, c_46])).
% 13.12/5.35  tff(c_18316, plain, (![A_333, C_334]: (k1_funct_1(k2_funct_1(A_333), C_334)='#skF_4'(A_333, k2_relat_1(A_333), C_334) | ~v2_funct_1(A_333) | ~v1_funct_1(A_333) | ~v1_relat_1(A_333) | ~r2_hidden(C_334, k2_relat_1(A_333)))), inference(resolution, [status(thm)], [c_410, c_16716])).
% 13.12/5.35  tff(c_18449, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_18316])).
% 13.12/5.35  tff(c_18523, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_18449])).
% 13.12/5.35  tff(c_54, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_134])).
% 13.12/5.35  tff(c_84, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_54])).
% 13.12/5.35  tff(c_18524, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_18523, c_84])).
% 13.12/5.35  tff(c_18939, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_436, c_18524])).
% 13.12/5.35  tff(c_18943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_62, c_60, c_18939])).
% 13.12/5.35  tff(c_18945, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_54])).
% 13.12/5.35  tff(c_18997, plain, (![A_346]: (k4_relat_1(A_346)=k2_funct_1(A_346) | ~v2_funct_1(A_346) | ~v1_funct_1(A_346) | ~v1_relat_1(A_346))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.12/5.35  tff(c_19003, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_18997])).
% 13.12/5.35  tff(c_19009, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_19003])).
% 13.12/5.35  tff(c_14, plain, (![A_20]: (v1_relat_1(k4_relat_1(A_20)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.12/5.35  tff(c_19019, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_19009, c_14])).
% 13.12/5.35  tff(c_19027, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_19019])).
% 13.12/5.35  tff(c_34, plain, (![A_31]: (v1_funct_1(k2_funct_1(A_31)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.12/5.35  tff(c_24, plain, (![A_27]: (k1_relat_1(k4_relat_1(A_27))=k2_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.12/5.35  tff(c_19016, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_19009, c_24])).
% 13.12/5.35  tff(c_19025, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_19016])).
% 13.12/5.35  tff(c_22, plain, (![A_27]: (k2_relat_1(k4_relat_1(A_27))=k1_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.12/5.35  tff(c_19013, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_19009, c_22])).
% 13.12/5.35  tff(c_19023, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_19013])).
% 13.12/5.35  tff(c_19427, plain, (![A_378, C_379]: (r2_hidden(k4_tarski(A_378, k1_funct_1(C_379, A_378)), C_379) | ~r2_hidden(A_378, k1_relat_1(C_379)) | ~v1_funct_1(C_379) | ~v1_relat_1(C_379))), inference(cnfTransformation, [status(thm)], [f_121])).
% 13.12/5.35  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k2_relat_1(A_1)) | ~r2_hidden(k4_tarski(D_19, C_16), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.12/5.35  tff(c_19446, plain, (![C_380, A_381]: (r2_hidden(k1_funct_1(C_380, A_381), k2_relat_1(C_380)) | ~r2_hidden(A_381, k1_relat_1(C_380)) | ~v1_funct_1(C_380) | ~v1_relat_1(C_380))), inference(resolution, [status(thm)], [c_19427, c_4])).
% 13.12/5.35  tff(c_19449, plain, (![A_381]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_381), k1_relat_1('#skF_6')) | ~r2_hidden(A_381, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_19023, c_19446])).
% 13.12/5.35  tff(c_19460, plain, (![A_381]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_381), k1_relat_1('#skF_6')) | ~r2_hidden(A_381, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_19027, c_19025, c_19449])).
% 13.12/5.35  tff(c_19466, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_19460])).
% 13.12/5.35  tff(c_19482, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_19466])).
% 13.12/5.35  tff(c_19486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_19482])).
% 13.12/5.35  tff(c_19488, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_19460])).
% 13.12/5.35  tff(c_30, plain, (![A_29]: (k5_relat_1(A_29, k6_relat_1(k2_relat_1(A_29)))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.12/5.35  tff(c_19032, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_19023, c_30])).
% 13.12/5.35  tff(c_19036, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19027, c_19032])).
% 13.12/5.35  tff(c_38, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.12/5.35  tff(c_26, plain, (![A_28]: (k1_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.12/5.35  tff(c_19048, plain, (![A_351, B_352]: (k10_relat_1(A_351, k1_relat_1(B_352))=k1_relat_1(k5_relat_1(A_351, B_352)) | ~v1_relat_1(B_352) | ~v1_relat_1(A_351))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.12/5.35  tff(c_19063, plain, (![A_351, A_28]: (k1_relat_1(k5_relat_1(A_351, k6_relat_1(A_28)))=k10_relat_1(A_351, A_28) | ~v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(A_351))), inference(superposition, [status(thm), theory('equality')], [c_26, c_19048])).
% 13.12/5.35  tff(c_19090, plain, (![A_355, A_356]: (k1_relat_1(k5_relat_1(A_355, k6_relat_1(A_356)))=k10_relat_1(A_355, A_356) | ~v1_relat_1(A_355))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_19063])).
% 13.12/5.35  tff(c_19102, plain, (k10_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_19036, c_19090])).
% 13.12/5.35  tff(c_19112, plain, (k10_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19027, c_19025, c_19102])).
% 13.12/5.35  tff(c_16, plain, (![A_21, B_23]: (k10_relat_1(A_21, k1_relat_1(B_23))=k1_relat_1(k5_relat_1(A_21, B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.12/5.35  tff(c_19139, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_19112, c_16])).
% 13.12/5.35  tff(c_19146, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19027, c_62, c_19139])).
% 13.12/5.35  tff(c_20826, plain, (![C_433, B_434, A_435]: (k1_funct_1(k5_relat_1(C_433, B_434), A_435)=k1_funct_1(B_434, k1_funct_1(C_433, A_435)) | ~r2_hidden(A_435, k1_relat_1(k5_relat_1(C_433, B_434))) | ~v1_funct_1(C_433) | ~v1_relat_1(C_433) | ~v1_funct_1(B_434) | ~v1_relat_1(B_434))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.12/5.35  tff(c_20934, plain, (![A_435]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), A_435)=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_435)) | ~r2_hidden(A_435, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_19146, c_20826])).
% 13.12/5.35  tff(c_21057, plain, (![A_436]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), A_436)=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_436)) | ~r2_hidden(A_436, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_19027, c_19488, c_20934])).
% 13.12/5.35  tff(c_18944, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_54])).
% 13.12/5.35  tff(c_21076, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_21057, c_18944])).
% 13.12/5.35  tff(c_21090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_18945, c_21076])).
% 13.12/5.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.12/5.35  
% 13.12/5.35  Inference rules
% 13.12/5.35  ----------------------
% 13.12/5.35  #Ref     : 0
% 13.12/5.35  #Sup     : 4866
% 13.12/5.35  #Fact    : 0
% 13.12/5.35  #Define  : 0
% 13.12/5.35  #Split   : 32
% 13.12/5.35  #Chain   : 0
% 13.12/5.35  #Close   : 0
% 13.12/5.35  
% 13.12/5.35  Ordering : KBO
% 13.12/5.35  
% 13.12/5.35  Simplification rules
% 13.12/5.35  ----------------------
% 13.12/5.35  #Subsume      : 572
% 13.12/5.35  #Demod        : 8754
% 13.12/5.35  #Tautology    : 1196
% 13.12/5.35  #SimpNegUnit  : 0
% 13.12/5.35  #BackRed      : 39
% 13.12/5.35  
% 13.12/5.35  #Partial instantiations: 0
% 13.12/5.35  #Strategies tried      : 1
% 13.12/5.35  
% 13.12/5.35  Timing (in seconds)
% 13.12/5.35  ----------------------
% 13.12/5.35  Preprocessing        : 0.34
% 13.12/5.35  Parsing              : 0.18
% 13.12/5.35  CNF conversion       : 0.02
% 13.12/5.35  Main loop            : 4.25
% 13.12/5.35  Inferencing          : 1.04
% 13.12/5.35  Reduction            : 1.95
% 13.12/5.36  Demodulation         : 1.59
% 13.12/5.36  BG Simplification    : 0.16
% 13.12/5.36  Subsumption          : 0.90
% 13.12/5.36  Abstraction          : 0.27
% 13.12/5.36  MUC search           : 0.00
% 13.12/5.36  Cooper               : 0.00
% 13.12/5.36  Total                : 4.62
% 13.12/5.36  Index Insertion      : 0.00
% 13.12/5.36  Index Deletion       : 0.00
% 13.12/5.36  Index Matching       : 0.00
% 13.12/5.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
