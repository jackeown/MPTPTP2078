%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:39 EST 2020

% Result     : Theorem 9.47s
% Output     : CNFRefutation 9.64s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 361 expanded)
%              Number of leaves         :   27 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  252 (1031 expanded)
%              Number of equality atoms :   36 (  90 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k5_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_188,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_189,plain,(
    ! [B_58,C_59,A_60] :
      ( k7_relat_1(k5_relat_1(B_58,C_59),A_60) = k5_relat_1(k7_relat_1(B_58,A_60),C_59)
      | ~ v1_relat_1(C_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_58,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_70,plain,(
    ! [B_47,A_48] :
      ( k1_relat_1(k7_relat_1(B_47,A_48)) = A_48
      | ~ r1_tarski(A_48,k1_relat_1(B_47))
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_81,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_70])).

tff(c_92,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_95,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_92])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_95])).

tff(c_100,plain,(
    k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_205,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_100])).

tff(c_223,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_205])).

tff(c_12,plain,(
    ! [A_14,B_16] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_14,B_16)),k1_relat_1(A_14))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_228,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_12])).

tff(c_241,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4')))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_228])).

tff(c_243,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_246,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_243])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_246])).

tff(c_251,plain,(
    r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_16,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_21,A_20)),k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_59,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_43,B_21,A_20] :
      ( r1_tarski(A_43,k1_relat_1(B_21))
      | ~ r1_tarski(A_43,k1_relat_1(k7_relat_1(B_21,A_20)))
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_16,c_59])).

tff(c_257,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_251,c_65])).

tff(c_267,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_257])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_267])).

tff(c_271,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_20,plain,(
    ! [A_24,B_25] :
      ( v1_funct_1(k7_relat_1(A_24,B_25))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_18,plain,(
    ! [B_23,A_22] :
      ( k1_relat_1(k7_relat_1(B_23,A_22)) = A_22
      | ~ r1_tarski(A_22,k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_276,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_271,c_18])).

tff(c_283,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_276])).

tff(c_303,plain,(
    ! [A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_4'),A_20)),'#skF_4')
      | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_16])).

tff(c_406,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_409,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_406])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_409])).

tff(c_415,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_416,plain,(
    ! [B_65,C_66,A_67] :
      ( k7_relat_1(k5_relat_1(B_65,C_66),A_67) = k5_relat_1(k7_relat_1(B_65,A_67),C_66)
      | ~ v1_relat_1(C_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_432,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_100])).

tff(c_450,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_432])).

tff(c_10,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_885,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(k2_relat_1(B_89),k1_relat_1(A_90))
      | k1_relat_1(k5_relat_1(B_89,A_90)) != k1_relat_1(B_89)
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89)
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4489,plain,(
    ! [B_168,A_169,A_170] :
      ( r1_tarski(k9_relat_1(B_168,A_169),k1_relat_1(A_170))
      | k1_relat_1(k5_relat_1(k7_relat_1(B_168,A_169),A_170)) != k1_relat_1(k7_relat_1(B_168,A_169))
      | ~ v1_funct_1(k7_relat_1(B_168,A_169))
      | ~ v1_relat_1(k7_relat_1(B_168,A_169))
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170)
      | ~ v1_relat_1(B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_885])).

tff(c_270,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_313,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_4533,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) != k1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4489,c_313])).

tff(c_4609,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_26,c_415,c_283,c_450,c_4533])).

tff(c_4622,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_4609])).

tff(c_4626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_4622])).

tff(c_4628,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4776,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_4628,c_34])).

tff(c_101,plain,(
    v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_4627,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_4633,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4627,c_18])).

tff(c_4639,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4633])).

tff(c_4659,plain,(
    ! [A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_3'),A_20)),'#skF_3')
      | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4639,c_16])).

tff(c_5357,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4659])).

tff(c_5360,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_5357])).

tff(c_5364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5360])).

tff(c_5366,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4659])).

tff(c_36,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4670,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_36])).

tff(c_4671,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4670])).

tff(c_4685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4628,c_4671])).

tff(c_4686,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4670])).

tff(c_4809,plain,(
    ! [A_176,B_177] :
      ( k1_relat_1(k5_relat_1(A_176,B_177)) = k1_relat_1(A_176)
      | ~ r1_tarski(k2_relat_1(A_176),k1_relat_1(B_177))
      | ~ v1_relat_1(B_177)
      | ~ v1_relat_1(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8641,plain,(
    ! [B_272,A_273,B_274] :
      ( k1_relat_1(k5_relat_1(k7_relat_1(B_272,A_273),B_274)) = k1_relat_1(k7_relat_1(B_272,A_273))
      | ~ r1_tarski(k9_relat_1(B_272,A_273),k1_relat_1(B_274))
      | ~ v1_relat_1(B_274)
      | ~ v1_relat_1(k7_relat_1(B_272,A_273))
      | ~ v1_relat_1(B_272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_4809])).

tff(c_8712,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = k1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4686,c_8641])).

tff(c_8745,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5366,c_28,c_4639,c_8712])).

tff(c_4713,plain,(
    ! [B_171,C_172,A_173] :
      ( k7_relat_1(k5_relat_1(B_171,C_172),A_173) = k5_relat_1(k7_relat_1(B_171,A_173),C_172)
      | ~ v1_relat_1(C_172)
      | ~ v1_relat_1(B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4732,plain,(
    ! [B_171,A_173,C_172] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_171,A_173),C_172)),k1_relat_1(k5_relat_1(B_171,C_172)))
      | ~ v1_relat_1(k5_relat_1(B_171,C_172))
      | ~ v1_relat_1(C_172)
      | ~ v1_relat_1(B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4713,c_16])).

tff(c_8773,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8745,c_4732])).

tff(c_8829,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_101,c_8773])).

tff(c_8831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4776,c_8829])).

tff(c_8833,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8931,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_8833,c_40])).

tff(c_8832,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8865,plain,(
    ! [B_282,A_283] :
      ( k1_relat_1(k7_relat_1(B_282,A_283)) = A_283
      | ~ r1_tarski(A_283,k1_relat_1(B_282))
      | ~ v1_relat_1(B_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8874,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8832,c_8865])).

tff(c_8886,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8874])).

tff(c_8897,plain,(
    ! [A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_3'),A_20)),'#skF_3')
      | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8886,c_16])).

tff(c_8993,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8897])).

tff(c_8996,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_8993])).

tff(c_9000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8996])).

tff(c_9002,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8897])).

tff(c_42,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8834,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_8833,c_42])).

tff(c_12777,plain,(
    ! [A_431,B_432] :
      ( k1_relat_1(k5_relat_1(A_431,B_432)) = k1_relat_1(A_431)
      | ~ r1_tarski(k2_relat_1(A_431),k1_relat_1(B_432))
      | ~ v1_relat_1(B_432)
      | ~ v1_relat_1(A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16060,plain,(
    ! [B_515,A_516,B_517] :
      ( k1_relat_1(k5_relat_1(k7_relat_1(B_515,A_516),B_517)) = k1_relat_1(k7_relat_1(B_515,A_516))
      | ~ r1_tarski(k9_relat_1(B_515,A_516),k1_relat_1(B_517))
      | ~ v1_relat_1(B_517)
      | ~ v1_relat_1(k7_relat_1(B_515,A_516))
      | ~ v1_relat_1(B_515) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_12777])).

tff(c_16115,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = k1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8834,c_16060])).

tff(c_16125,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9002,c_28,c_8886,c_16115])).

tff(c_9003,plain,(
    ! [B_290,C_291,A_292] :
      ( k7_relat_1(k5_relat_1(B_290,C_291),A_292) = k5_relat_1(k7_relat_1(B_290,A_292),C_291)
      | ~ v1_relat_1(C_291)
      | ~ v1_relat_1(B_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_9012,plain,(
    ! [B_290,A_292,C_291] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_290,A_292),C_291)),k1_relat_1(k5_relat_1(B_290,C_291)))
      | ~ v1_relat_1(k5_relat_1(B_290,C_291))
      | ~ v1_relat_1(C_291)
      | ~ v1_relat_1(B_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9003,c_16])).

tff(c_16153,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16125,c_9012])).

tff(c_16217,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_16153])).

tff(c_16218,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_8931,c_16217])).

tff(c_16243,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_16218])).

tff(c_16247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_16243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:43:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.47/3.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.47/3.36  
% 9.47/3.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.47/3.36  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.47/3.36  
% 9.47/3.36  %Foreground sorts:
% 9.47/3.36  
% 9.47/3.36  
% 9.47/3.36  %Background operators:
% 9.47/3.36  
% 9.47/3.36  
% 9.47/3.36  %Foreground operators:
% 9.47/3.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.47/3.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.47/3.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.47/3.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.47/3.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.47/3.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.47/3.36  tff('#skF_2', type, '#skF_2': $i).
% 9.47/3.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.47/3.36  tff('#skF_3', type, '#skF_3': $i).
% 9.47/3.36  tff('#skF_1', type, '#skF_1': $i).
% 9.47/3.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.47/3.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.47/3.36  tff('#skF_4', type, '#skF_4': $i).
% 9.47/3.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.47/3.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.47/3.36  
% 9.64/3.38  tff(f_116, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 9.64/3.38  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 9.64/3.38  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.64/3.38  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 9.64/3.38  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 9.64/3.38  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 9.64/3.38  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 9.64/3.38  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.64/3.38  tff(f_86, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 9.64/3.38  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 9.64/3.38  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 9.64/3.38  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 9.64/3.38  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.64/3.38  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.64/3.38  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k5_relat_1(A_4, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.64/3.38  tff(c_38, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.64/3.38  tff(c_188, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_38])).
% 9.64/3.38  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.64/3.38  tff(c_189, plain, (![B_58, C_59, A_60]: (k7_relat_1(k5_relat_1(B_58, C_59), A_60)=k5_relat_1(k7_relat_1(B_58, A_60), C_59) | ~v1_relat_1(C_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.64/3.38  tff(c_44, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.64/3.38  tff(c_58, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_44])).
% 9.64/3.38  tff(c_70, plain, (![B_47, A_48]: (k1_relat_1(k7_relat_1(B_47, A_48))=A_48 | ~r1_tarski(A_48, k1_relat_1(B_47)) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.64/3.38  tff(c_81, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4' | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_70])).
% 9.64/3.38  tff(c_92, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_81])).
% 9.64/3.38  tff(c_95, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_92])).
% 9.64/3.38  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_95])).
% 9.64/3.38  tff(c_100, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_81])).
% 9.64/3.38  tff(c_205, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_189, c_100])).
% 9.64/3.38  tff(c_223, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_205])).
% 9.64/3.38  tff(c_12, plain, (![A_14, B_16]: (r1_tarski(k1_relat_1(k5_relat_1(A_14, B_16)), k1_relat_1(A_14)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.64/3.38  tff(c_228, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_12])).
% 9.64/3.38  tff(c_241, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_228])).
% 9.64/3.38  tff(c_243, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_241])).
% 9.64/3.38  tff(c_246, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_243])).
% 9.64/3.38  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_246])).
% 9.64/3.38  tff(c_251, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4')))), inference(splitRight, [status(thm)], [c_241])).
% 9.64/3.38  tff(c_16, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(k7_relat_1(B_21, A_20)), k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.64/3.38  tff(c_59, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.64/3.38  tff(c_65, plain, (![A_43, B_21, A_20]: (r1_tarski(A_43, k1_relat_1(B_21)) | ~r1_tarski(A_43, k1_relat_1(k7_relat_1(B_21, A_20))) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_16, c_59])).
% 9.64/3.38  tff(c_257, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_251, c_65])).
% 9.64/3.38  tff(c_267, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_257])).
% 9.64/3.38  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_267])).
% 9.64/3.38  tff(c_271, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_38])).
% 9.64/3.38  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.64/3.38  tff(c_20, plain, (![A_24, B_25]: (v1_funct_1(k7_relat_1(A_24, B_25)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.64/3.38  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.64/3.38  tff(c_18, plain, (![B_23, A_22]: (k1_relat_1(k7_relat_1(B_23, A_22))=A_22 | ~r1_tarski(A_22, k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.64/3.38  tff(c_276, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_271, c_18])).
% 9.64/3.38  tff(c_283, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_276])).
% 9.64/3.38  tff(c_303, plain, (![A_20]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), A_20)), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_283, c_16])).
% 9.64/3.38  tff(c_406, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_303])).
% 9.64/3.38  tff(c_409, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_406])).
% 9.64/3.38  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_409])).
% 9.64/3.38  tff(c_415, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitRight, [status(thm)], [c_303])).
% 9.64/3.38  tff(c_416, plain, (![B_65, C_66, A_67]: (k7_relat_1(k5_relat_1(B_65, C_66), A_67)=k5_relat_1(k7_relat_1(B_65, A_67), C_66) | ~v1_relat_1(C_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.64/3.38  tff(c_432, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_416, c_100])).
% 9.64/3.38  tff(c_450, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_432])).
% 9.64/3.38  tff(c_10, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.64/3.38  tff(c_885, plain, (![B_89, A_90]: (r1_tarski(k2_relat_1(B_89), k1_relat_1(A_90)) | k1_relat_1(k5_relat_1(B_89, A_90))!=k1_relat_1(B_89) | ~v1_funct_1(B_89) | ~v1_relat_1(B_89) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.64/3.38  tff(c_4489, plain, (![B_168, A_169, A_170]: (r1_tarski(k9_relat_1(B_168, A_169), k1_relat_1(A_170)) | k1_relat_1(k5_relat_1(k7_relat_1(B_168, A_169), A_170))!=k1_relat_1(k7_relat_1(B_168, A_169)) | ~v1_funct_1(k7_relat_1(B_168, A_169)) | ~v1_relat_1(k7_relat_1(B_168, A_169)) | ~v1_funct_1(A_170) | ~v1_relat_1(A_170) | ~v1_relat_1(B_168))), inference(superposition, [status(thm), theory('equality')], [c_10, c_885])).
% 9.64/3.38  tff(c_270, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_38])).
% 9.64/3.38  tff(c_313, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_270])).
% 9.64/3.38  tff(c_4533, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))!=k1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4489, c_313])).
% 9.64/3.38  tff(c_4609, plain, (~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_26, c_415, c_283, c_450, c_4533])).
% 9.64/3.38  tff(c_4622, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_4609])).
% 9.64/3.38  tff(c_4626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_4622])).
% 9.64/3.38  tff(c_4628, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_270])).
% 9.64/3.38  tff(c_34, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.64/3.38  tff(c_4776, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_4628, c_34])).
% 9.64/3.38  tff(c_101, plain, (v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_81])).
% 9.64/3.38  tff(c_4627, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_270])).
% 9.64/3.38  tff(c_4633, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4627, c_18])).
% 9.64/3.38  tff(c_4639, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4633])).
% 9.64/3.38  tff(c_4659, plain, (![A_20]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_3'), A_20)), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4639, c_16])).
% 9.64/3.38  tff(c_5357, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_4659])).
% 9.64/3.38  tff(c_5360, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_5357])).
% 9.64/3.38  tff(c_5364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_5360])).
% 9.64/3.38  tff(c_5366, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_4659])).
% 9.64/3.38  tff(c_36, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.64/3.38  tff(c_4670, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_36])).
% 9.64/3.38  tff(c_4671, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_4670])).
% 9.64/3.38  tff(c_4685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4628, c_4671])).
% 9.64/3.38  tff(c_4686, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_4670])).
% 9.64/3.38  tff(c_4809, plain, (![A_176, B_177]: (k1_relat_1(k5_relat_1(A_176, B_177))=k1_relat_1(A_176) | ~r1_tarski(k2_relat_1(A_176), k1_relat_1(B_177)) | ~v1_relat_1(B_177) | ~v1_relat_1(A_176))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.64/3.38  tff(c_8641, plain, (![B_272, A_273, B_274]: (k1_relat_1(k5_relat_1(k7_relat_1(B_272, A_273), B_274))=k1_relat_1(k7_relat_1(B_272, A_273)) | ~r1_tarski(k9_relat_1(B_272, A_273), k1_relat_1(B_274)) | ~v1_relat_1(B_274) | ~v1_relat_1(k7_relat_1(B_272, A_273)) | ~v1_relat_1(B_272))), inference(superposition, [status(thm), theory('equality')], [c_10, c_4809])).
% 9.64/3.38  tff(c_8712, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))=k1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4686, c_8641])).
% 9.64/3.38  tff(c_8745, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5366, c_28, c_4639, c_8712])).
% 9.64/3.38  tff(c_4713, plain, (![B_171, C_172, A_173]: (k7_relat_1(k5_relat_1(B_171, C_172), A_173)=k5_relat_1(k7_relat_1(B_171, A_173), C_172) | ~v1_relat_1(C_172) | ~v1_relat_1(B_171))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.64/3.38  tff(c_4732, plain, (![B_171, A_173, C_172]: (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_171, A_173), C_172)), k1_relat_1(k5_relat_1(B_171, C_172))) | ~v1_relat_1(k5_relat_1(B_171, C_172)) | ~v1_relat_1(C_172) | ~v1_relat_1(B_171))), inference(superposition, [status(thm), theory('equality')], [c_4713, c_16])).
% 9.64/3.38  tff(c_8773, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8745, c_4732])).
% 9.64/3.38  tff(c_8829, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_101, c_8773])).
% 9.64/3.38  tff(c_8831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4776, c_8829])).
% 9.64/3.38  tff(c_8833, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_44])).
% 9.64/3.38  tff(c_40, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.64/3.38  tff(c_8931, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_8833, c_40])).
% 9.64/3.38  tff(c_8832, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_44])).
% 9.64/3.38  tff(c_8865, plain, (![B_282, A_283]: (k1_relat_1(k7_relat_1(B_282, A_283))=A_283 | ~r1_tarski(A_283, k1_relat_1(B_282)) | ~v1_relat_1(B_282))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.64/3.38  tff(c_8874, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8832, c_8865])).
% 9.64/3.38  tff(c_8886, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8874])).
% 9.64/3.38  tff(c_8897, plain, (![A_20]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_3'), A_20)), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8886, c_16])).
% 9.64/3.38  tff(c_8993, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_8897])).
% 9.64/3.38  tff(c_8996, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_8993])).
% 9.64/3.38  tff(c_9000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_8996])).
% 9.64/3.38  tff(c_9002, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_8897])).
% 9.64/3.38  tff(c_42, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.64/3.38  tff(c_8834, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_8833, c_42])).
% 9.64/3.38  tff(c_12777, plain, (![A_431, B_432]: (k1_relat_1(k5_relat_1(A_431, B_432))=k1_relat_1(A_431) | ~r1_tarski(k2_relat_1(A_431), k1_relat_1(B_432)) | ~v1_relat_1(B_432) | ~v1_relat_1(A_431))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.64/3.38  tff(c_16060, plain, (![B_515, A_516, B_517]: (k1_relat_1(k5_relat_1(k7_relat_1(B_515, A_516), B_517))=k1_relat_1(k7_relat_1(B_515, A_516)) | ~r1_tarski(k9_relat_1(B_515, A_516), k1_relat_1(B_517)) | ~v1_relat_1(B_517) | ~v1_relat_1(k7_relat_1(B_515, A_516)) | ~v1_relat_1(B_515))), inference(superposition, [status(thm), theory('equality')], [c_10, c_12777])).
% 9.64/3.38  tff(c_16115, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))=k1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8834, c_16060])).
% 9.64/3.38  tff(c_16125, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_9002, c_28, c_8886, c_16115])).
% 9.64/3.38  tff(c_9003, plain, (![B_290, C_291, A_292]: (k7_relat_1(k5_relat_1(B_290, C_291), A_292)=k5_relat_1(k7_relat_1(B_290, A_292), C_291) | ~v1_relat_1(C_291) | ~v1_relat_1(B_290))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.64/3.38  tff(c_9012, plain, (![B_290, A_292, C_291]: (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_290, A_292), C_291)), k1_relat_1(k5_relat_1(B_290, C_291))) | ~v1_relat_1(k5_relat_1(B_290, C_291)) | ~v1_relat_1(C_291) | ~v1_relat_1(B_290))), inference(superposition, [status(thm), theory('equality')], [c_9003, c_16])).
% 9.64/3.38  tff(c_16153, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16125, c_9012])).
% 9.64/3.38  tff(c_16217, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_16153])).
% 9.64/3.38  tff(c_16218, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_8931, c_16217])).
% 9.64/3.38  tff(c_16243, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_16218])).
% 9.64/3.38  tff(c_16247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_16243])).
% 9.64/3.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.38  
% 9.64/3.38  Inference rules
% 9.64/3.38  ----------------------
% 9.64/3.38  #Ref     : 0
% 9.64/3.38  #Sup     : 3670
% 9.64/3.38  #Fact    : 0
% 9.64/3.38  #Define  : 0
% 9.64/3.38  #Split   : 26
% 9.64/3.38  #Chain   : 0
% 9.64/3.38  #Close   : 0
% 9.64/3.38  
% 9.64/3.38  Ordering : KBO
% 9.64/3.38  
% 9.64/3.38  Simplification rules
% 9.64/3.38  ----------------------
% 9.64/3.38  #Subsume      : 770
% 9.64/3.38  #Demod        : 2297
% 9.64/3.38  #Tautology    : 835
% 9.64/3.38  #SimpNegUnit  : 24
% 9.64/3.38  #BackRed      : 0
% 9.64/3.38  
% 9.64/3.38  #Partial instantiations: 0
% 9.64/3.38  #Strategies tried      : 1
% 9.64/3.38  
% 9.64/3.38  Timing (in seconds)
% 9.64/3.38  ----------------------
% 9.64/3.38  Preprocessing        : 0.34
% 9.64/3.38  Parsing              : 0.19
% 9.64/3.38  CNF conversion       : 0.02
% 9.64/3.38  Main loop            : 2.27
% 9.64/3.38  Inferencing          : 0.66
% 9.64/3.38  Reduction            : 0.74
% 9.64/3.38  Demodulation         : 0.53
% 9.64/3.38  BG Simplification    : 0.09
% 9.64/3.38  Subsumption          : 0.64
% 9.64/3.38  Abstraction          : 0.12
% 9.64/3.38  MUC search           : 0.00
% 9.64/3.38  Cooper               : 0.00
% 9.64/3.38  Total                : 2.66
% 9.64/3.38  Index Insertion      : 0.00
% 9.64/3.38  Index Deletion       : 0.00
% 9.64/3.38  Index Matching       : 0.00
% 9.64/3.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
