%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:39 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 8.31s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 509 expanded)
%              Number of leaves         :   32 ( 182 expanded)
%              Depth                    :   16
%              Number of atoms          :  261 (1416 expanded)
%              Number of equality atoms :   38 ( 115 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_130,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_58,B_59)),k1_relat_1(A_58))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_52,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_58,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_104,plain,(
    ! [C_3] :
      ( r1_tarski('#skF_4',C_3)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2])).

tff(c_113,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_109,c_104])).

tff(c_125,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_113])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_28,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [A_30] : v1_funct_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    ! [A_26,B_27] :
      ( k5_relat_1(k6_relat_1(A_26),B_27) = k7_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_268,plain,(
    ! [A_66,B_67] :
      ( v1_funct_1(k5_relat_1(A_66,B_67))
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_271,plain,(
    ! [B_27,A_26] :
      ( v1_funct_1(k7_relat_1(B_27,A_26))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_268])).

tff(c_273,plain,(
    ! [B_27,A_26] :
      ( v1_funct_1(k7_relat_1(B_27,A_26))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_271])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [B_25,A_24] :
      ( k1_relat_1(k7_relat_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_133,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_125,c_20])).

tff(c_139,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_133])).

tff(c_18,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_23,A_22)),k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_153,plain,(
    ! [A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_4'),A_22)),'#skF_4')
      | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_18])).

tff(c_334,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_337,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_334])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_337])).

tff(c_343,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_349,plain,(
    ! [B_74,C_75,A_76] :
      ( k7_relat_1(k5_relat_1(B_74,C_75),A_76) = k5_relat_1(k7_relat_1(B_74,A_76),C_75)
      | ~ v1_relat_1(C_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    ! [B_55,A_56] :
      ( k1_relat_1(k7_relat_1(B_55,A_56)) = A_56
      | ~ r1_tarski(A_56,k1_relat_1(B_55))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_100,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_92])).

tff(c_258,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_261,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_261])).

tff(c_266,plain,(
    k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_361,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_266])).

tff(c_385,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_361])).

tff(c_12,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_786,plain,(
    ! [B_96,A_97] :
      ( r1_tarski(k2_relat_1(B_96),k1_relat_1(A_97))
      | k1_relat_1(k5_relat_1(B_96,A_97)) != k1_relat_1(B_96)
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3412,plain,(
    ! [B_176,A_177,A_178] :
      ( r1_tarski(k9_relat_1(B_176,A_177),k1_relat_1(A_178))
      | k1_relat_1(k5_relat_1(k7_relat_1(B_176,A_177),A_178)) != k1_relat_1(k7_relat_1(B_176,A_177))
      | ~ v1_funct_1(k7_relat_1(B_176,A_177))
      | ~ v1_relat_1(k7_relat_1(B_176,A_177))
      | ~ v1_funct_1(A_178)
      | ~ v1_relat_1(A_178)
      | ~ v1_relat_1(B_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_786])).

tff(c_46,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_225,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_46])).

tff(c_226,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_3418,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) != k1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3412,c_226])).

tff(c_3470,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_34,c_343,c_139,c_385,c_3418])).

tff(c_3481,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_273,c_3470])).

tff(c_3485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3481])).

tff(c_3487,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3593,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_3487,c_42])).

tff(c_3671,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_3674,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_3671])).

tff(c_3678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_3674])).

tff(c_3680,plain,(
    v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_3486,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_3490,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3486,c_20])).

tff(c_3496,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3490])).

tff(c_3513,plain,(
    ! [A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_3'),A_22)),'#skF_3')
      | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3496,c_18])).

tff(c_6715,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3513])).

tff(c_6718,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_6715])).

tff(c_6722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6718])).

tff(c_6724,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3513])).

tff(c_44,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3522,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_44])).

tff(c_3523,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3522])).

tff(c_3545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3487,c_3523])).

tff(c_3546,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3522])).

tff(c_3846,plain,(
    ! [A_193,B_194] :
      ( k1_relat_1(k5_relat_1(A_193,B_194)) = k1_relat_1(A_193)
      | ~ r1_tarski(k2_relat_1(A_193),k1_relat_1(B_194))
      | ~ v1_relat_1(B_194)
      | ~ v1_relat_1(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7202,plain,(
    ! [B_292,A_293,B_294] :
      ( k1_relat_1(k5_relat_1(k7_relat_1(B_292,A_293),B_294)) = k1_relat_1(k7_relat_1(B_292,A_293))
      | ~ r1_tarski(k9_relat_1(B_292,A_293),k1_relat_1(B_294))
      | ~ v1_relat_1(B_294)
      | ~ v1_relat_1(k7_relat_1(B_292,A_293))
      | ~ v1_relat_1(B_292) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3846])).

tff(c_7293,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = k1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3546,c_7202])).

tff(c_7339,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6724,c_36,c_3496,c_7293])).

tff(c_3633,plain,(
    ! [B_184,C_185,A_186] :
      ( k7_relat_1(k5_relat_1(B_184,C_185),A_186) = k5_relat_1(k7_relat_1(B_184,A_186),C_185)
      | ~ v1_relat_1(C_185)
      | ~ v1_relat_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3648,plain,(
    ! [B_184,A_186,C_185] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_184,A_186),C_185)),k1_relat_1(k5_relat_1(B_184,C_185)))
      | ~ v1_relat_1(k5_relat_1(B_184,C_185))
      | ~ v1_relat_1(C_185)
      | ~ v1_relat_1(B_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3633,c_18])).

tff(c_7362,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7339,c_3648])).

tff(c_7410,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_3680,c_7362])).

tff(c_7412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3593,c_7410])).

tff(c_7414,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7474,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_7414,c_48])).

tff(c_7413,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7490,plain,(
    ! [B_311,A_312] :
      ( k1_relat_1(k7_relat_1(B_311,A_312)) = A_312
      | ~ r1_tarski(A_312,k1_relat_1(B_311))
      | ~ v1_relat_1(B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7509,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_7413,c_7490])).

tff(c_7521,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7509])).

tff(c_7537,plain,(
    ! [A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_3'),A_22)),'#skF_3')
      | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7521,c_18])).

tff(c_7666,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7537])).

tff(c_7701,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_7666])).

tff(c_7705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7701])).

tff(c_7707,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7537])).

tff(c_50,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7419,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_7414,c_50])).

tff(c_8098,plain,(
    ! [A_346,B_347] :
      ( k1_relat_1(k5_relat_1(A_346,B_347)) = k1_relat_1(A_346)
      | ~ r1_tarski(k2_relat_1(A_346),k1_relat_1(B_347))
      | ~ v1_relat_1(B_347)
      | ~ v1_relat_1(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10312,plain,(
    ! [B_422,A_423,B_424] :
      ( k1_relat_1(k5_relat_1(k7_relat_1(B_422,A_423),B_424)) = k1_relat_1(k7_relat_1(B_422,A_423))
      | ~ r1_tarski(k9_relat_1(B_422,A_423),k1_relat_1(B_424))
      | ~ v1_relat_1(B_424)
      | ~ v1_relat_1(k7_relat_1(B_422,A_423))
      | ~ v1_relat_1(B_422) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8098])).

tff(c_10371,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = k1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_7419,c_10312])).

tff(c_10394,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7707,c_36,c_7521,c_10371])).

tff(c_7797,plain,(
    ! [B_331,C_332,A_333] :
      ( k7_relat_1(k5_relat_1(B_331,C_332),A_333) = k5_relat_1(k7_relat_1(B_331,A_333),C_332)
      | ~ v1_relat_1(C_332)
      | ~ v1_relat_1(B_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7815,plain,(
    ! [B_331,A_333,C_332] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_331,A_333),C_332)),k1_relat_1(k5_relat_1(B_331,C_332)))
      | ~ v1_relat_1(k5_relat_1(B_331,C_332))
      | ~ v1_relat_1(C_332)
      | ~ v1_relat_1(B_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7797,c_18])).

tff(c_10407,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10394,c_7815])).

tff(c_10456,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_10407])).

tff(c_10457,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_7474,c_10456])).

tff(c_10477,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_10457])).

tff(c_10481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_10477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:50:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.95/2.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.79  
% 7.95/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.79  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.95/2.79  
% 7.95/2.79  %Foreground sorts:
% 7.95/2.79  
% 7.95/2.79  
% 7.95/2.79  %Background operators:
% 7.95/2.79  
% 7.95/2.79  
% 7.95/2.79  %Foreground operators:
% 7.95/2.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.95/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.95/2.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.95/2.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.95/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.95/2.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.95/2.79  tff('#skF_2', type, '#skF_2': $i).
% 7.95/2.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.95/2.79  tff('#skF_3', type, '#skF_3': $i).
% 7.95/2.79  tff('#skF_1', type, '#skF_1': $i).
% 7.95/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.95/2.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.95/2.79  tff('#skF_4', type, '#skF_4': $i).
% 7.95/2.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.95/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.95/2.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.95/2.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.95/2.79  
% 8.31/2.82  tff(f_130, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 8.31/2.82  tff(f_39, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 8.31/2.82  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 8.31/2.82  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.31/2.82  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 8.31/2.82  tff(f_100, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 8.31/2.82  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 8.31/2.82  tff(f_96, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 8.31/2.82  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 8.31/2.82  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 8.31/2.82  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 8.31/2.82  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 8.31/2.82  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 8.31/2.82  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 8.31/2.82  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 8.31/2.82  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.31/2.82  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.31/2.82  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.31/2.82  tff(c_109, plain, (![A_58, B_59]: (r1_tarski(k1_relat_1(k5_relat_1(A_58, B_59)), k1_relat_1(A_58)) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.31/2.82  tff(c_52, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.31/2.82  tff(c_58, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_52])).
% 8.31/2.82  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.31/2.82  tff(c_62, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_4])).
% 8.31/2.82  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.31/2.82  tff(c_104, plain, (![C_3]: (r1_tarski('#skF_4', C_3) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_3))), inference(superposition, [status(thm), theory('equality')], [c_62, c_2])).
% 8.31/2.82  tff(c_113, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_109, c_104])).
% 8.31/2.82  tff(c_125, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_113])).
% 8.31/2.82  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.31/2.82  tff(c_28, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.31/2.82  tff(c_30, plain, (![A_30]: (v1_funct_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.31/2.82  tff(c_22, plain, (![A_26, B_27]: (k5_relat_1(k6_relat_1(A_26), B_27)=k7_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.31/2.82  tff(c_268, plain, (![A_66, B_67]: (v1_funct_1(k5_relat_1(A_66, B_67)) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.31/2.82  tff(c_271, plain, (![B_27, A_26]: (v1_funct_1(k7_relat_1(B_27, A_26)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_22, c_268])).
% 8.31/2.82  tff(c_273, plain, (![B_27, A_26]: (v1_funct_1(k7_relat_1(B_27, A_26)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_271])).
% 8.31/2.82  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.31/2.82  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.31/2.82  tff(c_20, plain, (![B_25, A_24]: (k1_relat_1(k7_relat_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.31/2.82  tff(c_133, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_125, c_20])).
% 8.31/2.82  tff(c_139, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_133])).
% 8.31/2.82  tff(c_18, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(k7_relat_1(B_23, A_22)), k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.31/2.82  tff(c_153, plain, (![A_22]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), A_22)), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_139, c_18])).
% 8.31/2.82  tff(c_334, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_153])).
% 8.31/2.82  tff(c_337, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_334])).
% 8.31/2.82  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_337])).
% 8.31/2.82  tff(c_343, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitRight, [status(thm)], [c_153])).
% 8.31/2.82  tff(c_349, plain, (![B_74, C_75, A_76]: (k7_relat_1(k5_relat_1(B_74, C_75), A_76)=k5_relat_1(k7_relat_1(B_74, A_76), C_75) | ~v1_relat_1(C_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.31/2.82  tff(c_92, plain, (![B_55, A_56]: (k1_relat_1(k7_relat_1(B_55, A_56))=A_56 | ~r1_tarski(A_56, k1_relat_1(B_55)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.31/2.82  tff(c_100, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4' | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_92])).
% 8.31/2.82  tff(c_258, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_100])).
% 8.31/2.82  tff(c_261, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_258])).
% 8.31/2.82  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_261])).
% 8.31/2.82  tff(c_266, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_100])).
% 8.31/2.82  tff(c_361, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_349, c_266])).
% 8.31/2.82  tff(c_385, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_361])).
% 8.31/2.82  tff(c_12, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.31/2.82  tff(c_786, plain, (![B_96, A_97]: (r1_tarski(k2_relat_1(B_96), k1_relat_1(A_97)) | k1_relat_1(k5_relat_1(B_96, A_97))!=k1_relat_1(B_96) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.31/2.82  tff(c_3412, plain, (![B_176, A_177, A_178]: (r1_tarski(k9_relat_1(B_176, A_177), k1_relat_1(A_178)) | k1_relat_1(k5_relat_1(k7_relat_1(B_176, A_177), A_178))!=k1_relat_1(k7_relat_1(B_176, A_177)) | ~v1_funct_1(k7_relat_1(B_176, A_177)) | ~v1_relat_1(k7_relat_1(B_176, A_177)) | ~v1_funct_1(A_178) | ~v1_relat_1(A_178) | ~v1_relat_1(B_176))), inference(superposition, [status(thm), theory('equality')], [c_12, c_786])).
% 8.31/2.82  tff(c_46, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.31/2.82  tff(c_225, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_46])).
% 8.31/2.82  tff(c_226, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_225])).
% 8.31/2.82  tff(c_3418, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))!=k1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3412, c_226])).
% 8.31/2.82  tff(c_3470, plain, (~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_34, c_343, c_139, c_385, c_3418])).
% 8.31/2.82  tff(c_3481, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_273, c_3470])).
% 8.31/2.82  tff(c_3485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3481])).
% 8.31/2.82  tff(c_3487, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_225])).
% 8.31/2.82  tff(c_42, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.31/2.82  tff(c_3593, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_3487, c_42])).
% 8.31/2.82  tff(c_3671, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_100])).
% 8.31/2.82  tff(c_3674, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_3671])).
% 8.31/2.82  tff(c_3678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_3674])).
% 8.31/2.82  tff(c_3680, plain, (v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_100])).
% 8.31/2.82  tff(c_3486, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_225])).
% 8.31/2.82  tff(c_3490, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3486, c_20])).
% 8.31/2.82  tff(c_3496, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3490])).
% 8.31/2.82  tff(c_3513, plain, (![A_22]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_3'), A_22)), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3496, c_18])).
% 8.31/2.82  tff(c_6715, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3513])).
% 8.31/2.82  tff(c_6718, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_6715])).
% 8.31/2.82  tff(c_6722, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_6718])).
% 8.31/2.82  tff(c_6724, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_3513])).
% 8.31/2.82  tff(c_44, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.31/2.82  tff(c_3522, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_44])).
% 8.31/2.82  tff(c_3523, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3522])).
% 8.31/2.82  tff(c_3545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3487, c_3523])).
% 8.31/2.82  tff(c_3546, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_3522])).
% 8.31/2.82  tff(c_3846, plain, (![A_193, B_194]: (k1_relat_1(k5_relat_1(A_193, B_194))=k1_relat_1(A_193) | ~r1_tarski(k2_relat_1(A_193), k1_relat_1(B_194)) | ~v1_relat_1(B_194) | ~v1_relat_1(A_193))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.31/2.82  tff(c_7202, plain, (![B_292, A_293, B_294]: (k1_relat_1(k5_relat_1(k7_relat_1(B_292, A_293), B_294))=k1_relat_1(k7_relat_1(B_292, A_293)) | ~r1_tarski(k9_relat_1(B_292, A_293), k1_relat_1(B_294)) | ~v1_relat_1(B_294) | ~v1_relat_1(k7_relat_1(B_292, A_293)) | ~v1_relat_1(B_292))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3846])).
% 8.31/2.82  tff(c_7293, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))=k1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3546, c_7202])).
% 8.31/2.82  tff(c_7339, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6724, c_36, c_3496, c_7293])).
% 8.31/2.82  tff(c_3633, plain, (![B_184, C_185, A_186]: (k7_relat_1(k5_relat_1(B_184, C_185), A_186)=k5_relat_1(k7_relat_1(B_184, A_186), C_185) | ~v1_relat_1(C_185) | ~v1_relat_1(B_184))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.31/2.82  tff(c_3648, plain, (![B_184, A_186, C_185]: (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_184, A_186), C_185)), k1_relat_1(k5_relat_1(B_184, C_185))) | ~v1_relat_1(k5_relat_1(B_184, C_185)) | ~v1_relat_1(C_185) | ~v1_relat_1(B_184))), inference(superposition, [status(thm), theory('equality')], [c_3633, c_18])).
% 8.31/2.82  tff(c_7362, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7339, c_3648])).
% 8.31/2.82  tff(c_7410, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_3680, c_7362])).
% 8.31/2.82  tff(c_7412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3593, c_7410])).
% 8.31/2.82  tff(c_7414, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_52])).
% 8.31/2.82  tff(c_48, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.31/2.82  tff(c_7474, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_7414, c_48])).
% 8.31/2.82  tff(c_7413, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_52])).
% 8.31/2.82  tff(c_7490, plain, (![B_311, A_312]: (k1_relat_1(k7_relat_1(B_311, A_312))=A_312 | ~r1_tarski(A_312, k1_relat_1(B_311)) | ~v1_relat_1(B_311))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.31/2.82  tff(c_7509, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_7413, c_7490])).
% 8.31/2.82  tff(c_7521, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7509])).
% 8.31/2.82  tff(c_7537, plain, (![A_22]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_3'), A_22)), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7521, c_18])).
% 8.31/2.82  tff(c_7666, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_7537])).
% 8.31/2.82  tff(c_7701, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_7666])).
% 8.31/2.82  tff(c_7705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_7701])).
% 8.31/2.82  tff(c_7707, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_7537])).
% 8.31/2.82  tff(c_50, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.31/2.82  tff(c_7419, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_7414, c_50])).
% 8.31/2.82  tff(c_8098, plain, (![A_346, B_347]: (k1_relat_1(k5_relat_1(A_346, B_347))=k1_relat_1(A_346) | ~r1_tarski(k2_relat_1(A_346), k1_relat_1(B_347)) | ~v1_relat_1(B_347) | ~v1_relat_1(A_346))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.31/2.82  tff(c_10312, plain, (![B_422, A_423, B_424]: (k1_relat_1(k5_relat_1(k7_relat_1(B_422, A_423), B_424))=k1_relat_1(k7_relat_1(B_422, A_423)) | ~r1_tarski(k9_relat_1(B_422, A_423), k1_relat_1(B_424)) | ~v1_relat_1(B_424) | ~v1_relat_1(k7_relat_1(B_422, A_423)) | ~v1_relat_1(B_422))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8098])).
% 8.31/2.82  tff(c_10371, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))=k1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_7419, c_10312])).
% 8.31/2.82  tff(c_10394, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7707, c_36, c_7521, c_10371])).
% 8.31/2.82  tff(c_7797, plain, (![B_331, C_332, A_333]: (k7_relat_1(k5_relat_1(B_331, C_332), A_333)=k5_relat_1(k7_relat_1(B_331, A_333), C_332) | ~v1_relat_1(C_332) | ~v1_relat_1(B_331))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.31/2.82  tff(c_7815, plain, (![B_331, A_333, C_332]: (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_331, A_333), C_332)), k1_relat_1(k5_relat_1(B_331, C_332))) | ~v1_relat_1(k5_relat_1(B_331, C_332)) | ~v1_relat_1(C_332) | ~v1_relat_1(B_331))), inference(superposition, [status(thm), theory('equality')], [c_7797, c_18])).
% 8.31/2.82  tff(c_10407, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10394, c_7815])).
% 8.31/2.82  tff(c_10456, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_10407])).
% 8.31/2.82  tff(c_10457, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_7474, c_10456])).
% 8.31/2.82  tff(c_10477, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_10457])).
% 8.31/2.82  tff(c_10481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_10477])).
% 8.31/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.31/2.82  
% 8.31/2.82  Inference rules
% 8.31/2.82  ----------------------
% 8.31/2.82  #Ref     : 0
% 8.31/2.82  #Sup     : 2345
% 8.31/2.82  #Fact    : 0
% 8.31/2.82  #Define  : 0
% 8.31/2.82  #Split   : 20
% 8.31/2.82  #Chain   : 0
% 8.31/2.82  #Close   : 0
% 8.31/2.82  
% 8.31/2.82  Ordering : KBO
% 8.31/2.82  
% 8.31/2.82  Simplification rules
% 8.31/2.82  ----------------------
% 8.31/2.82  #Subsume      : 328
% 8.31/2.82  #Demod        : 1468
% 8.31/2.82  #Tautology    : 765
% 8.31/2.82  #SimpNegUnit  : 11
% 8.31/2.82  #BackRed      : 0
% 8.31/2.82  
% 8.31/2.82  #Partial instantiations: 0
% 8.31/2.82  #Strategies tried      : 1
% 8.31/2.82  
% 8.31/2.82  Timing (in seconds)
% 8.31/2.82  ----------------------
% 8.31/2.82  Preprocessing        : 0.35
% 8.31/2.82  Parsing              : 0.19
% 8.31/2.82  CNF conversion       : 0.03
% 8.31/2.82  Main loop            : 1.64
% 8.31/2.82  Inferencing          : 0.54
% 8.31/2.82  Reduction            : 0.59
% 8.31/2.82  Demodulation         : 0.43
% 8.31/2.82  BG Simplification    : 0.07
% 8.31/2.82  Subsumption          : 0.33
% 8.31/2.82  Abstraction          : 0.08
% 8.31/2.82  MUC search           : 0.00
% 8.31/2.82  Cooper               : 0.00
% 8.31/2.82  Total                : 2.04
% 8.31/2.82  Index Insertion      : 0.00
% 8.31/2.82  Index Deletion       : 0.00
% 8.31/2.82  Index Matching       : 0.00
% 8.31/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
