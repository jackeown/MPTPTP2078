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
% DateTime   : Thu Dec  3 10:05:37 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 384 expanded)
%              Number of leaves         :   31 ( 134 expanded)
%              Depth                    :   14
%              Number of atoms          :  251 (1112 expanded)
%              Number of equality atoms :   34 ( 124 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_132,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_48,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_311,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_333,plain,(
    ! [B_66,C_67,A_68] :
      ( k7_relat_1(k5_relat_1(B_66,C_67),A_68) = k5_relat_1(k7_relat_1(B_66,A_68),C_67)
      | ~ v1_relat_1(C_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k5_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_79,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_114,plain,(
    ! [B_54,A_55] :
      ( k1_relat_1(k7_relat_1(B_54,A_55)) = A_55
      | ~ r1_tarski(A_55,k1_relat_1(B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_130,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_79,c_114])).

tff(c_193,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_196,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_193])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_196])).

tff(c_201,plain,(
    k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_349,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_201])).

tff(c_382,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_349])).

tff(c_18,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_16,B_18)),k1_relat_1(A_16))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_390,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_18])).

tff(c_412,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4')))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_390])).

tff(c_415,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_418,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_415])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_418])).

tff(c_423,plain,(
    r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_20,A_19)),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_80,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [B_20,A_19] :
      ( k1_relat_1(k7_relat_1(B_20,A_19)) = A_19
      | ~ r1_tarski(A_19,k1_relat_1(k7_relat_1(B_20,A_19)))
      | ~ v1_relat_1(B_20) ) ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_427,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_423,c_88])).

tff(c_435,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_427])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_22,A_21)),k1_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_466,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_22])).

tff(c_493,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_466])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_493])).

tff(c_497,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_24,plain,(
    ! [B_24,A_23] :
      ( k1_relat_1(k7_relat_1(B_24,A_23)) = A_23
      | ~ r1_tarski(A_23,k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_500,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_497,c_24])).

tff(c_505,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_500])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [B_54] :
      ( k1_relat_1(k7_relat_1(B_54,k1_relat_1(B_54))) = k1_relat_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_522,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_4')) = k1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_132])).

tff(c_542,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_522])).

tff(c_550,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_542])).

tff(c_553,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_550])).

tff(c_557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_553])).

tff(c_559,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_542])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( v1_funct_1(k7_relat_1(A_26,B_27))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [A_25] :
      ( k7_relat_1(A_25,k1_relat_1(A_25)) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_102,plain,(
    ! [B_52,A_53] :
      ( k2_relat_1(k7_relat_1(B_52,A_53)) = k9_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ! [A_25] :
      ( k9_relat_1(A_25,k1_relat_1(A_25)) = k2_relat_1(A_25)
      | ~ v1_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_102])).

tff(c_1156,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_tarski(A_85,k10_relat_1(C_86,B_87))
      | ~ r1_tarski(k9_relat_1(C_86,A_85),B_87)
      | ~ r1_tarski(A_85,k1_relat_1(C_86))
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1205,plain,(
    ! [A_90,C_91] :
      ( r1_tarski(A_90,k10_relat_1(C_91,k9_relat_1(C_91,A_90)))
      | ~ r1_tarski(A_90,k1_relat_1(C_91))
      | ~ v1_funct_1(C_91)
      | ~ v1_relat_1(C_91) ) ),
    inference(resolution,[status(thm)],[c_6,c_1156])).

tff(c_1217,plain,(
    ! [A_25] :
      ( r1_tarski(k1_relat_1(A_25),k10_relat_1(A_25,k2_relat_1(A_25)))
      | ~ r1_tarski(k1_relat_1(A_25),k1_relat_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25)
      | ~ v1_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_1205])).

tff(c_1224,plain,(
    ! [A_92] :
      ( r1_tarski(k1_relat_1(A_92),k10_relat_1(A_92,k2_relat_1(A_92)))
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1217])).

tff(c_1241,plain,
    ( r1_tarski('#skF_4',k10_relat_1(k7_relat_1('#skF_1','#skF_4'),k2_relat_1(k7_relat_1('#skF_1','#skF_4'))))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_1224])).

tff(c_1256,plain,
    ( r1_tarski('#skF_4',k10_relat_1(k7_relat_1('#skF_1','#skF_4'),k2_relat_1(k7_relat_1('#skF_1','#skF_4'))))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_1241])).

tff(c_1606,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1256])).

tff(c_1609,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1606])).

tff(c_1613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1609])).

tff(c_1615,plain,(
    v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1256])).

tff(c_672,plain,(
    ! [B_70,C_71,A_72] :
      ( k7_relat_1(k5_relat_1(B_70,C_71),A_72) = k5_relat_1(k7_relat_1(B_70,A_72),C_71)
      | ~ v1_relat_1(C_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_685,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_201])).

tff(c_718,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_685])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1452,plain,(
    ! [B_96,A_97] :
      ( r1_tarski(k2_relat_1(B_96),k1_relat_1(A_97))
      | k1_relat_1(k5_relat_1(B_96,A_97)) != k1_relat_1(B_96)
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_5923,plain,(
    ! [B_156,A_157,A_158] :
      ( r1_tarski(k9_relat_1(B_156,A_157),k1_relat_1(A_158))
      | k1_relat_1(k5_relat_1(k7_relat_1(B_156,A_157),A_158)) != k1_relat_1(k7_relat_1(B_156,A_157))
      | ~ v1_funct_1(k7_relat_1(B_156,A_157))
      | ~ v1_relat_1(k7_relat_1(B_156,A_157))
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158)
      | ~ v1_relat_1(B_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1452])).

tff(c_496,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_549,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_5937,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) != k1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5923,c_549])).

tff(c_6035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_559,c_1615,c_505,c_718,c_5937])).

tff(c_6037,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6273,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_6037,c_44])).

tff(c_16,plain,(
    ! [A_13,B_15] :
      ( k10_relat_1(A_13,k1_relat_1(B_15)) = k1_relat_1(k5_relat_1(A_13,B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6036,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_46,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6098,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_6037,c_46])).

tff(c_6325,plain,(
    ! [A_162,C_163,B_164] :
      ( r1_tarski(A_162,k10_relat_1(C_163,B_164))
      | ~ r1_tarski(k9_relat_1(C_163,A_162),B_164)
      | ~ r1_tarski(A_162,k1_relat_1(C_163))
      | ~ v1_funct_1(C_163)
      | ~ v1_relat_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6328,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6098,c_6325])).

tff(c_6341,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_6036,c_6328])).

tff(c_6352,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6341])).

tff(c_6355,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_6352])).

tff(c_6357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6273,c_6355])).

tff(c_6359,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6360,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6359,c_50])).

tff(c_6358,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6434,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_6359,c_52])).

tff(c_7440,plain,(
    ! [A_204,C_205,B_206] :
      ( r1_tarski(A_204,k10_relat_1(C_205,B_206))
      | ~ r1_tarski(k9_relat_1(C_205,A_204),B_206)
      | ~ r1_tarski(A_204,k1_relat_1(C_205))
      | ~ v1_funct_1(C_205)
      | ~ v1_relat_1(C_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7446,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6434,c_7440])).

tff(c_7458,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_6358,c_7446])).

tff(c_7466,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_7458])).

tff(c_7469,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_7466])).

tff(c_7471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6360,c_7469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:36:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.12/2.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.43  
% 7.12/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.44  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.12/2.44  
% 7.12/2.44  %Foreground sorts:
% 7.12/2.44  
% 7.12/2.44  
% 7.12/2.44  %Background operators:
% 7.12/2.44  
% 7.12/2.44  
% 7.12/2.44  %Foreground operators:
% 7.12/2.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.12/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.12/2.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.12/2.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.12/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.12/2.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.12/2.44  tff('#skF_2', type, '#skF_2': $i).
% 7.12/2.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.12/2.44  tff('#skF_3', type, '#skF_3': $i).
% 7.12/2.44  tff('#skF_1', type, '#skF_1': $i).
% 7.12/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.12/2.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.12/2.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.12/2.44  tff('#skF_4', type, '#skF_4': $i).
% 7.12/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.12/2.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.12/2.44  
% 7.12/2.45  tff(f_132, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 7.12/2.45  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.12/2.45  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 7.12/2.45  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 7.12/2.45  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 7.12/2.46  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 7.12/2.46  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 7.12/2.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.12/2.46  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 7.12/2.46  tff(f_92, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 7.12/2.46  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 7.12/2.46  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 7.12/2.46  tff(f_102, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 7.12/2.46  tff(f_115, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 7.12/2.46  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 7.12/2.46  tff(c_48, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.12/2.46  tff(c_311, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 7.12/2.46  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.12/2.46  tff(c_10, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.12/2.46  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.12/2.46  tff(c_333, plain, (![B_66, C_67, A_68]: (k7_relat_1(k5_relat_1(B_66, C_67), A_68)=k5_relat_1(k7_relat_1(B_66, A_68), C_67) | ~v1_relat_1(C_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.12/2.46  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k5_relat_1(A_3, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.12/2.46  tff(c_54, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.12/2.46  tff(c_79, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_54])).
% 7.12/2.46  tff(c_114, plain, (![B_54, A_55]: (k1_relat_1(k7_relat_1(B_54, A_55))=A_55 | ~r1_tarski(A_55, k1_relat_1(B_54)) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.12/2.46  tff(c_130, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4' | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_79, c_114])).
% 7.12/2.46  tff(c_193, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_130])).
% 7.12/2.46  tff(c_196, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_193])).
% 7.12/2.46  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_196])).
% 7.12/2.46  tff(c_201, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_130])).
% 7.12/2.46  tff(c_349, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_333, c_201])).
% 7.12/2.46  tff(c_382, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_349])).
% 7.12/2.46  tff(c_18, plain, (![A_16, B_18]: (r1_tarski(k1_relat_1(k5_relat_1(A_16, B_18)), k1_relat_1(A_16)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.12/2.46  tff(c_390, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_382, c_18])).
% 7.12/2.46  tff(c_412, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_390])).
% 7.12/2.46  tff(c_415, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_412])).
% 7.12/2.46  tff(c_418, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_415])).
% 7.12/2.46  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_418])).
% 7.12/2.46  tff(c_423, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4')))), inference(splitRight, [status(thm)], [c_412])).
% 7.12/2.46  tff(c_20, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(k7_relat_1(B_20, A_19)), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.12/2.46  tff(c_80, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.12/2.46  tff(c_88, plain, (![B_20, A_19]: (k1_relat_1(k7_relat_1(B_20, A_19))=A_19 | ~r1_tarski(A_19, k1_relat_1(k7_relat_1(B_20, A_19))) | ~v1_relat_1(B_20))), inference(resolution, [status(thm)], [c_20, c_80])).
% 7.12/2.46  tff(c_427, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_423, c_88])).
% 7.12/2.46  tff(c_435, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_427])).
% 7.12/2.46  tff(c_22, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(k7_relat_1(B_22, A_21)), k1_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.12/2.46  tff(c_466, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_435, c_22])).
% 7.12/2.46  tff(c_493, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_466])).
% 7.12/2.46  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_311, c_493])).
% 7.12/2.46  tff(c_497, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 7.12/2.46  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.12/2.46  tff(c_24, plain, (![B_24, A_23]: (k1_relat_1(k7_relat_1(B_24, A_23))=A_23 | ~r1_tarski(A_23, k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.12/2.46  tff(c_500, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_497, c_24])).
% 7.12/2.46  tff(c_505, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_500])).
% 7.12/2.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.12/2.46  tff(c_132, plain, (![B_54]: (k1_relat_1(k7_relat_1(B_54, k1_relat_1(B_54)))=k1_relat_1(B_54) | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_6, c_114])).
% 7.12/2.46  tff(c_522, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_4'))=k1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_505, c_132])).
% 7.12/2.46  tff(c_542, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_4'))='#skF_4' | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_522])).
% 7.12/2.46  tff(c_550, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_542])).
% 7.12/2.46  tff(c_553, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_550])).
% 7.12/2.46  tff(c_557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_553])).
% 7.12/2.46  tff(c_559, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitRight, [status(thm)], [c_542])).
% 7.12/2.46  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.12/2.46  tff(c_28, plain, (![A_26, B_27]: (v1_funct_1(k7_relat_1(A_26, B_27)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.12/2.46  tff(c_26, plain, (![A_25]: (k7_relat_1(A_25, k1_relat_1(A_25))=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.12/2.46  tff(c_102, plain, (![B_52, A_53]: (k2_relat_1(k7_relat_1(B_52, A_53))=k9_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.12/2.46  tff(c_111, plain, (![A_25]: (k9_relat_1(A_25, k1_relat_1(A_25))=k2_relat_1(A_25) | ~v1_relat_1(A_25) | ~v1_relat_1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_26, c_102])).
% 7.12/2.46  tff(c_1156, plain, (![A_85, C_86, B_87]: (r1_tarski(A_85, k10_relat_1(C_86, B_87)) | ~r1_tarski(k9_relat_1(C_86, A_85), B_87) | ~r1_tarski(A_85, k1_relat_1(C_86)) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.12/2.46  tff(c_1205, plain, (![A_90, C_91]: (r1_tarski(A_90, k10_relat_1(C_91, k9_relat_1(C_91, A_90))) | ~r1_tarski(A_90, k1_relat_1(C_91)) | ~v1_funct_1(C_91) | ~v1_relat_1(C_91))), inference(resolution, [status(thm)], [c_6, c_1156])).
% 7.12/2.46  tff(c_1217, plain, (![A_25]: (r1_tarski(k1_relat_1(A_25), k10_relat_1(A_25, k2_relat_1(A_25))) | ~r1_tarski(k1_relat_1(A_25), k1_relat_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25) | ~v1_relat_1(A_25) | ~v1_relat_1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_111, c_1205])).
% 7.12/2.46  tff(c_1224, plain, (![A_92]: (r1_tarski(k1_relat_1(A_92), k10_relat_1(A_92, k2_relat_1(A_92))) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1217])).
% 7.12/2.46  tff(c_1241, plain, (r1_tarski('#skF_4', k10_relat_1(k7_relat_1('#skF_1', '#skF_4'), k2_relat_1(k7_relat_1('#skF_1', '#skF_4')))) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_505, c_1224])).
% 7.12/2.46  tff(c_1256, plain, (r1_tarski('#skF_4', k10_relat_1(k7_relat_1('#skF_1', '#skF_4'), k2_relat_1(k7_relat_1('#skF_1', '#skF_4')))) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_559, c_1241])).
% 7.12/2.46  tff(c_1606, plain, (~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1256])).
% 7.12/2.46  tff(c_1609, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1606])).
% 7.12/2.46  tff(c_1613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1609])).
% 7.12/2.46  tff(c_1615, plain, (v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitRight, [status(thm)], [c_1256])).
% 7.12/2.46  tff(c_672, plain, (![B_70, C_71, A_72]: (k7_relat_1(k5_relat_1(B_70, C_71), A_72)=k5_relat_1(k7_relat_1(B_70, A_72), C_71) | ~v1_relat_1(C_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.12/2.46  tff(c_685, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_672, c_201])).
% 7.12/2.46  tff(c_718, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_685])).
% 7.12/2.46  tff(c_14, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.12/2.46  tff(c_1452, plain, (![B_96, A_97]: (r1_tarski(k2_relat_1(B_96), k1_relat_1(A_97)) | k1_relat_1(k5_relat_1(B_96, A_97))!=k1_relat_1(B_96) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.12/2.46  tff(c_5923, plain, (![B_156, A_157, A_158]: (r1_tarski(k9_relat_1(B_156, A_157), k1_relat_1(A_158)) | k1_relat_1(k5_relat_1(k7_relat_1(B_156, A_157), A_158))!=k1_relat_1(k7_relat_1(B_156, A_157)) | ~v1_funct_1(k7_relat_1(B_156, A_157)) | ~v1_relat_1(k7_relat_1(B_156, A_157)) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158) | ~v1_relat_1(B_156))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1452])).
% 7.12/2.46  tff(c_496, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 7.12/2.46  tff(c_549, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_496])).
% 7.12/2.46  tff(c_5937, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))!=k1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_5923, c_549])).
% 7.12/2.46  tff(c_6035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_559, c_1615, c_505, c_718, c_5937])).
% 7.12/2.46  tff(c_6037, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_496])).
% 7.12/2.46  tff(c_44, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.12/2.46  tff(c_6273, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_497, c_6037, c_44])).
% 7.12/2.46  tff(c_16, plain, (![A_13, B_15]: (k10_relat_1(A_13, k1_relat_1(B_15))=k1_relat_1(k5_relat_1(A_13, B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.12/2.46  tff(c_6036, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_496])).
% 7.12/2.46  tff(c_46, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.12/2.46  tff(c_6098, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_497, c_6037, c_46])).
% 7.12/2.46  tff(c_6325, plain, (![A_162, C_163, B_164]: (r1_tarski(A_162, k10_relat_1(C_163, B_164)) | ~r1_tarski(k9_relat_1(C_163, A_162), B_164) | ~r1_tarski(A_162, k1_relat_1(C_163)) | ~v1_funct_1(C_163) | ~v1_relat_1(C_163))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.12/2.46  tff(c_6328, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6098, c_6325])).
% 7.12/2.46  tff(c_6341, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_6036, c_6328])).
% 7.12/2.46  tff(c_6352, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_6341])).
% 7.12/2.46  tff(c_6355, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_6352])).
% 7.12/2.46  tff(c_6357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6273, c_6355])).
% 7.12/2.46  tff(c_6359, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 7.12/2.46  tff(c_50, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.12/2.46  tff(c_6360, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_6359, c_50])).
% 7.12/2.46  tff(c_6358, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_54])).
% 7.12/2.46  tff(c_52, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.12/2.46  tff(c_6434, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_6359, c_52])).
% 7.12/2.46  tff(c_7440, plain, (![A_204, C_205, B_206]: (r1_tarski(A_204, k10_relat_1(C_205, B_206)) | ~r1_tarski(k9_relat_1(C_205, A_204), B_206) | ~r1_tarski(A_204, k1_relat_1(C_205)) | ~v1_funct_1(C_205) | ~v1_relat_1(C_205))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.12/2.46  tff(c_7446, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6434, c_7440])).
% 7.12/2.46  tff(c_7458, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_6358, c_7446])).
% 7.12/2.46  tff(c_7466, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_7458])).
% 7.12/2.46  tff(c_7469, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_7466])).
% 7.12/2.46  tff(c_7471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6360, c_7469])).
% 7.12/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.46  
% 7.12/2.46  Inference rules
% 7.12/2.46  ----------------------
% 7.12/2.46  #Ref     : 0
% 7.12/2.46  #Sup     : 1832
% 7.12/2.46  #Fact    : 0
% 7.12/2.46  #Define  : 0
% 7.12/2.46  #Split   : 22
% 7.12/2.46  #Chain   : 0
% 7.12/2.46  #Close   : 0
% 7.12/2.46  
% 7.12/2.46  Ordering : KBO
% 7.12/2.46  
% 7.12/2.46  Simplification rules
% 7.12/2.46  ----------------------
% 7.12/2.46  #Subsume      : 188
% 7.12/2.46  #Demod        : 1684
% 7.12/2.46  #Tautology    : 514
% 7.12/2.46  #SimpNegUnit  : 18
% 7.12/2.46  #BackRed      : 13
% 7.12/2.46  
% 7.12/2.46  #Partial instantiations: 0
% 7.12/2.46  #Strategies tried      : 1
% 7.12/2.46  
% 7.12/2.46  Timing (in seconds)
% 7.12/2.46  ----------------------
% 7.12/2.46  Preprocessing        : 0.32
% 7.12/2.46  Parsing              : 0.17
% 7.12/2.46  CNF conversion       : 0.02
% 7.12/2.46  Main loop            : 1.35
% 7.12/2.46  Inferencing          : 0.40
% 7.12/2.46  Reduction            : 0.49
% 7.12/2.46  Demodulation         : 0.35
% 7.12/2.46  BG Simplification    : 0.06
% 7.12/2.46  Subsumption          : 0.31
% 7.12/2.46  Abstraction          : 0.07
% 7.12/2.46  MUC search           : 0.00
% 7.12/2.46  Cooper               : 0.00
% 7.12/2.46  Total                : 1.72
% 7.12/2.46  Index Insertion      : 0.00
% 7.12/2.46  Index Deletion       : 0.00
% 7.12/2.46  Index Matching       : 0.00
% 7.12/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
