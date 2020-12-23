%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:03 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 266 expanded)
%              Number of leaves         :   23 ( 109 expanded)
%              Depth                    :   12
%              Number of atoms          :  185 (1052 expanded)
%              Number of equality atoms :   49 ( 335 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_26,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_24,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k2_funct_1(A_17)) = k6_relat_1(k1_relat_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_16] :
      ( k1_relat_1(k5_relat_1(A_16,k2_funct_1(A_16))) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70,plain,(
    ! [A_24] :
      ( k2_relat_1(k2_funct_1(A_24)) = k1_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_relat_1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_196,plain,(
    ! [A_33] :
      ( k5_relat_1(k2_funct_1(A_33),k6_relat_1(k1_relat_1(A_33))) = k2_funct_1(A_33)
      | ~ v1_relat_1(k2_funct_1(A_33))
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6])).

tff(c_214,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_196])).

tff(c_218,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_214])).

tff(c_219,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_222,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_219])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_222])).

tff(c_228,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_30,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_16,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_229,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(k2_relat_1(B_34),k1_relat_1(A_35))
      | k1_relat_1(k5_relat_1(B_34,A_35)) != k1_relat_1(B_34)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_244,plain,(
    ! [A_35] :
      ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(A_35))
      | k1_relat_1(k5_relat_1('#skF_1',A_35)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_229])).

tff(c_256,plain,(
    ! [A_36] :
      ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(A_36))
      | k1_relat_1(k5_relat_1('#skF_1',A_36)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_244])).

tff(c_269,plain,(
    ! [A_37] :
      ( r1_tarski(k1_relat_1('#skF_2'),k2_relat_1(A_37))
      | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1(A_37))) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(k2_funct_1(A_37))
      | ~ v1_relat_1(k2_funct_1(A_37))
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_256])).

tff(c_281,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_269])).

tff(c_286,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_228,c_281])).

tff(c_287,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_290,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_287])).

tff(c_294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_290])).

tff(c_295,plain,
    ( k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_297,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_300,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_297])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_300])).

tff(c_309,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_394,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_309])).

tff(c_406,plain,(
    k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_28,c_394])).

tff(c_227,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_22,plain,(
    ! [A_17] :
      ( k5_relat_1(k2_funct_1(A_17),A_17) = k6_relat_1(k2_relat_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_142,plain,(
    ! [A_30,B_31,C_32] :
      ( k5_relat_1(k5_relat_1(A_30,B_31),C_32) = k5_relat_1(A_30,k5_relat_1(B_31,C_32))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_806,plain,(
    ! [A_50,C_51] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_50)),C_51) = k5_relat_1(k2_funct_1(A_50),k5_relat_1(A_50,C_51))
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(A_50)
      | ~ v1_relat_1(k2_funct_1(A_50))
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_142])).

tff(c_925,plain,(
    ! [C_51] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_51) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_51))
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_806])).

tff(c_1104,plain,(
    ! [C_54] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_54) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_54))
      | ~ v1_relat_1(C_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_228,c_40,c_925])).

tff(c_4,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),B_9) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_259,plain,(
    ! [A_36] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_36)),'#skF_2') = '#skF_2'
      | ~ v1_relat_1('#skF_2')
      | k1_relat_1(k5_relat_1('#skF_1',A_36)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_256,c_4])).

tff(c_268,plain,(
    ! [A_36] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_36)),'#skF_2') = '#skF_2'
      | k1_relat_1(k5_relat_1('#skF_1',A_36)) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_259])).

tff(c_1133,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | k1_relat_1(k5_relat_1('#skF_1','#skF_2')) != k1_relat_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1104,c_268])).

tff(c_1194,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_34,c_406,c_227,c_1133])).

tff(c_1196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:30:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.53  
% 3.40/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.53  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.40/1.53  
% 3.40/1.53  %Foreground sorts:
% 3.40/1.53  
% 3.40/1.53  
% 3.40/1.53  %Background operators:
% 3.40/1.53  
% 3.40/1.53  
% 3.40/1.53  %Foreground operators:
% 3.40/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.40/1.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.40/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.40/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.53  
% 3.40/1.55  tff(f_114, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 3.40/1.55  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 3.40/1.55  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 3.40/1.55  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.40/1.55  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.40/1.55  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 3.40/1.55  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 3.40/1.55  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 3.40/1.55  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 3.40/1.55  tff(c_26, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.40/1.55  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.40/1.55  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.40/1.55  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.40/1.55  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.40/1.55  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.40/1.55  tff(c_28, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.40/1.55  tff(c_24, plain, (![A_17]: (k5_relat_1(A_17, k2_funct_1(A_17))=k6_relat_1(k1_relat_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.40/1.55  tff(c_20, plain, (![A_16]: (k1_relat_1(k5_relat_1(A_16, k2_funct_1(A_16)))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.40/1.55  tff(c_8, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.55  tff(c_10, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.55  tff(c_70, plain, (![A_24]: (k2_relat_1(k2_funct_1(A_24))=k1_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.40/1.55  tff(c_6, plain, (![A_10]: (k5_relat_1(A_10, k6_relat_1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.55  tff(c_196, plain, (![A_33]: (k5_relat_1(k2_funct_1(A_33), k6_relat_1(k1_relat_1(A_33)))=k2_funct_1(A_33) | ~v1_relat_1(k2_funct_1(A_33)) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_70, c_6])).
% 3.40/1.55  tff(c_214, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_196])).
% 3.40/1.55  tff(c_218, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_214])).
% 3.40/1.55  tff(c_219, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_218])).
% 3.40/1.55  tff(c_222, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_219])).
% 3.40/1.55  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_222])).
% 3.40/1.55  tff(c_228, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_218])).
% 3.40/1.55  tff(c_30, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.40/1.55  tff(c_16, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.40/1.55  tff(c_229, plain, (![B_34, A_35]: (r1_tarski(k2_relat_1(B_34), k1_relat_1(A_35)) | k1_relat_1(k5_relat_1(B_34, A_35))!=k1_relat_1(B_34) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.40/1.55  tff(c_244, plain, (![A_35]: (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(A_35)) | k1_relat_1(k5_relat_1('#skF_1', A_35))!=k1_relat_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_30, c_229])).
% 3.40/1.55  tff(c_256, plain, (![A_36]: (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(A_36)) | k1_relat_1(k5_relat_1('#skF_1', A_36))!=k1_relat_1('#skF_1') | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_244])).
% 3.40/1.55  tff(c_269, plain, (![A_37]: (r1_tarski(k1_relat_1('#skF_2'), k2_relat_1(A_37)) | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1(A_37)))!=k1_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1(A_37)) | ~v1_relat_1(k2_funct_1(A_37)) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_16, c_256])).
% 3.40/1.55  tff(c_281, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_269])).
% 3.40/1.55  tff(c_286, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_228, c_281])).
% 3.40/1.55  tff(c_287, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_286])).
% 3.40/1.55  tff(c_290, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_287])).
% 3.40/1.55  tff(c_294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_290])).
% 3.40/1.55  tff(c_295, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_286])).
% 3.40/1.55  tff(c_297, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_295])).
% 3.40/1.55  tff(c_300, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_297])).
% 3.40/1.55  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_300])).
% 3.40/1.55  tff(c_309, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_295])).
% 3.40/1.55  tff(c_394, plain, (k1_relat_1(k6_relat_1(k1_relat_1('#skF_1')))=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_309])).
% 3.40/1.55  tff(c_406, plain, (k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_28, c_394])).
% 3.40/1.55  tff(c_227, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_218])).
% 3.40/1.55  tff(c_22, plain, (![A_17]: (k5_relat_1(k2_funct_1(A_17), A_17)=k6_relat_1(k2_relat_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.40/1.55  tff(c_142, plain, (![A_30, B_31, C_32]: (k5_relat_1(k5_relat_1(A_30, B_31), C_32)=k5_relat_1(A_30, k5_relat_1(B_31, C_32)) | ~v1_relat_1(C_32) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.40/1.55  tff(c_806, plain, (![A_50, C_51]: (k5_relat_1(k6_relat_1(k2_relat_1(A_50)), C_51)=k5_relat_1(k2_funct_1(A_50), k5_relat_1(A_50, C_51)) | ~v1_relat_1(C_51) | ~v1_relat_1(A_50) | ~v1_relat_1(k2_funct_1(A_50)) | ~v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_22, c_142])).
% 3.40/1.55  tff(c_925, plain, (![C_51]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_51)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_51)) | ~v1_relat_1(C_51) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_806])).
% 3.40/1.55  tff(c_1104, plain, (![C_54]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_54)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_54)) | ~v1_relat_1(C_54))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_228, c_40, c_925])).
% 3.40/1.55  tff(c_4, plain, (![A_8, B_9]: (k5_relat_1(k6_relat_1(A_8), B_9)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.40/1.55  tff(c_259, plain, (![A_36]: (k5_relat_1(k6_relat_1(k1_relat_1(A_36)), '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2') | k1_relat_1(k5_relat_1('#skF_1', A_36))!=k1_relat_1('#skF_1') | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_256, c_4])).
% 3.40/1.55  tff(c_268, plain, (![A_36]: (k5_relat_1(k6_relat_1(k1_relat_1(A_36)), '#skF_2')='#skF_2' | k1_relat_1(k5_relat_1('#skF_1', A_36))!=k1_relat_1('#skF_1') | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_259])).
% 3.40/1.55  tff(c_1133, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))!=k1_relat_1('#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1104, c_268])).
% 3.40/1.55  tff(c_1194, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_34, c_406, c_227, c_1133])).
% 3.40/1.55  tff(c_1196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1194])).
% 3.40/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.55  
% 3.40/1.55  Inference rules
% 3.40/1.55  ----------------------
% 3.40/1.55  #Ref     : 0
% 3.40/1.55  #Sup     : 291
% 3.40/1.55  #Fact    : 0
% 3.40/1.55  #Define  : 0
% 3.40/1.55  #Split   : 9
% 3.40/1.55  #Chain   : 0
% 3.40/1.55  #Close   : 0
% 3.40/1.55  
% 3.40/1.55  Ordering : KBO
% 3.40/1.55  
% 3.40/1.55  Simplification rules
% 3.40/1.55  ----------------------
% 3.40/1.55  #Subsume      : 39
% 3.40/1.55  #Demod        : 157
% 3.40/1.55  #Tautology    : 73
% 3.40/1.55  #SimpNegUnit  : 1
% 3.40/1.55  #BackRed      : 0
% 3.40/1.55  
% 3.40/1.55  #Partial instantiations: 0
% 3.40/1.55  #Strategies tried      : 1
% 3.40/1.55  
% 3.40/1.55  Timing (in seconds)
% 3.40/1.55  ----------------------
% 3.40/1.55  Preprocessing        : 0.31
% 3.40/1.55  Parsing              : 0.16
% 3.40/1.55  CNF conversion       : 0.02
% 3.40/1.55  Main loop            : 0.48
% 3.40/1.55  Inferencing          : 0.19
% 3.40/1.55  Reduction            : 0.15
% 3.40/1.55  Demodulation         : 0.10
% 3.40/1.55  BG Simplification    : 0.03
% 3.40/1.55  Subsumption          : 0.09
% 3.40/1.55  Abstraction          : 0.03
% 3.40/1.55  MUC search           : 0.00
% 3.40/1.55  Cooper               : 0.00
% 3.40/1.55  Total                : 0.83
% 3.40/1.55  Index Insertion      : 0.00
% 3.40/1.55  Index Deletion       : 0.00
% 3.40/1.55  Index Matching       : 0.00
% 3.40/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
