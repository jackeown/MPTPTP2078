%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:11 EST 2020

% Result     : Theorem 14.10s
% Output     : CNFRefutation 14.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 217 expanded)
%              Number of leaves         :   24 (  83 expanded)
%              Depth                    :   15
%              Number of atoms          :  142 ( 474 expanded)
%              Number of equality atoms :   47 ( 150 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(k2_relat_1(B),k1_relat_1(k7_relat_1(C,A)))
             => k5_relat_1(B,k7_relat_1(C,A)) = k5_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_20,plain,(
    k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')) != k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [A_28,B_29] :
      ( k5_relat_1(k6_relat_1(A_28),B_29) = k7_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [B_29,A_28] :
      ( v1_relat_1(k7_relat_1(B_29,A_28))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_2])).

tff(c_65,plain,(
    ! [B_29,A_28] :
      ( v1_relat_1(k7_relat_1(B_29,A_28))
      | ~ v1_relat_1(B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_22,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_109,plain,(
    ! [B_37,A_38] :
      ( k1_relat_1(k7_relat_1(B_37,A_38)) = A_38
      | ~ r1_tarski(A_38,k1_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_113,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_1'),k2_relat_1('#skF_2'))) = k2_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_109])).

tff(c_223,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_226,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_223])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_226])).

tff(c_232,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [C_6,A_4,B_5] :
      ( k7_relat_1(k7_relat_1(C_6,A_4),B_5) = k7_relat_1(C_6,k3_xboole_0(A_4,B_5))
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_231,plain,(
    k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_1'),k2_relat_1('#skF_2'))) = k2_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_246,plain,
    ( k1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1',k2_relat_1('#skF_2')))) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_231])).

tff(c_250,plain,(
    k1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1',k2_relat_1('#skF_2')))) = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_246])).

tff(c_14,plain,(
    ! [B_18,A_17] :
      ( k3_xboole_0(k1_relat_1(B_18),A_17) = k1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_94,plain,(
    ! [B_35,A_36] :
      ( k7_relat_1(B_35,k3_xboole_0(k1_relat_1(B_35),A_36)) = k7_relat_1(B_35,A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_264,plain,(
    ! [B_49,A_50] :
      ( k7_relat_1(B_49,k1_relat_1(k7_relat_1(B_49,A_50))) = k7_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_94])).

tff(c_293,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))) = k7_relat_1('#skF_3',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_264])).

tff(c_320,plain,(
    k7_relat_1('#skF_3',k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))) = k7_relat_1('#skF_3',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_293])).

tff(c_12,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k6_relat_1(k2_relat_1(A_16))) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_148,plain,(
    ! [A_42,B_43,C_44] :
      ( k5_relat_1(k5_relat_1(A_42,B_43),C_44) = k5_relat_1(A_42,k5_relat_1(B_43,C_44))
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_170,plain,(
    ! [A_21,B_22,C_44] :
      ( k5_relat_1(k6_relat_1(A_21),k5_relat_1(B_22,C_44)) = k5_relat_1(k7_relat_1(B_22,A_21),C_44)
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_148])).

tff(c_537,plain,(
    ! [A_56,B_57,C_58] :
      ( k5_relat_1(k6_relat_1(A_56),k5_relat_1(B_57,C_58)) = k5_relat_1(k7_relat_1(B_57,A_56),C_58)
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_170])).

tff(c_8276,plain,(
    ! [B_306,C_307,A_308] :
      ( k7_relat_1(k5_relat_1(B_306,C_307),A_308) = k5_relat_1(k7_relat_1(B_306,A_308),C_307)
      | ~ v1_relat_1(C_307)
      | ~ v1_relat_1(B_306)
      | ~ v1_relat_1(k5_relat_1(B_306,C_307)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_537])).

tff(c_8415,plain,(
    ! [A_309,B_310,A_311] :
      ( k7_relat_1(k5_relat_1(A_309,B_310),A_311) = k5_relat_1(k7_relat_1(A_309,A_311),B_310)
      | ~ v1_relat_1(B_310)
      | ~ v1_relat_1(A_309) ) ),
    inference(resolution,[status(thm)],[c_2,c_8276])).

tff(c_8539,plain,(
    ! [A_16,A_311] :
      ( k5_relat_1(k7_relat_1(A_16,A_311),k6_relat_1(k2_relat_1(A_16))) = k7_relat_1(A_16,A_311)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_16)))
      | ~ v1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8415])).

tff(c_8556,plain,(
    ! [A_312,A_313] :
      ( k5_relat_1(k7_relat_1(A_312,A_313),k6_relat_1(k2_relat_1(A_312))) = k7_relat_1(A_312,A_313)
      | ~ v1_relat_1(A_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8539])).

tff(c_8686,plain,
    ( k5_relat_1(k7_relat_1('#skF_3',k2_relat_1('#skF_2')),k6_relat_1(k2_relat_1('#skF_3'))) = k7_relat_1('#skF_3',k3_xboole_0('#skF_1',k2_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_8556])).

tff(c_8768,plain,(
    k5_relat_1(k7_relat_1('#skF_3',k2_relat_1('#skF_2')),k6_relat_1(k2_relat_1('#skF_3'))) = k7_relat_1('#skF_3',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_320,c_8686])).

tff(c_586,plain,(
    ! [A_16,A_56] :
      ( k5_relat_1(k7_relat_1(A_16,A_56),k6_relat_1(k2_relat_1(A_16))) = k5_relat_1(k6_relat_1(A_56),A_16)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_16)))
      | ~ v1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_537])).

tff(c_604,plain,(
    ! [A_16,A_56] :
      ( k5_relat_1(k7_relat_1(A_16,A_56),k6_relat_1(k2_relat_1(A_16))) = k5_relat_1(k6_relat_1(A_56),A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_586])).

tff(c_9112,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1('#skF_2')),'#skF_3') = k7_relat_1('#skF_3',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8768,c_604])).

tff(c_9150,plain,(
    k5_relat_1(k6_relat_1(k2_relat_1('#skF_2')),'#skF_3') = k7_relat_1('#skF_3',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_9112])).

tff(c_173,plain,(
    ! [A_16,C_44] :
      ( k5_relat_1(A_16,k5_relat_1(k6_relat_1(k2_relat_1(A_16)),C_44)) = k5_relat_1(A_16,C_44)
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_16)))
      | ~ v1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_148])).

tff(c_185,plain,(
    ! [A_16,C_44] :
      ( k5_relat_1(A_16,k5_relat_1(k6_relat_1(k2_relat_1(A_16)),C_44)) = k5_relat_1(A_16,C_44)
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_173])).

tff(c_9186,plain,
    ( k5_relat_1('#skF_2',k7_relat_1('#skF_3',k2_relat_1('#skF_2'))) = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9150,c_185])).

tff(c_9214,plain,(
    k5_relat_1('#skF_2',k7_relat_1('#skF_3',k2_relat_1('#skF_2'))) = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_9186])).

tff(c_33663,plain,(
    ! [C_676,A_677,A_678] :
      ( k7_relat_1(C_676,k3_xboole_0(A_677,k1_relat_1(k7_relat_1(k7_relat_1(C_676,A_677),A_678)))) = k7_relat_1(k7_relat_1(C_676,A_677),A_678)
      | ~ v1_relat_1(k7_relat_1(C_676,A_677))
      | ~ v1_relat_1(k7_relat_1(C_676,A_677))
      | ~ v1_relat_1(C_676) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_264])).

tff(c_34668,plain,
    ( k7_relat_1(k7_relat_1('#skF_3','#skF_1'),k2_relat_1('#skF_2')) = k7_relat_1('#skF_3',k3_xboole_0('#skF_1',k2_relat_1('#skF_2')))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_33663])).

tff(c_35049,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),k2_relat_1('#skF_2')) = k7_relat_1('#skF_3',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_232,c_232,c_320,c_34668])).

tff(c_355,plain,(
    ! [A_52,C_53] :
      ( k5_relat_1(A_52,k5_relat_1(k6_relat_1(k2_relat_1(A_52)),C_53)) = k5_relat_1(A_52,C_53)
      | ~ v1_relat_1(C_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_173])).

tff(c_391,plain,(
    ! [A_52,B_22] :
      ( k5_relat_1(A_52,k7_relat_1(B_22,k2_relat_1(A_52))) = k5_relat_1(A_52,B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_52)
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_355])).

tff(c_35107,plain,
    ( k5_relat_1('#skF_2',k7_relat_1('#skF_3',k2_relat_1('#skF_2'))) = k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35049,c_391])).

tff(c_35166,plain,(
    k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')) = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_26,c_232,c_9214,c_35107])).

tff(c_35168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_35166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:30:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.10/6.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.10/6.89  
% 14.10/6.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.10/6.89  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 14.10/6.89  
% 14.10/6.89  %Foreground sorts:
% 14.10/6.89  
% 14.10/6.89  
% 14.10/6.89  %Background operators:
% 14.10/6.89  
% 14.10/6.89  
% 14.10/6.89  %Foreground operators:
% 14.10/6.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.10/6.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.10/6.89  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.10/6.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.10/6.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.10/6.89  tff('#skF_2', type, '#skF_2': $i).
% 14.10/6.89  tff('#skF_3', type, '#skF_3': $i).
% 14.10/6.89  tff('#skF_1', type, '#skF_1': $i).
% 14.10/6.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.10/6.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.10/6.89  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 14.10/6.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.10/6.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.10/6.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.10/6.89  
% 14.22/6.90  tff(f_79, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(k7_relat_1(C, A))) => (k5_relat_1(B, k7_relat_1(C, A)) = k5_relat_1(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_relat_1)).
% 14.22/6.90  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 14.22/6.90  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 14.22/6.90  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 14.22/6.90  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 14.22/6.90  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 14.22/6.90  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 14.22/6.90  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 14.22/6.90  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 14.22/6.90  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 14.22/6.90  tff(c_20, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1'))!=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.22/6.90  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.22/6.90  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.22/6.90  tff(c_43, plain, (![A_28, B_29]: (k5_relat_1(k6_relat_1(A_28), B_29)=k7_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.22/6.90  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.22/6.90  tff(c_53, plain, (![B_29, A_28]: (v1_relat_1(k7_relat_1(B_29, A_28)) | ~v1_relat_1(B_29) | ~v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_43, c_2])).
% 14.22/6.90  tff(c_65, plain, (![B_29, A_28]: (v1_relat_1(k7_relat_1(B_29, A_28)) | ~v1_relat_1(B_29))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_53])).
% 14.22/6.90  tff(c_22, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.22/6.90  tff(c_109, plain, (![B_37, A_38]: (k1_relat_1(k7_relat_1(B_37, A_38))=A_38 | ~r1_tarski(A_38, k1_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.22/6.90  tff(c_113, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), k2_relat_1('#skF_2')))=k2_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_109])).
% 14.22/6.90  tff(c_223, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_113])).
% 14.22/6.90  tff(c_226, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_65, c_223])).
% 14.22/6.90  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_226])).
% 14.22/6.90  tff(c_232, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_113])).
% 14.22/6.90  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.22/6.90  tff(c_6, plain, (![C_6, A_4, B_5]: (k7_relat_1(k7_relat_1(C_6, A_4), B_5)=k7_relat_1(C_6, k3_xboole_0(A_4, B_5)) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.22/6.90  tff(c_231, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), k2_relat_1('#skF_2')))=k2_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_113])).
% 14.22/6.90  tff(c_246, plain, (k1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_231])).
% 14.22/6.90  tff(c_250, plain, (k1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))))=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_246])).
% 14.22/6.90  tff(c_14, plain, (![B_18, A_17]: (k3_xboole_0(k1_relat_1(B_18), A_17)=k1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.22/6.90  tff(c_94, plain, (![B_35, A_36]: (k7_relat_1(B_35, k3_xboole_0(k1_relat_1(B_35), A_36))=k7_relat_1(B_35, A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.22/6.90  tff(c_264, plain, (![B_49, A_50]: (k7_relat_1(B_49, k1_relat_1(k7_relat_1(B_49, A_50)))=k7_relat_1(B_49, A_50) | ~v1_relat_1(B_49) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_14, c_94])).
% 14.22/6.90  tff(c_293, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', k2_relat_1('#skF_2')))=k7_relat_1('#skF_3', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_250, c_264])).
% 14.22/6.90  tff(c_320, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', k2_relat_1('#skF_2')))=k7_relat_1('#skF_3', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_293])).
% 14.22/6.90  tff(c_12, plain, (![A_16]: (k5_relat_1(A_16, k6_relat_1(k2_relat_1(A_16)))=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.22/6.90  tff(c_18, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.22/6.91  tff(c_148, plain, (![A_42, B_43, C_44]: (k5_relat_1(k5_relat_1(A_42, B_43), C_44)=k5_relat_1(A_42, k5_relat_1(B_43, C_44)) | ~v1_relat_1(C_44) | ~v1_relat_1(B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.22/6.91  tff(c_170, plain, (![A_21, B_22, C_44]: (k5_relat_1(k6_relat_1(A_21), k5_relat_1(B_22, C_44))=k5_relat_1(k7_relat_1(B_22, A_21), C_44) | ~v1_relat_1(C_44) | ~v1_relat_1(B_22) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_18, c_148])).
% 14.22/6.91  tff(c_537, plain, (![A_56, B_57, C_58]: (k5_relat_1(k6_relat_1(A_56), k5_relat_1(B_57, C_58))=k5_relat_1(k7_relat_1(B_57, A_56), C_58) | ~v1_relat_1(C_58) | ~v1_relat_1(B_57))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_170])).
% 14.22/6.91  tff(c_8276, plain, (![B_306, C_307, A_308]: (k7_relat_1(k5_relat_1(B_306, C_307), A_308)=k5_relat_1(k7_relat_1(B_306, A_308), C_307) | ~v1_relat_1(C_307) | ~v1_relat_1(B_306) | ~v1_relat_1(k5_relat_1(B_306, C_307)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_537])).
% 14.22/6.91  tff(c_8415, plain, (![A_309, B_310, A_311]: (k7_relat_1(k5_relat_1(A_309, B_310), A_311)=k5_relat_1(k7_relat_1(A_309, A_311), B_310) | ~v1_relat_1(B_310) | ~v1_relat_1(A_309))), inference(resolution, [status(thm)], [c_2, c_8276])).
% 14.22/6.91  tff(c_8539, plain, (![A_16, A_311]: (k5_relat_1(k7_relat_1(A_16, A_311), k6_relat_1(k2_relat_1(A_16)))=k7_relat_1(A_16, A_311) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_16))) | ~v1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8415])).
% 14.22/6.91  tff(c_8556, plain, (![A_312, A_313]: (k5_relat_1(k7_relat_1(A_312, A_313), k6_relat_1(k2_relat_1(A_312)))=k7_relat_1(A_312, A_313) | ~v1_relat_1(A_312))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8539])).
% 14.22/6.91  tff(c_8686, plain, (k5_relat_1(k7_relat_1('#skF_3', k2_relat_1('#skF_2')), k6_relat_1(k2_relat_1('#skF_3')))=k7_relat_1('#skF_3', k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_320, c_8556])).
% 14.22/6.91  tff(c_8768, plain, (k5_relat_1(k7_relat_1('#skF_3', k2_relat_1('#skF_2')), k6_relat_1(k2_relat_1('#skF_3')))=k7_relat_1('#skF_3', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_320, c_8686])).
% 14.22/6.91  tff(c_586, plain, (![A_16, A_56]: (k5_relat_1(k7_relat_1(A_16, A_56), k6_relat_1(k2_relat_1(A_16)))=k5_relat_1(k6_relat_1(A_56), A_16) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_16))) | ~v1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_12, c_537])).
% 14.22/6.91  tff(c_604, plain, (![A_16, A_56]: (k5_relat_1(k7_relat_1(A_16, A_56), k6_relat_1(k2_relat_1(A_16)))=k5_relat_1(k6_relat_1(A_56), A_16) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_586])).
% 14.22/6.91  tff(c_9112, plain, (k5_relat_1(k6_relat_1(k2_relat_1('#skF_2')), '#skF_3')=k7_relat_1('#skF_3', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8768, c_604])).
% 14.22/6.91  tff(c_9150, plain, (k5_relat_1(k6_relat_1(k2_relat_1('#skF_2')), '#skF_3')=k7_relat_1('#skF_3', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_9112])).
% 14.22/6.91  tff(c_173, plain, (![A_16, C_44]: (k5_relat_1(A_16, k5_relat_1(k6_relat_1(k2_relat_1(A_16)), C_44))=k5_relat_1(A_16, C_44) | ~v1_relat_1(C_44) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_16))) | ~v1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_12, c_148])).
% 14.22/6.91  tff(c_185, plain, (![A_16, C_44]: (k5_relat_1(A_16, k5_relat_1(k6_relat_1(k2_relat_1(A_16)), C_44))=k5_relat_1(A_16, C_44) | ~v1_relat_1(C_44) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_173])).
% 14.22/6.91  tff(c_9186, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', k2_relat_1('#skF_2')))=k5_relat_1('#skF_2', '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9150, c_185])).
% 14.22/6.91  tff(c_9214, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', k2_relat_1('#skF_2')))=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_9186])).
% 14.22/6.91  tff(c_33663, plain, (![C_676, A_677, A_678]: (k7_relat_1(C_676, k3_xboole_0(A_677, k1_relat_1(k7_relat_1(k7_relat_1(C_676, A_677), A_678))))=k7_relat_1(k7_relat_1(C_676, A_677), A_678) | ~v1_relat_1(k7_relat_1(C_676, A_677)) | ~v1_relat_1(k7_relat_1(C_676, A_677)) | ~v1_relat_1(C_676))), inference(superposition, [status(thm), theory('equality')], [c_6, c_264])).
% 14.22/6.91  tff(c_34668, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), k2_relat_1('#skF_2'))=k7_relat_1('#skF_3', k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_231, c_33663])).
% 14.22/6.91  tff(c_35049, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), k2_relat_1('#skF_2'))=k7_relat_1('#skF_3', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_232, c_232, c_320, c_34668])).
% 14.22/6.91  tff(c_355, plain, (![A_52, C_53]: (k5_relat_1(A_52, k5_relat_1(k6_relat_1(k2_relat_1(A_52)), C_53))=k5_relat_1(A_52, C_53) | ~v1_relat_1(C_53) | ~v1_relat_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_173])).
% 14.22/6.91  tff(c_391, plain, (![A_52, B_22]: (k5_relat_1(A_52, k7_relat_1(B_22, k2_relat_1(A_52)))=k5_relat_1(A_52, B_22) | ~v1_relat_1(B_22) | ~v1_relat_1(A_52) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_18, c_355])).
% 14.22/6.91  tff(c_35107, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', k2_relat_1('#skF_2')))=k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_35049, c_391])).
% 14.22/6.91  tff(c_35166, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1'))=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_26, c_232, c_9214, c_35107])).
% 14.22/6.91  tff(c_35168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_35166])).
% 14.22/6.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.22/6.91  
% 14.22/6.91  Inference rules
% 14.22/6.91  ----------------------
% 14.22/6.91  #Ref     : 0
% 14.22/6.91  #Sup     : 6951
% 14.22/6.91  #Fact    : 0
% 14.22/6.91  #Define  : 0
% 14.22/6.91  #Split   : 7
% 14.22/6.91  #Chain   : 0
% 14.22/6.91  #Close   : 0
% 14.22/6.91  
% 14.22/6.91  Ordering : KBO
% 14.22/6.91  
% 14.22/6.91  Simplification rules
% 14.22/6.91  ----------------------
% 14.22/6.91  #Subsume      : 546
% 14.22/6.91  #Demod        : 15540
% 14.22/6.91  #Tautology    : 2881
% 14.22/6.91  #SimpNegUnit  : 1
% 14.22/6.91  #BackRed      : 91
% 14.22/6.91  
% 14.22/6.91  #Partial instantiations: 0
% 14.22/6.91  #Strategies tried      : 1
% 14.22/6.91  
% 14.22/6.91  Timing (in seconds)
% 14.22/6.91  ----------------------
% 14.22/6.91  Preprocessing        : 0.30
% 14.22/6.91  Parsing              : 0.16
% 14.22/6.91  CNF conversion       : 0.02
% 14.22/6.91  Main loop            : 5.85
% 14.22/6.91  Inferencing          : 1.17
% 14.22/6.91  Reduction            : 3.58
% 14.22/6.91  Demodulation         : 3.22
% 14.22/6.91  BG Simplification    : 0.16
% 14.22/6.91  Subsumption          : 0.74
% 14.22/6.91  Abstraction          : 0.29
% 14.22/6.91  MUC search           : 0.00
% 14.22/6.91  Cooper               : 0.00
% 14.22/6.91  Total                : 6.19
% 14.22/6.91  Index Insertion      : 0.00
% 14.22/6.91  Index Deletion       : 0.00
% 14.22/6.91  Index Matching       : 0.00
% 14.22/6.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
