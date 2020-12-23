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
% DateTime   : Thu Dec  3 10:03:48 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 148 expanded)
%              Number of leaves         :   22 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  108 ( 367 expanded)
%              Number of equality atoms :   36 ( 124 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2019,plain,(
    ! [A_59] :
      ( k4_relat_1(A_59) = k2_funct_1(A_59)
      | ~ v2_funct_1(A_59)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2022,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_2019])).

tff(c_2025,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2022])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2038,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2025,c_8])).

tff(c_2048,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2038])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k5_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_85,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_87,plain,(
    ! [A_24] :
      ( k4_relat_1(A_24) = k2_funct_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_90,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_87])).

tff(c_93,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_90])).

tff(c_106,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_8])).

tff(c_116,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_106])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_7] :
      ( k1_relat_1(k4_relat_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_252,plain,(
    ! [A_28,B_29] :
      ( k1_relat_1(k5_relat_1(A_28,B_29)) = k1_relat_1(A_28)
      | ~ r1_tarski(k2_relat_1(A_28),k1_relat_1(B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1899,plain,(
    ! [A_54,A_55] :
      ( k1_relat_1(k5_relat_1(A_54,k4_relat_1(A_55))) = k1_relat_1(A_54)
      | ~ r1_tarski(k2_relat_1(A_54),k2_relat_1(A_55))
      | ~ v1_relat_1(k4_relat_1(A_55))
      | ~ v1_relat_1(A_54)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_252])).

tff(c_1931,plain,(
    ! [A_56] :
      ( k1_relat_1(k5_relat_1(A_56,k4_relat_1(A_56))) = k1_relat_1(A_56)
      | ~ v1_relat_1(k4_relat_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_1899])).

tff(c_1990,plain,
    ( k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_1931])).

tff(c_2009,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_116,c_93,c_1990])).

tff(c_2011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_2009])).

tff(c_2012,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_2013,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_12,plain,(
    ! [A_6] :
      ( k4_relat_1(k4_relat_1(A_6)) = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2035,plain,
    ( k4_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2025,c_12])).

tff(c_2046,plain,(
    k4_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2035])).

tff(c_2078,plain,(
    ! [B_60,A_61] :
      ( k5_relat_1(k4_relat_1(B_60),k4_relat_1(A_61)) = k4_relat_1(k5_relat_1(A_61,B_60))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2099,plain,(
    ! [B_60] :
      ( k5_relat_1(k4_relat_1(B_60),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_60))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2025,c_2078])).

tff(c_2210,plain,(
    ! [B_66] :
      ( k5_relat_1(k4_relat_1(B_66),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2099])).

tff(c_2225,plain,
    ( k4_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k5_relat_1('#skF_1',k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2046,c_2210])).

tff(c_2239,plain,(
    k4_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k5_relat_1('#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2048,c_2225])).

tff(c_2257,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1')))
    | ~ v1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2239,c_16])).

tff(c_2269,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2013,c_2257])).

tff(c_2270,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2012,c_2269])).

tff(c_2277,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_2270])).

tff(c_2281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2048,c_2277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.77  
% 4.50/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.78  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 4.50/1.78  
% 4.50/1.78  %Foreground sorts:
% 4.50/1.78  
% 4.50/1.78  
% 4.50/1.78  %Background operators:
% 4.50/1.78  
% 4.50/1.78  
% 4.50/1.78  %Foreground operators:
% 4.50/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.50/1.78  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.50/1.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.50/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.50/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.50/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.50/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.50/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.50/1.78  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.50/1.78  
% 4.50/1.79  tff(f_86, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 4.50/1.79  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 4.50/1.79  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.50/1.79  tff(f_41, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.50/1.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.50/1.79  tff(f_51, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 4.50/1.79  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 4.50/1.79  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 4.50/1.79  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 4.50/1.79  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.50/1.79  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.50/1.79  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.50/1.79  tff(c_2019, plain, (![A_59]: (k4_relat_1(A_59)=k2_funct_1(A_59) | ~v2_funct_1(A_59) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.50/1.79  tff(c_2022, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_2019])).
% 4.50/1.79  tff(c_2025, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2022])).
% 4.50/1.79  tff(c_8, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.50/1.79  tff(c_2038, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2025, c_8])).
% 4.50/1.79  tff(c_2048, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2038])).
% 4.50/1.79  tff(c_10, plain, (![A_4, B_5]: (v1_relat_1(k5_relat_1(A_4, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.50/1.79  tff(c_24, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.50/1.79  tff(c_85, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 4.50/1.79  tff(c_87, plain, (![A_24]: (k4_relat_1(A_24)=k2_funct_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.50/1.79  tff(c_90, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_87])).
% 4.50/1.79  tff(c_93, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_90])).
% 4.50/1.79  tff(c_106, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_93, c_8])).
% 4.50/1.79  tff(c_116, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_106])).
% 4.50/1.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/1.79  tff(c_16, plain, (![A_7]: (k1_relat_1(k4_relat_1(A_7))=k2_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.50/1.79  tff(c_252, plain, (![A_28, B_29]: (k1_relat_1(k5_relat_1(A_28, B_29))=k1_relat_1(A_28) | ~r1_tarski(k2_relat_1(A_28), k1_relat_1(B_29)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.50/1.79  tff(c_1899, plain, (![A_54, A_55]: (k1_relat_1(k5_relat_1(A_54, k4_relat_1(A_55)))=k1_relat_1(A_54) | ~r1_tarski(k2_relat_1(A_54), k2_relat_1(A_55)) | ~v1_relat_1(k4_relat_1(A_55)) | ~v1_relat_1(A_54) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_16, c_252])).
% 4.50/1.79  tff(c_1931, plain, (![A_56]: (k1_relat_1(k5_relat_1(A_56, k4_relat_1(A_56)))=k1_relat_1(A_56) | ~v1_relat_1(k4_relat_1(A_56)) | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_6, c_1899])).
% 4.50/1.79  tff(c_1990, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_93, c_1931])).
% 4.50/1.79  tff(c_2009, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_116, c_93, c_1990])).
% 4.50/1.79  tff(c_2011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_2009])).
% 4.50/1.79  tff(c_2012, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 4.50/1.79  tff(c_2013, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 4.50/1.79  tff(c_12, plain, (![A_6]: (k4_relat_1(k4_relat_1(A_6))=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.50/1.79  tff(c_2035, plain, (k4_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2025, c_12])).
% 4.50/1.79  tff(c_2046, plain, (k4_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2035])).
% 4.50/1.79  tff(c_2078, plain, (![B_60, A_61]: (k5_relat_1(k4_relat_1(B_60), k4_relat_1(A_61))=k4_relat_1(k5_relat_1(A_61, B_60)) | ~v1_relat_1(B_60) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.50/1.79  tff(c_2099, plain, (![B_60]: (k5_relat_1(k4_relat_1(B_60), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_60)) | ~v1_relat_1(B_60) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2025, c_2078])).
% 4.50/1.79  tff(c_2210, plain, (![B_66]: (k5_relat_1(k4_relat_1(B_66), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_66)) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2099])).
% 4.50/1.79  tff(c_2225, plain, (k4_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k5_relat_1('#skF_1', k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2046, c_2210])).
% 4.50/1.79  tff(c_2239, plain, (k4_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k5_relat_1('#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2048, c_2225])).
% 4.50/1.79  tff(c_2257, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1'))) | ~v1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2239, c_16])).
% 4.50/1.79  tff(c_2269, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2013, c_2257])).
% 4.50/1.79  tff(c_2270, plain, (~v1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_2012, c_2269])).
% 4.50/1.79  tff(c_2277, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_2270])).
% 4.50/1.79  tff(c_2281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2048, c_2277])).
% 4.50/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.79  
% 4.50/1.79  Inference rules
% 4.50/1.79  ----------------------
% 4.50/1.79  #Ref     : 0
% 4.50/1.79  #Sup     : 568
% 4.50/1.79  #Fact    : 0
% 4.50/1.79  #Define  : 0
% 4.50/1.79  #Split   : 1
% 4.50/1.79  #Chain   : 0
% 4.50/1.79  #Close   : 0
% 4.50/1.79  
% 4.50/1.79  Ordering : KBO
% 4.50/1.79  
% 4.50/1.79  Simplification rules
% 4.50/1.79  ----------------------
% 4.50/1.79  #Subsume      : 43
% 4.50/1.79  #Demod        : 516
% 4.50/1.79  #Tautology    : 198
% 4.50/1.79  #SimpNegUnit  : 3
% 4.50/1.79  #BackRed      : 0
% 4.50/1.79  
% 4.50/1.79  #Partial instantiations: 0
% 4.50/1.79  #Strategies tried      : 1
% 4.50/1.79  
% 4.50/1.79  Timing (in seconds)
% 4.50/1.79  ----------------------
% 4.50/1.79  Preprocessing        : 0.31
% 4.50/1.79  Parsing              : 0.16
% 4.50/1.79  CNF conversion       : 0.02
% 4.50/1.79  Main loop            : 0.72
% 4.50/1.79  Inferencing          : 0.24
% 4.50/1.79  Reduction            : 0.23
% 4.50/1.79  Demodulation         : 0.17
% 4.50/1.79  BG Simplification    : 0.03
% 4.50/1.79  Subsumption          : 0.16
% 4.50/1.79  Abstraction          : 0.04
% 4.50/1.79  MUC search           : 0.00
% 4.50/1.79  Cooper               : 0.00
% 4.50/1.79  Total                : 1.05
% 4.50/1.79  Index Insertion      : 0.00
% 4.50/1.79  Index Deletion       : 0.00
% 4.50/1.79  Index Matching       : 0.00
% 4.50/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
