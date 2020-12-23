%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:53 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 157 expanded)
%              Number of leaves         :   23 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 408 expanded)
%              Number of equality atoms :   47 ( 162 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    ! [A_23] :
      ( k2_relat_1(k2_funct_1(A_23)) = k1_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    ! [A_22] :
      ( v1_relat_1(k2_funct_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_594,plain,(
    ! [A_56,B_57] :
      ( k5_relat_1(k6_relat_1(A_56),B_57) = B_57
      | ~ r1_tarski(k1_relat_1(B_57),A_56)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_607,plain,(
    ! [B_57] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_57)),B_57) = B_57
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_594])).

tff(c_721,plain,(
    ! [B_64,C_65,A_66] :
      ( k2_relat_1(k5_relat_1(B_64,C_65)) = k2_relat_1(k5_relat_1(A_66,C_65))
      | k2_relat_1(B_64) != k2_relat_1(A_66)
      | ~ v1_relat_1(C_65)
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_775,plain,(
    ! [B_64,B_57] :
      ( k2_relat_1(k5_relat_1(B_64,B_57)) = k2_relat_1(B_57)
      | k2_relat_1(k6_relat_1(k1_relat_1(B_57))) != k2_relat_1(B_64)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(B_57)))
      | ~ v1_relat_1(B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_721])).

tff(c_1048,plain,(
    ! [B_76,B_77] :
      ( k2_relat_1(k5_relat_1(B_76,B_77)) = k2_relat_1(B_77)
      | k2_relat_1(B_76) != k1_relat_1(B_77)
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16,c_775])).

tff(c_28,plain,(
    ! [A_23] :
      ( k1_relat_1(k2_funct_1(A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_21] :
      ( k5_relat_1(A_21,k6_relat_1(k2_relat_1(A_21))) = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_191,plain,(
    ! [C_41,B_42,A_43] :
      ( k1_relat_1(k5_relat_1(C_41,B_42)) = k1_relat_1(k5_relat_1(C_41,A_43))
      | k1_relat_1(B_42) != k1_relat_1(A_43)
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_254,plain,(
    ! [A_21,A_43] :
      ( k1_relat_1(k5_relat_1(A_21,A_43)) = k1_relat_1(A_21)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_21))) != k1_relat_1(A_43)
      | ~ v1_relat_1(A_21)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_21)))
      | ~ v1_relat_1(A_43)
      | ~ v1_relat_1(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_191])).

tff(c_340,plain,(
    ! [A_46,A_47] :
      ( k1_relat_1(k5_relat_1(A_46,A_47)) = k1_relat_1(A_46)
      | k2_relat_1(A_46) != k1_relat_1(A_47)
      | ~ v1_relat_1(A_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_254])).

tff(c_30,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_60,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_362,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_60])).

tff(c_391,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_362])).

tff(c_407,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_410,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_407])).

tff(c_414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_410])).

tff(c_415,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_488,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_491,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_488])).

tff(c_495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_491])).

tff(c_496,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_553,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_496])).

tff(c_557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_553])).

tff(c_558,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1076,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1048,c_558])).

tff(c_1121,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1076])).

tff(c_1144,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1121])).

tff(c_1260,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1144])).

tff(c_1264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1260])).

tff(c_1265,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1121])).

tff(c_1269,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1265])).

tff(c_1273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_1269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:18:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.46  
% 3.32/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.46  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.32/1.46  
% 3.32/1.46  %Foreground sorts:
% 3.32/1.46  
% 3.32/1.46  
% 3.32/1.46  %Background operators:
% 3.32/1.46  
% 3.32/1.46  
% 3.32/1.46  %Foreground operators:
% 3.32/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.46  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.32/1.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.32/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.32/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.32/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.47  
% 3.32/1.48  tff(f_100, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 3.32/1.48  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.32/1.48  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.32/1.48  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.32/1.48  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.32/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.32/1.48  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 3.32/1.48  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 3.32/1.48  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.32/1.48  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 3.32/1.48  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.32/1.48  tff(c_34, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.32/1.48  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.32/1.48  tff(c_26, plain, (![A_23]: (k2_relat_1(k2_funct_1(A_23))=k1_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.32/1.48  tff(c_24, plain, (![A_22]: (v1_relat_1(k2_funct_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.32/1.48  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/1.48  tff(c_16, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.48  tff(c_594, plain, (![A_56, B_57]: (k5_relat_1(k6_relat_1(A_56), B_57)=B_57 | ~r1_tarski(k1_relat_1(B_57), A_56) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.32/1.48  tff(c_607, plain, (![B_57]: (k5_relat_1(k6_relat_1(k1_relat_1(B_57)), B_57)=B_57 | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_6, c_594])).
% 3.32/1.48  tff(c_721, plain, (![B_64, C_65, A_66]: (k2_relat_1(k5_relat_1(B_64, C_65))=k2_relat_1(k5_relat_1(A_66, C_65)) | k2_relat_1(B_64)!=k2_relat_1(A_66) | ~v1_relat_1(C_65) | ~v1_relat_1(B_64) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.32/1.48  tff(c_775, plain, (![B_64, B_57]: (k2_relat_1(k5_relat_1(B_64, B_57))=k2_relat_1(B_57) | k2_relat_1(k6_relat_1(k1_relat_1(B_57)))!=k2_relat_1(B_64) | ~v1_relat_1(B_57) | ~v1_relat_1(B_64) | ~v1_relat_1(k6_relat_1(k1_relat_1(B_57))) | ~v1_relat_1(B_57))), inference(superposition, [status(thm), theory('equality')], [c_607, c_721])).
% 3.32/1.48  tff(c_1048, plain, (![B_76, B_77]: (k2_relat_1(k5_relat_1(B_76, B_77))=k2_relat_1(B_77) | k2_relat_1(B_76)!=k1_relat_1(B_77) | ~v1_relat_1(B_76) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16, c_775])).
% 3.32/1.48  tff(c_28, plain, (![A_23]: (k1_relat_1(k2_funct_1(A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.32/1.48  tff(c_14, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.48  tff(c_20, plain, (![A_21]: (k5_relat_1(A_21, k6_relat_1(k2_relat_1(A_21)))=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.32/1.48  tff(c_191, plain, (![C_41, B_42, A_43]: (k1_relat_1(k5_relat_1(C_41, B_42))=k1_relat_1(k5_relat_1(C_41, A_43)) | k1_relat_1(B_42)!=k1_relat_1(A_43) | ~v1_relat_1(C_41) | ~v1_relat_1(B_42) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.32/1.48  tff(c_254, plain, (![A_21, A_43]: (k1_relat_1(k5_relat_1(A_21, A_43))=k1_relat_1(A_21) | k1_relat_1(k6_relat_1(k2_relat_1(A_21)))!=k1_relat_1(A_43) | ~v1_relat_1(A_21) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_21))) | ~v1_relat_1(A_43) | ~v1_relat_1(A_21))), inference(superposition, [status(thm), theory('equality')], [c_20, c_191])).
% 3.32/1.48  tff(c_340, plain, (![A_46, A_47]: (k1_relat_1(k5_relat_1(A_46, A_47))=k1_relat_1(A_46) | k2_relat_1(A_46)!=k1_relat_1(A_47) | ~v1_relat_1(A_47) | ~v1_relat_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14, c_254])).
% 3.32/1.48  tff(c_30, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.32/1.48  tff(c_60, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.32/1.48  tff(c_362, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_340, c_60])).
% 3.32/1.48  tff(c_391, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_362])).
% 3.32/1.48  tff(c_407, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_391])).
% 3.32/1.48  tff(c_410, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_407])).
% 3.32/1.48  tff(c_414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_410])).
% 3.32/1.48  tff(c_415, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_391])).
% 3.32/1.48  tff(c_488, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_415])).
% 3.32/1.48  tff(c_491, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_488])).
% 3.32/1.48  tff(c_495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_491])).
% 3.32/1.48  tff(c_496, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_415])).
% 3.32/1.48  tff(c_553, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_496])).
% 3.32/1.48  tff(c_557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_553])).
% 3.32/1.48  tff(c_558, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.32/1.48  tff(c_1076, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1048, c_558])).
% 3.32/1.48  tff(c_1121, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1076])).
% 3.32/1.48  tff(c_1144, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1121])).
% 3.32/1.48  tff(c_1260, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1144])).
% 3.32/1.48  tff(c_1264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1260])).
% 3.32/1.48  tff(c_1265, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1121])).
% 3.32/1.48  tff(c_1269, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1265])).
% 3.32/1.48  tff(c_1273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_1269])).
% 3.32/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.48  
% 3.32/1.48  Inference rules
% 3.32/1.48  ----------------------
% 3.32/1.48  #Ref     : 1
% 3.32/1.48  #Sup     : 265
% 3.32/1.48  #Fact    : 0
% 3.32/1.48  #Define  : 0
% 3.32/1.48  #Split   : 5
% 3.32/1.48  #Chain   : 0
% 3.32/1.48  #Close   : 0
% 3.32/1.48  
% 3.32/1.48  Ordering : KBO
% 3.32/1.48  
% 3.32/1.48  Simplification rules
% 3.32/1.48  ----------------------
% 3.32/1.48  #Subsume      : 16
% 3.32/1.48  #Demod        : 332
% 3.32/1.48  #Tautology    : 103
% 3.32/1.48  #SimpNegUnit  : 0
% 3.32/1.48  #BackRed      : 0
% 3.32/1.48  
% 3.32/1.48  #Partial instantiations: 0
% 3.32/1.48  #Strategies tried      : 1
% 3.32/1.48  
% 3.32/1.48  Timing (in seconds)
% 3.32/1.48  ----------------------
% 3.32/1.48  Preprocessing        : 0.30
% 3.32/1.48  Parsing              : 0.16
% 3.32/1.48  CNF conversion       : 0.02
% 3.32/1.48  Main loop            : 0.43
% 3.32/1.48  Inferencing          : 0.16
% 3.32/1.48  Reduction            : 0.13
% 3.32/1.48  Demodulation         : 0.10
% 3.32/1.48  BG Simplification    : 0.03
% 3.32/1.48  Subsumption          : 0.07
% 3.32/1.48  Abstraction          : 0.03
% 3.32/1.48  MUC search           : 0.00
% 3.32/1.48  Cooper               : 0.00
% 3.32/1.48  Total                : 0.76
% 3.32/1.48  Index Insertion      : 0.00
% 3.32/1.48  Index Deletion       : 0.00
% 3.32/1.48  Index Matching       : 0.00
% 3.32/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
