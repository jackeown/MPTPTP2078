%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:35 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   74 ( 100 expanded)
%              Number of equality atoms :   37 (  46 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_50,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_15] : k4_relat_1(k6_relat_1(A_15)) = k6_relat_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_146,plain,(
    ! [A_36,B_37] :
      ( k5_relat_1(k6_relat_1(A_36),B_37) = B_37
      | ~ r1_tarski(k1_relat_1(B_37),A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_149,plain,(
    ! [A_36,A_14] :
      ( k5_relat_1(k6_relat_1(A_36),k6_relat_1(A_14)) = k6_relat_1(A_14)
      | ~ r1_tarski(A_14,A_36)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_146])).

tff(c_151,plain,(
    ! [A_36,A_14] :
      ( k5_relat_1(k6_relat_1(A_36),k6_relat_1(A_14)) = k6_relat_1(A_14)
      | ~ r1_tarski(A_14,A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_149])).

tff(c_264,plain,(
    ! [B_47,A_48] :
      ( k5_relat_1(k4_relat_1(B_47),k4_relat_1(A_48)) = k4_relat_1(k5_relat_1(A_48,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_276,plain,(
    ! [B_47,A_15] :
      ( k5_relat_1(k4_relat_1(B_47),k6_relat_1(A_15)) = k4_relat_1(k5_relat_1(k6_relat_1(A_15),B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_264])).

tff(c_284,plain,(
    ! [B_51,A_52] :
      ( k5_relat_1(k4_relat_1(B_51),k6_relat_1(A_52)) = k4_relat_1(k5_relat_1(k6_relat_1(A_52),B_51))
      | ~ v1_relat_1(B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_276])).

tff(c_301,plain,(
    ! [A_52,A_15] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_52),k6_relat_1(A_15))) = k5_relat_1(k6_relat_1(A_15),k6_relat_1(A_52))
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_284])).

tff(c_345,plain,(
    ! [A_54,A_55] : k4_relat_1(k5_relat_1(k6_relat_1(A_54),k6_relat_1(A_55))) = k5_relat_1(k6_relat_1(A_55),k6_relat_1(A_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_301])).

tff(c_374,plain,(
    ! [A_14,A_36] :
      ( k5_relat_1(k6_relat_1(A_14),k6_relat_1(A_36)) = k4_relat_1(k6_relat_1(A_14))
      | ~ r1_tarski(A_14,A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_345])).

tff(c_399,plain,(
    ! [A_56,A_57] :
      ( k5_relat_1(k6_relat_1(A_56),k6_relat_1(A_57)) = k6_relat_1(A_56)
      | ~ r1_tarski(A_56,A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_374])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_415,plain,(
    ! [A_57,A_56] :
      ( k7_relat_1(k6_relat_1(A_57),A_56) = k6_relat_1(A_56)
      | ~ v1_relat_1(k6_relat_1(A_57))
      | ~ r1_tarski(A_56,A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_24])).

tff(c_461,plain,(
    ! [A_58,A_59] :
      ( k7_relat_1(k6_relat_1(A_58),A_59) = k6_relat_1(A_59)
      | ~ r1_tarski(A_59,A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_415])).

tff(c_16,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_97,plain,(
    ! [A_33,B_34] :
      ( k5_relat_1(k6_relat_1(A_33),B_34) = k7_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_relat_1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_111,plain,(
    ! [A_33] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_33))),A_33) = k6_relat_1(A_33)
      | ~ v1_relat_1(k6_relat_1(A_33))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_33)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_22])).

tff(c_128,plain,(
    ! [A_33] : k7_relat_1(k6_relat_1(A_33),A_33) = k6_relat_1(A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_16,c_111])).

tff(c_218,plain,(
    ! [C_42,A_43,B_44] :
      ( k7_relat_1(k7_relat_1(C_42,A_43),B_44) = k7_relat_1(C_42,k3_xboole_0(A_43,B_44))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_236,plain,(
    ! [A_33,B_44] :
      ( k7_relat_1(k6_relat_1(A_33),k3_xboole_0(A_33,B_44)) = k7_relat_1(k6_relat_1(A_33),B_44)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_218])).

tff(c_242,plain,(
    ! [A_33,B_44] : k7_relat_1(k6_relat_1(A_33),k3_xboole_0(A_33,B_44)) = k7_relat_1(k6_relat_1(A_33),B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_236])).

tff(c_468,plain,(
    ! [A_58,B_44] :
      ( k7_relat_1(k6_relat_1(A_58),B_44) = k6_relat_1(k3_xboole_0(A_58,B_44))
      | ~ r1_tarski(k3_xboole_0(A_58,B_44),A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_242])).

tff(c_496,plain,(
    ! [A_58,B_44] : k7_relat_1(k6_relat_1(A_58),B_44) = k6_relat_1(k3_xboole_0(A_58,B_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_468])).

tff(c_26,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_103,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_26])).

tff(c_124,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_103])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.17/1.29  
% 2.17/1.29  %Foreground sorts:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Background operators:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Foreground operators:
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.29  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.17/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.17/1.29  
% 2.42/1.31  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.42/1.31  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.42/1.31  tff(f_50, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 2.42/1.31  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.42/1.31  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.42/1.31  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 2.42/1.31  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.42/1.31  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 2.42/1.31  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.42/1.31  tff(f_67, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.42/1.31  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.42/1.31  tff(c_8, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.42/1.31  tff(c_18, plain, (![A_15]: (k4_relat_1(k6_relat_1(A_15))=k6_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.42/1.31  tff(c_14, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.42/1.31  tff(c_146, plain, (![A_36, B_37]: (k5_relat_1(k6_relat_1(A_36), B_37)=B_37 | ~r1_tarski(k1_relat_1(B_37), A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.42/1.31  tff(c_149, plain, (![A_36, A_14]: (k5_relat_1(k6_relat_1(A_36), k6_relat_1(A_14))=k6_relat_1(A_14) | ~r1_tarski(A_14, A_36) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_146])).
% 2.42/1.31  tff(c_151, plain, (![A_36, A_14]: (k5_relat_1(k6_relat_1(A_36), k6_relat_1(A_14))=k6_relat_1(A_14) | ~r1_tarski(A_14, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_149])).
% 2.42/1.31  tff(c_264, plain, (![B_47, A_48]: (k5_relat_1(k4_relat_1(B_47), k4_relat_1(A_48))=k4_relat_1(k5_relat_1(A_48, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.42/1.31  tff(c_276, plain, (![B_47, A_15]: (k5_relat_1(k4_relat_1(B_47), k6_relat_1(A_15))=k4_relat_1(k5_relat_1(k6_relat_1(A_15), B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_264])).
% 2.42/1.31  tff(c_284, plain, (![B_51, A_52]: (k5_relat_1(k4_relat_1(B_51), k6_relat_1(A_52))=k4_relat_1(k5_relat_1(k6_relat_1(A_52), B_51)) | ~v1_relat_1(B_51))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_276])).
% 2.42/1.31  tff(c_301, plain, (![A_52, A_15]: (k4_relat_1(k5_relat_1(k6_relat_1(A_52), k6_relat_1(A_15)))=k5_relat_1(k6_relat_1(A_15), k6_relat_1(A_52)) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_284])).
% 2.42/1.31  tff(c_345, plain, (![A_54, A_55]: (k4_relat_1(k5_relat_1(k6_relat_1(A_54), k6_relat_1(A_55)))=k5_relat_1(k6_relat_1(A_55), k6_relat_1(A_54)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_301])).
% 2.42/1.31  tff(c_374, plain, (![A_14, A_36]: (k5_relat_1(k6_relat_1(A_14), k6_relat_1(A_36))=k4_relat_1(k6_relat_1(A_14)) | ~r1_tarski(A_14, A_36))), inference(superposition, [status(thm), theory('equality')], [c_151, c_345])).
% 2.42/1.31  tff(c_399, plain, (![A_56, A_57]: (k5_relat_1(k6_relat_1(A_56), k6_relat_1(A_57))=k6_relat_1(A_56) | ~r1_tarski(A_56, A_57))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_374])).
% 2.42/1.31  tff(c_24, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.42/1.31  tff(c_415, plain, (![A_57, A_56]: (k7_relat_1(k6_relat_1(A_57), A_56)=k6_relat_1(A_56) | ~v1_relat_1(k6_relat_1(A_57)) | ~r1_tarski(A_56, A_57))), inference(superposition, [status(thm), theory('equality')], [c_399, c_24])).
% 2.42/1.31  tff(c_461, plain, (![A_58, A_59]: (k7_relat_1(k6_relat_1(A_58), A_59)=k6_relat_1(A_59) | ~r1_tarski(A_59, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_415])).
% 2.42/1.31  tff(c_16, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.42/1.31  tff(c_97, plain, (![A_33, B_34]: (k5_relat_1(k6_relat_1(A_33), B_34)=k7_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.42/1.31  tff(c_22, plain, (![A_18]: (k5_relat_1(A_18, k6_relat_1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.42/1.31  tff(c_111, plain, (![A_33]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_33))), A_33)=k6_relat_1(A_33) | ~v1_relat_1(k6_relat_1(A_33)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_33)))))), inference(superposition, [status(thm), theory('equality')], [c_97, c_22])).
% 2.42/1.31  tff(c_128, plain, (![A_33]: (k7_relat_1(k6_relat_1(A_33), A_33)=k6_relat_1(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_16, c_111])).
% 2.42/1.31  tff(c_218, plain, (![C_42, A_43, B_44]: (k7_relat_1(k7_relat_1(C_42, A_43), B_44)=k7_relat_1(C_42, k3_xboole_0(A_43, B_44)) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.31  tff(c_236, plain, (![A_33, B_44]: (k7_relat_1(k6_relat_1(A_33), k3_xboole_0(A_33, B_44))=k7_relat_1(k6_relat_1(A_33), B_44) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_218])).
% 2.42/1.31  tff(c_242, plain, (![A_33, B_44]: (k7_relat_1(k6_relat_1(A_33), k3_xboole_0(A_33, B_44))=k7_relat_1(k6_relat_1(A_33), B_44))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_236])).
% 2.42/1.31  tff(c_468, plain, (![A_58, B_44]: (k7_relat_1(k6_relat_1(A_58), B_44)=k6_relat_1(k3_xboole_0(A_58, B_44)) | ~r1_tarski(k3_xboole_0(A_58, B_44), A_58))), inference(superposition, [status(thm), theory('equality')], [c_461, c_242])).
% 2.42/1.31  tff(c_496, plain, (![A_58, B_44]: (k7_relat_1(k6_relat_1(A_58), B_44)=k6_relat_1(k3_xboole_0(A_58, B_44)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_468])).
% 2.42/1.31  tff(c_26, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.42/1.31  tff(c_103, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_26])).
% 2.42/1.31  tff(c_124, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_103])).
% 2.42/1.31  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_496, c_124])).
% 2.42/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.31  
% 2.42/1.31  Inference rules
% 2.42/1.31  ----------------------
% 2.42/1.31  #Ref     : 0
% 2.42/1.31  #Sup     : 104
% 2.42/1.31  #Fact    : 0
% 2.42/1.31  #Define  : 0
% 2.42/1.31  #Split   : 1
% 2.42/1.31  #Chain   : 0
% 2.42/1.31  #Close   : 0
% 2.42/1.31  
% 2.42/1.31  Ordering : KBO
% 2.42/1.31  
% 2.42/1.31  Simplification rules
% 2.42/1.31  ----------------------
% 2.42/1.31  #Subsume      : 4
% 2.42/1.31  #Demod        : 88
% 2.42/1.31  #Tautology    : 60
% 2.42/1.31  #SimpNegUnit  : 0
% 2.42/1.31  #BackRed      : 5
% 2.42/1.31  
% 2.42/1.31  #Partial instantiations: 0
% 2.42/1.31  #Strategies tried      : 1
% 2.42/1.31  
% 2.42/1.31  Timing (in seconds)
% 2.42/1.31  ----------------------
% 2.42/1.31  Preprocessing        : 0.29
% 2.42/1.31  Parsing              : 0.16
% 2.42/1.31  CNF conversion       : 0.02
% 2.42/1.31  Main loop            : 0.25
% 2.42/1.31  Inferencing          : 0.10
% 2.42/1.31  Reduction            : 0.08
% 2.42/1.31  Demodulation         : 0.06
% 2.42/1.31  BG Simplification    : 0.02
% 2.42/1.31  Subsumption          : 0.03
% 2.42/1.31  Abstraction          : 0.02
% 2.42/1.31  MUC search           : 0.00
% 2.42/1.31  Cooper               : 0.00
% 2.42/1.31  Total                : 0.57
% 2.42/1.31  Index Insertion      : 0.00
% 2.42/1.31  Index Deletion       : 0.00
% 2.42/1.31  Index Matching       : 0.00
% 2.42/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
