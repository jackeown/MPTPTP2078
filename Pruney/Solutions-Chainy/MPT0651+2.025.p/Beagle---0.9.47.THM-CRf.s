%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:51 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 144 expanded)
%              Number of leaves         :   22 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 354 expanded)
%              Number of equality atoms :   35 ( 122 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_5] :
      ( k10_relat_1(A_5,k2_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_99,plain,(
    ! [A_22] :
      ( k4_relat_1(A_22) = k2_funct_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_102,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_99])).

tff(c_105,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_102])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_2])).

tff(c_128,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_118])).

tff(c_14,plain,(
    ! [A_9] :
      ( k1_relat_1(k4_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_109,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_14])).

tff(c_122,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_109])).

tff(c_10,plain,(
    ! [A_6,B_8] :
      ( k10_relat_1(A_6,k1_relat_1(B_8)) = k1_relat_1(k5_relat_1(A_6,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_172,plain,(
    ! [A_6] :
      ( k1_relat_1(k5_relat_1(A_6,k2_funct_1('#skF_1'))) = k10_relat_1(A_6,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_10])).

tff(c_279,plain,(
    ! [A_28] :
      ( k1_relat_1(k5_relat_1(A_28,k2_funct_1('#skF_1'))) = k10_relat_1(A_28,k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_172])).

tff(c_20,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_91,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_297,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_91])).

tff(c_306,plain,(
    k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_297])).

tff(c_310,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_306])).

tff(c_314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_310])).

tff(c_315,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_339,plain,(
    ! [A_30] :
      ( k4_relat_1(A_30) = k2_funct_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_342,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_339])).

tff(c_345,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_342])).

tff(c_376,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_2])).

tff(c_386,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_376])).

tff(c_12,plain,(
    ! [A_9] :
      ( k2_relat_1(k4_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_370,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_12])).

tff(c_382,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_370])).

tff(c_76,plain,(
    ! [A_20] :
      ( k10_relat_1(A_20,k2_relat_1(A_20)) = k1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k10_relat_1(B_4,A_3),k1_relat_1(B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_324,plain,(
    ! [A_29] :
      ( r1_tarski(k1_relat_1(A_29),k1_relat_1(A_29))
      | ~ v1_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_6])).

tff(c_745,plain,(
    ! [A_45] :
      ( r1_tarski(k1_relat_1(k4_relat_1(A_45)),k2_relat_1(A_45))
      | ~ v1_relat_1(k4_relat_1(A_45))
      | ~ v1_relat_1(k4_relat_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_324])).

tff(c_16,plain,(
    ! [B_12,A_10] :
      ( k2_relat_1(k5_relat_1(B_12,A_10)) = k2_relat_1(A_10)
      | ~ r1_tarski(k1_relat_1(A_10),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_774,plain,(
    ! [A_46] :
      ( k2_relat_1(k5_relat_1(A_46,k4_relat_1(A_46))) = k2_relat_1(k4_relat_1(A_46))
      | ~ v1_relat_1(k4_relat_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_745,c_16])).

tff(c_798,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1(k4_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_774])).

tff(c_807,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_386,c_345,c_382,c_345,c_798])).

tff(c_809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:50:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  
% 2.78/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.78/1.40  
% 2.78/1.40  %Foreground sorts:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Background operators:
% 2.78/1.40  
% 2.78/1.40  
% 2.78/1.40  %Foreground operators:
% 2.78/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.40  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.78/1.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.78/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.78/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.40  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.78/1.40  
% 2.78/1.42  tff(f_82, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 2.78/1.42  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.78/1.42  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.78/1.42  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.78/1.42  tff(f_54, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.78/1.42  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.78/1.42  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.78/1.42  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.78/1.42  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.78/1.42  tff(c_8, plain, (![A_5]: (k10_relat_1(A_5, k2_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.42  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.78/1.42  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.78/1.42  tff(c_99, plain, (![A_22]: (k4_relat_1(A_22)=k2_funct_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.42  tff(c_102, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_99])).
% 2.78/1.42  tff(c_105, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_102])).
% 2.78/1.42  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.78/1.42  tff(c_118, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_105, c_2])).
% 2.78/1.42  tff(c_128, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_118])).
% 2.78/1.42  tff(c_14, plain, (![A_9]: (k1_relat_1(k4_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.78/1.42  tff(c_109, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_105, c_14])).
% 2.78/1.42  tff(c_122, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_109])).
% 2.78/1.42  tff(c_10, plain, (![A_6, B_8]: (k10_relat_1(A_6, k1_relat_1(B_8))=k1_relat_1(k5_relat_1(A_6, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.78/1.42  tff(c_172, plain, (![A_6]: (k1_relat_1(k5_relat_1(A_6, k2_funct_1('#skF_1')))=k10_relat_1(A_6, k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_122, c_10])).
% 2.78/1.42  tff(c_279, plain, (![A_28]: (k1_relat_1(k5_relat_1(A_28, k2_funct_1('#skF_1')))=k10_relat_1(A_28, k2_relat_1('#skF_1')) | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_172])).
% 2.78/1.42  tff(c_20, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.78/1.42  tff(c_91, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 2.78/1.42  tff(c_297, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_279, c_91])).
% 2.78/1.42  tff(c_306, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_297])).
% 2.78/1.42  tff(c_310, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_306])).
% 2.78/1.42  tff(c_314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_310])).
% 2.78/1.42  tff(c_315, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 2.78/1.42  tff(c_339, plain, (![A_30]: (k4_relat_1(A_30)=k2_funct_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.42  tff(c_342, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_339])).
% 2.78/1.42  tff(c_345, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_342])).
% 2.78/1.42  tff(c_376, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_345, c_2])).
% 2.78/1.42  tff(c_386, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_376])).
% 2.78/1.42  tff(c_12, plain, (![A_9]: (k2_relat_1(k4_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.78/1.42  tff(c_370, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_345, c_12])).
% 2.78/1.42  tff(c_382, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_370])).
% 2.78/1.42  tff(c_76, plain, (![A_20]: (k10_relat_1(A_20, k2_relat_1(A_20))=k1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.42  tff(c_6, plain, (![B_4, A_3]: (r1_tarski(k10_relat_1(B_4, A_3), k1_relat_1(B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.42  tff(c_324, plain, (![A_29]: (r1_tarski(k1_relat_1(A_29), k1_relat_1(A_29)) | ~v1_relat_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_76, c_6])).
% 2.78/1.42  tff(c_745, plain, (![A_45]: (r1_tarski(k1_relat_1(k4_relat_1(A_45)), k2_relat_1(A_45)) | ~v1_relat_1(k4_relat_1(A_45)) | ~v1_relat_1(k4_relat_1(A_45)) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_14, c_324])).
% 2.78/1.42  tff(c_16, plain, (![B_12, A_10]: (k2_relat_1(k5_relat_1(B_12, A_10))=k2_relat_1(A_10) | ~r1_tarski(k1_relat_1(A_10), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.78/1.42  tff(c_774, plain, (![A_46]: (k2_relat_1(k5_relat_1(A_46, k4_relat_1(A_46)))=k2_relat_1(k4_relat_1(A_46)) | ~v1_relat_1(k4_relat_1(A_46)) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_745, c_16])).
% 2.78/1.42  tff(c_798, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1(k4_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_345, c_774])).
% 2.78/1.42  tff(c_807, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_386, c_345, c_382, c_345, c_798])).
% 2.78/1.42  tff(c_809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_315, c_807])).
% 2.78/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  Inference rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Ref     : 0
% 2.78/1.42  #Sup     : 193
% 2.78/1.42  #Fact    : 0
% 2.78/1.42  #Define  : 0
% 2.78/1.42  #Split   : 2
% 2.78/1.42  #Chain   : 0
% 2.78/1.42  #Close   : 0
% 2.78/1.42  
% 2.78/1.42  Ordering : KBO
% 2.78/1.42  
% 2.78/1.42  Simplification rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Subsume      : 11
% 2.78/1.42  #Demod        : 189
% 2.78/1.42  #Tautology    : 92
% 2.78/1.42  #SimpNegUnit  : 1
% 2.78/1.42  #BackRed      : 0
% 2.78/1.42  
% 2.78/1.42  #Partial instantiations: 0
% 2.78/1.42  #Strategies tried      : 1
% 2.78/1.42  
% 2.78/1.42  Timing (in seconds)
% 2.78/1.42  ----------------------
% 2.78/1.42  Preprocessing        : 0.30
% 2.78/1.42  Parsing              : 0.16
% 2.78/1.42  CNF conversion       : 0.02
% 2.78/1.42  Main loop            : 0.35
% 2.78/1.42  Inferencing          : 0.13
% 2.78/1.42  Reduction            : 0.12
% 2.78/1.42  Demodulation         : 0.09
% 2.78/1.42  BG Simplification    : 0.02
% 2.78/1.42  Subsumption          : 0.06
% 2.78/1.42  Abstraction          : 0.02
% 2.78/1.42  MUC search           : 0.00
% 2.78/1.42  Cooper               : 0.00
% 2.78/1.42  Total                : 0.69
% 2.78/1.42  Index Insertion      : 0.00
% 2.78/1.42  Index Deletion       : 0.00
% 2.78/1.42  Index Matching       : 0.00
% 2.78/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
