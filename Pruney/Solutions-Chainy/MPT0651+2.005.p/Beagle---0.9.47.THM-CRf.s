%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:48 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 121 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 292 expanded)
%              Number of equality atoms :   33 ( 103 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
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
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_20,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    ! [A_18] :
      ( k4_relat_1(A_18) = k2_funct_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_55])).

tff(c_61,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_58])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_8])).

tff(c_80,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_72])).

tff(c_12,plain,(
    ! [A_4] :
      ( k1_relat_1(k4_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_12])).

tff(c_76,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66])).

tff(c_162,plain,(
    ! [A_23,B_24] :
      ( k1_relat_1(k5_relat_1(A_23,B_24)) = k1_relat_1(A_23)
      | ~ r1_tarski(k2_relat_1(A_23),k1_relat_1(B_24))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_171,plain,(
    ! [A_23] :
      ( k1_relat_1(k5_relat_1(A_23,k2_funct_1('#skF_1'))) = k1_relat_1(A_23)
      | ~ r1_tarski(k2_relat_1(A_23),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_162])).

tff(c_185,plain,(
    ! [A_25] :
      ( k1_relat_1(k5_relat_1(A_25,k2_funct_1('#skF_1'))) = k1_relat_1(A_25)
      | ~ r1_tarski(k2_relat_1(A_25),k2_relat_1('#skF_1'))
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_171])).

tff(c_201,plain,
    ( k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_185])).

tff(c_208,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_201])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_208])).

tff(c_211,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_226,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_8])).

tff(c_234,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_226])).

tff(c_10,plain,(
    ! [A_4] :
      ( k2_relat_1(k4_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_223,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_10])).

tff(c_232,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_223])).

tff(c_220,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_12])).

tff(c_230,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_220])).

tff(c_244,plain,(
    ! [B_26,A_27] :
      ( k2_relat_1(k5_relat_1(B_26,A_27)) = k2_relat_1(A_27)
      | ~ r1_tarski(k1_relat_1(A_27),k2_relat_1(B_26))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_247,plain,(
    ! [B_26] :
      ( k2_relat_1(k5_relat_1(B_26,k2_funct_1('#skF_1'))) = k2_relat_1(k2_funct_1('#skF_1'))
      | ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(B_26))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_244])).

tff(c_264,plain,(
    ! [B_28] :
      ( k2_relat_1(k5_relat_1(B_28,k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
      | ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_232,c_247])).

tff(c_274,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_264])).

tff(c_279,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_274])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:00:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.99/1.22  
% 1.99/1.22  %Foreground sorts:
% 1.99/1.22  
% 1.99/1.22  
% 1.99/1.22  %Background operators:
% 1.99/1.22  
% 1.99/1.22  
% 1.99/1.22  %Foreground operators:
% 1.99/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.22  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.99/1.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.99/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.22  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.99/1.22  
% 2.13/1.23  tff(f_78, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 2.13/1.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.13/1.23  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.13/1.23  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.13/1.23  tff(f_41, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.13/1.23  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.13/1.23  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.13/1.23  tff(c_20, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.23  tff(c_62, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 2.13/1.23  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.23  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.23  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.23  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.23  tff(c_55, plain, (![A_18]: (k4_relat_1(A_18)=k2_funct_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.23  tff(c_58, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_55])).
% 2.13/1.23  tff(c_61, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_58])).
% 2.13/1.23  tff(c_8, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.23  tff(c_72, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_8])).
% 2.13/1.23  tff(c_80, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_72])).
% 2.13/1.23  tff(c_12, plain, (![A_4]: (k1_relat_1(k4_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.23  tff(c_66, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_12])).
% 2.13/1.23  tff(c_76, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_66])).
% 2.13/1.23  tff(c_162, plain, (![A_23, B_24]: (k1_relat_1(k5_relat_1(A_23, B_24))=k1_relat_1(A_23) | ~r1_tarski(k2_relat_1(A_23), k1_relat_1(B_24)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.23  tff(c_171, plain, (![A_23]: (k1_relat_1(k5_relat_1(A_23, k2_funct_1('#skF_1')))=k1_relat_1(A_23) | ~r1_tarski(k2_relat_1(A_23), k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_23))), inference(superposition, [status(thm), theory('equality')], [c_76, c_162])).
% 2.13/1.23  tff(c_185, plain, (![A_25]: (k1_relat_1(k5_relat_1(A_25, k2_funct_1('#skF_1')))=k1_relat_1(A_25) | ~r1_tarski(k2_relat_1(A_25), k2_relat_1('#skF_1')) | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_171])).
% 2.13/1.23  tff(c_201, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_185])).
% 2.13/1.23  tff(c_208, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_201])).
% 2.13/1.23  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_208])).
% 2.13/1.23  tff(c_211, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 2.13/1.23  tff(c_226, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_8])).
% 2.13/1.23  tff(c_234, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_226])).
% 2.13/1.23  tff(c_10, plain, (![A_4]: (k2_relat_1(k4_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.23  tff(c_223, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_10])).
% 2.13/1.23  tff(c_232, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_223])).
% 2.13/1.23  tff(c_220, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_12])).
% 2.13/1.23  tff(c_230, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_220])).
% 2.13/1.23  tff(c_244, plain, (![B_26, A_27]: (k2_relat_1(k5_relat_1(B_26, A_27))=k2_relat_1(A_27) | ~r1_tarski(k1_relat_1(A_27), k2_relat_1(B_26)) | ~v1_relat_1(B_26) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.13/1.23  tff(c_247, plain, (![B_26]: (k2_relat_1(k5_relat_1(B_26, k2_funct_1('#skF_1')))=k2_relat_1(k2_funct_1('#skF_1')) | ~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(B_26)) | ~v1_relat_1(B_26) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_230, c_244])).
% 2.13/1.23  tff(c_264, plain, (![B_28]: (k2_relat_1(k5_relat_1(B_28, k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_232, c_247])).
% 2.13/1.23  tff(c_274, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_264])).
% 2.13/1.23  tff(c_279, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_274])).
% 2.13/1.23  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_279])).
% 2.13/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.23  
% 2.13/1.23  Inference rules
% 2.13/1.23  ----------------------
% 2.13/1.23  #Ref     : 0
% 2.13/1.23  #Sup     : 63
% 2.13/1.23  #Fact    : 0
% 2.13/1.23  #Define  : 0
% 2.13/1.23  #Split   : 2
% 2.13/1.23  #Chain   : 0
% 2.13/1.23  #Close   : 0
% 2.13/1.23  
% 2.13/1.23  Ordering : KBO
% 2.13/1.23  
% 2.13/1.23  Simplification rules
% 2.13/1.23  ----------------------
% 2.13/1.23  #Subsume      : 1
% 2.13/1.23  #Demod        : 31
% 2.13/1.23  #Tautology    : 24
% 2.13/1.23  #SimpNegUnit  : 2
% 2.13/1.23  #BackRed      : 0
% 2.13/1.23  
% 2.13/1.23  #Partial instantiations: 0
% 2.13/1.23  #Strategies tried      : 1
% 2.13/1.23  
% 2.13/1.23  Timing (in seconds)
% 2.13/1.23  ----------------------
% 2.13/1.24  Preprocessing        : 0.29
% 2.15/1.24  Parsing              : 0.15
% 2.15/1.24  CNF conversion       : 0.02
% 2.15/1.24  Main loop            : 0.20
% 2.15/1.24  Inferencing          : 0.07
% 2.15/1.24  Reduction            : 0.06
% 2.15/1.24  Demodulation         : 0.04
% 2.15/1.24  BG Simplification    : 0.01
% 2.15/1.24  Subsumption          : 0.04
% 2.15/1.24  Abstraction          : 0.01
% 2.15/1.24  MUC search           : 0.00
% 2.15/1.24  Cooper               : 0.00
% 2.15/1.24  Total                : 0.51
% 2.15/1.24  Index Insertion      : 0.00
% 2.15/1.24  Index Deletion       : 0.00
% 2.15/1.24  Index Matching       : 0.00
% 2.15/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
