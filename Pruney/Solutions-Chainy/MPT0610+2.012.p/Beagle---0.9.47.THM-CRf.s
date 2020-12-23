%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:38 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   46 (  56 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 (  88 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_67,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k3_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_75,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_67,c_24])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_91])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_102,plain,(
    k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_91])).

tff(c_231,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_42,B_43)),k3_xboole_0(k1_relat_1(A_42),k1_relat_1(B_43)))
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_240,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0)
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_231])).

tff(c_246,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_240])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_252,plain,(
    k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_246,c_8])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = A_24
      | k3_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_67,c_12])).

tff(c_259,plain,
    ( k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_74])).

tff(c_273,plain,(
    k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_259])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k3_xboole_0(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_8,B_9] :
      ( k1_relat_1(k3_xboole_0(A_8,B_9)) != k1_xboole_0
      | k3_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_34])).

tff(c_292,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_44])).

tff(c_300,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_292])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.36  
% 2.02/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.36  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.02/1.36  
% 2.02/1.36  %Foreground sorts:
% 2.02/1.36  
% 2.02/1.36  
% 2.02/1.36  %Background operators:
% 2.02/1.36  
% 2.02/1.36  
% 2.02/1.36  %Foreground operators:
% 2.02/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.36  
% 2.02/1.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.02/1.37  tff(f_68, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 2.02/1.37  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.02/1.37  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 2.02/1.37  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.02/1.37  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.02/1.37  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.02/1.37  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.02/1.37  tff(c_67, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k3_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.37  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.02/1.37  tff(c_75, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_67, c_24])).
% 2.02/1.37  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.02/1.37  tff(c_10, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.37  tff(c_91, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.37  tff(c_103, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_91])).
% 2.02/1.37  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.02/1.37  tff(c_26, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.02/1.37  tff(c_102, plain, (k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_91])).
% 2.02/1.37  tff(c_231, plain, (![A_42, B_43]: (r1_tarski(k1_relat_1(k3_xboole_0(A_42, B_43)), k3_xboole_0(k1_relat_1(A_42), k1_relat_1(B_43))) | ~v1_relat_1(B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.02/1.37  tff(c_240, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_102, c_231])).
% 2.02/1.37  tff(c_246, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_240])).
% 2.02/1.37  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.37  tff(c_252, plain, (k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_246, c_8])).
% 2.02/1.37  tff(c_12, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.37  tff(c_74, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=A_24 | k3_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_67, c_12])).
% 2.02/1.37  tff(c_259, plain, (k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_252, c_74])).
% 2.02/1.37  tff(c_273, plain, (k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_103, c_259])).
% 2.02/1.37  tff(c_16, plain, (![A_8, B_9]: (v1_relat_1(k3_xboole_0(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.37  tff(c_34, plain, (![A_20]: (k1_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.02/1.37  tff(c_44, plain, (![A_8, B_9]: (k1_relat_1(k3_xboole_0(A_8, B_9))!=k1_xboole_0 | k3_xboole_0(A_8, B_9)=k1_xboole_0 | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_16, c_34])).
% 2.02/1.37  tff(c_292, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_273, c_44])).
% 2.02/1.37  tff(c_300, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_292])).
% 2.02/1.37  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_300])).
% 2.02/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.37  
% 2.02/1.37  Inference rules
% 2.02/1.37  ----------------------
% 2.02/1.37  #Ref     : 0
% 2.02/1.37  #Sup     : 61
% 2.02/1.37  #Fact    : 0
% 2.02/1.37  #Define  : 0
% 2.02/1.37  #Split   : 5
% 2.02/1.37  #Chain   : 0
% 2.02/1.37  #Close   : 0
% 2.02/1.37  
% 2.02/1.37  Ordering : KBO
% 2.02/1.37  
% 2.02/1.37  Simplification rules
% 2.02/1.37  ----------------------
% 2.02/1.37  #Subsume      : 4
% 2.02/1.37  #Demod        : 25
% 2.02/1.37  #Tautology    : 32
% 2.02/1.37  #SimpNegUnit  : 4
% 2.02/1.37  #BackRed      : 4
% 2.02/1.37  
% 2.02/1.37  #Partial instantiations: 0
% 2.02/1.37  #Strategies tried      : 1
% 2.02/1.37  
% 2.02/1.37  Timing (in seconds)
% 2.02/1.37  ----------------------
% 2.02/1.37  Preprocessing        : 0.35
% 2.02/1.37  Parsing              : 0.20
% 2.02/1.37  CNF conversion       : 0.02
% 2.02/1.37  Main loop            : 0.20
% 2.02/1.37  Inferencing          : 0.07
% 2.02/1.37  Reduction            : 0.06
% 2.02/1.37  Demodulation         : 0.04
% 2.02/1.37  BG Simplification    : 0.01
% 2.02/1.37  Subsumption          : 0.03
% 2.02/1.37  Abstraction          : 0.01
% 2.02/1.37  MUC search           : 0.00
% 2.02/1.37  Cooper               : 0.00
% 2.02/1.37  Total                : 0.57
% 2.02/1.37  Index Insertion      : 0.00
% 2.02/1.37  Index Deletion       : 0.00
% 2.02/1.37  Index Matching       : 0.00
% 2.02/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
