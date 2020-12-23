%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:37 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   47 (  54 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 (  83 expanded)
%              Number of equality atoms :   27 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_109,plain,(
    ! [A_31,B_32] :
      ( r1_xboole_0(A_31,B_32)
      | k3_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_117,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_28])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_81,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_81])).

tff(c_235,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_43,B_44)),k3_xboole_0(k1_relat_1(A_43),k1_relat_1(B_44)))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_244,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0)
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_235])).

tff(c_250,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_244])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_256,plain,(
    k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_250,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = A_34
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_137])).

tff(c_263,plain,
    ( k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_147])).

tff(c_277,plain,(
    k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_263])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k3_xboole_0(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    ! [A_33] :
      ( k1_relat_1(A_33) != k1_xboole_0
      | k1_xboole_0 = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_327,plain,(
    ! [A_48,B_49] :
      ( k1_relat_1(k3_xboole_0(A_48,B_49)) != k1_xboole_0
      | k3_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_20,c_118])).

tff(c_330,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_327])).

tff(c_339,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_330])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.30  
% 1.96/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.30  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.96/1.30  
% 1.96/1.30  %Foreground sorts:
% 1.96/1.30  
% 1.96/1.30  
% 1.96/1.30  %Background operators:
% 1.96/1.30  
% 1.96/1.30  
% 1.96/1.30  %Foreground operators:
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.30  
% 2.30/1.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.30/1.32  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 2.30/1.32  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.30/1.32  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relat_1)).
% 2.30/1.32  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.30/1.32  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.30/1.32  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.30/1.32  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.30/1.32  tff(c_109, plain, (![A_31, B_32]: (r1_xboole_0(A_31, B_32) | k3_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.32  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.32  tff(c_117, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_28])).
% 2.30/1.32  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.32  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.32  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.32  tff(c_30, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.32  tff(c_81, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.32  tff(c_85, plain, (k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_81])).
% 2.30/1.32  tff(c_235, plain, (![A_43, B_44]: (r1_tarski(k1_relat_1(k3_xboole_0(A_43, B_44)), k3_xboole_0(k1_relat_1(A_43), k1_relat_1(B_44))) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.30/1.32  tff(c_244, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_85, c_235])).
% 2.30/1.32  tff(c_250, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_244])).
% 2.30/1.32  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.32  tff(c_256, plain, (k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_250, c_8])).
% 2.30/1.32  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.32  tff(c_137, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=A_34 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.32  tff(c_147, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_137])).
% 2.30/1.32  tff(c_263, plain, (k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_256, c_147])).
% 2.30/1.32  tff(c_277, plain, (k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_263])).
% 2.30/1.32  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k3_xboole_0(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.32  tff(c_118, plain, (![A_33]: (k1_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.30/1.32  tff(c_327, plain, (![A_48, B_49]: (k1_relat_1(k3_xboole_0(A_48, B_49))!=k1_xboole_0 | k3_xboole_0(A_48, B_49)=k1_xboole_0 | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_20, c_118])).
% 2.30/1.32  tff(c_330, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_277, c_327])).
% 2.30/1.32  tff(c_339, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_330])).
% 2.30/1.32  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_339])).
% 2.30/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.32  
% 2.30/1.32  Inference rules
% 2.30/1.32  ----------------------
% 2.30/1.32  #Ref     : 0
% 2.30/1.32  #Sup     : 68
% 2.30/1.32  #Fact    : 0
% 2.30/1.32  #Define  : 0
% 2.30/1.32  #Split   : 6
% 2.30/1.32  #Chain   : 0
% 2.30/1.32  #Close   : 0
% 2.30/1.32  
% 2.30/1.32  Ordering : KBO
% 2.30/1.32  
% 2.30/1.32  Simplification rules
% 2.30/1.32  ----------------------
% 2.30/1.32  #Subsume      : 3
% 2.30/1.32  #Demod        : 31
% 2.30/1.32  #Tautology    : 40
% 2.30/1.32  #SimpNegUnit  : 4
% 2.30/1.32  #BackRed      : 4
% 2.30/1.32  
% 2.30/1.32  #Partial instantiations: 0
% 2.30/1.32  #Strategies tried      : 1
% 2.30/1.32  
% 2.30/1.32  Timing (in seconds)
% 2.30/1.32  ----------------------
% 2.30/1.32  Preprocessing        : 0.29
% 2.30/1.32  Parsing              : 0.16
% 2.30/1.32  CNF conversion       : 0.02
% 2.30/1.32  Main loop            : 0.25
% 2.30/1.32  Inferencing          : 0.10
% 2.30/1.32  Reduction            : 0.07
% 2.30/1.32  Demodulation         : 0.05
% 2.30/1.32  BG Simplification    : 0.01
% 2.30/1.32  Subsumption          : 0.04
% 2.30/1.32  Abstraction          : 0.01
% 2.30/1.32  MUC search           : 0.00
% 2.30/1.32  Cooper               : 0.00
% 2.30/1.32  Total                : 0.56
% 2.30/1.32  Index Insertion      : 0.00
% 2.30/1.32  Index Deletion       : 0.00
% 2.30/1.32  Index Matching       : 0.00
% 2.30/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
