%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:38 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 112 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 ( 202 expanded)
%              Number of equality atoms :   25 (  62 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_54,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_80,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | k3_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_92,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_28])).

tff(c_10,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_62,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_62])).

tff(c_280,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_42,B_43)),k3_xboole_0(k1_relat_1(A_42),k1_relat_1(B_43)))
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_296,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0)
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_280])).

tff(c_304,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_296])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_310,plain,(
    k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_304,c_8])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = A_28
      | k3_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80,c_16])).

tff(c_314,plain,
    ( k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_90])).

tff(c_330,plain,(
    k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_314])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k3_xboole_0(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_13,B_15] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_13,B_15)),k3_xboole_0(k1_relat_1(A_13),k1_relat_1(B_15)))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_344,plain,(
    ! [B_15] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),B_15)),k3_xboole_0(k1_xboole_0,k1_relat_1(B_15)))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_22])).

tff(c_401,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_404,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_401])).

tff(c_408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_404])).

tff(c_410,plain,(
    v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_26,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_413,plain,
    ( k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_410,c_26])).

tff(c_419,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_413])).

tff(c_421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:39:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.33  
% 2.21/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.34  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.21/1.34  
% 2.21/1.34  %Foreground sorts:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Background operators:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Foreground operators:
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.34  
% 2.21/1.35  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.21/1.35  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 2.21/1.35  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.21/1.35  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 2.21/1.35  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.21/1.35  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.21/1.35  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.21/1.35  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.21/1.35  tff(c_80, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | k3_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.35  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.35  tff(c_92, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_28])).
% 2.21/1.35  tff(c_10, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.35  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.35  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.35  tff(c_30, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.35  tff(c_62, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.35  tff(c_66, plain, (k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_62])).
% 2.21/1.35  tff(c_280, plain, (![A_42, B_43]: (r1_tarski(k1_relat_1(k3_xboole_0(A_42, B_43)), k3_xboole_0(k1_relat_1(A_42), k1_relat_1(B_43))) | ~v1_relat_1(B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.35  tff(c_296, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_66, c_280])).
% 2.21/1.35  tff(c_304, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_296])).
% 2.21/1.35  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.35  tff(c_310, plain, (k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_304, c_8])).
% 2.21/1.35  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.35  tff(c_90, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=A_28 | k3_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_16])).
% 2.21/1.35  tff(c_314, plain, (k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_310, c_90])).
% 2.21/1.35  tff(c_330, plain, (k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_314])).
% 2.21/1.35  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k3_xboole_0(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.35  tff(c_22, plain, (![A_13, B_15]: (r1_tarski(k1_relat_1(k3_xboole_0(A_13, B_15)), k3_xboole_0(k1_relat_1(A_13), k1_relat_1(B_15))) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.35  tff(c_344, plain, (![B_15]: (r1_tarski(k1_relat_1(k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), B_15)), k3_xboole_0(k1_xboole_0, k1_relat_1(B_15))) | ~v1_relat_1(B_15) | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_330, c_22])).
% 2.21/1.35  tff(c_401, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_344])).
% 2.21/1.35  tff(c_404, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_401])).
% 2.21/1.35  tff(c_408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_404])).
% 2.21/1.35  tff(c_410, plain, (v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_344])).
% 2.21/1.35  tff(c_26, plain, (![A_16]: (k1_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.21/1.35  tff(c_413, plain, (k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_410, c_26])).
% 2.21/1.35  tff(c_419, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_330, c_413])).
% 2.21/1.35  tff(c_421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_419])).
% 2.21/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  Inference rules
% 2.21/1.35  ----------------------
% 2.21/1.35  #Ref     : 0
% 2.21/1.35  #Sup     : 86
% 2.21/1.35  #Fact    : 0
% 2.21/1.35  #Define  : 0
% 2.21/1.35  #Split   : 7
% 2.21/1.35  #Chain   : 0
% 2.21/1.35  #Close   : 0
% 2.21/1.35  
% 2.21/1.35  Ordering : KBO
% 2.21/1.35  
% 2.21/1.35  Simplification rules
% 2.21/1.35  ----------------------
% 2.21/1.35  #Subsume      : 2
% 2.21/1.35  #Demod        : 44
% 2.21/1.35  #Tautology    : 53
% 2.21/1.35  #SimpNegUnit  : 4
% 2.21/1.35  #BackRed      : 4
% 2.21/1.35  
% 2.21/1.35  #Partial instantiations: 0
% 2.21/1.35  #Strategies tried      : 1
% 2.21/1.35  
% 2.21/1.35  Timing (in seconds)
% 2.21/1.35  ----------------------
% 2.21/1.35  Preprocessing        : 0.31
% 2.21/1.35  Parsing              : 0.17
% 2.21/1.35  CNF conversion       : 0.02
% 2.21/1.35  Main loop            : 0.26
% 2.21/1.35  Inferencing          : 0.10
% 2.21/1.35  Reduction            : 0.08
% 2.21/1.35  Demodulation         : 0.05
% 2.21/1.35  BG Simplification    : 0.01
% 2.21/1.35  Subsumption          : 0.05
% 2.21/1.35  Abstraction          : 0.01
% 2.21/1.35  MUC search           : 0.00
% 2.21/1.35  Cooper               : 0.00
% 2.21/1.35  Total                : 0.60
% 2.21/1.35  Index Insertion      : 0.00
% 2.21/1.35  Index Deletion       : 0.00
% 2.21/1.35  Index Matching       : 0.00
% 2.21/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
