%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:38 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 112 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 ( 185 expanded)
%              Number of equality atoms :   25 (  55 expanded)
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

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_86,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_90,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_28])).

tff(c_12,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

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

tff(c_109,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_109])).

tff(c_244,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_42,B_43)),k3_xboole_0(k1_relat_1(A_42),k1_relat_1(B_43)))
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_260,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0)
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_244])).

tff(c_268,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_260])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_274,plain,(
    k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_8])).

tff(c_14,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_278,plain,(
    k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) = k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_14])).

tff(c_290,plain,(
    k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_278])).

tff(c_138,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k4_xboole_0(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_147,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k3_xboole_0(A_36,B_37))
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_20])).

tff(c_22,plain,(
    ! [A_13,B_15] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_13,B_15)),k3_xboole_0(k1_relat_1(A_13),k1_relat_1(B_15)))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_302,plain,(
    ! [B_15] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),B_15)),k3_xboole_0(k1_xboole_0,k1_relat_1(B_15)))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_22])).

tff(c_418,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_421,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_147,c_418])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_421])).

tff(c_427,plain,(
    v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_26,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_430,plain,
    ( k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_427,c_26])).

tff(c_436,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_430])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.10/1.29  
% 2.10/1.29  %Foreground sorts:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Background operators:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Foreground operators:
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.29  
% 2.10/1.30  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.10/1.30  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 2.10/1.30  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.10/1.30  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.10/1.30  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 2.10/1.30  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.10/1.30  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.10/1.30  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.10/1.30  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.10/1.30  tff(c_86, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.30  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.10/1.30  tff(c_90, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_28])).
% 2.10/1.30  tff(c_12, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.30  tff(c_10, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.30  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.10/1.30  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.10/1.30  tff(c_30, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.10/1.30  tff(c_109, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.30  tff(c_121, plain, (k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_109])).
% 2.10/1.30  tff(c_244, plain, (![A_42, B_43]: (r1_tarski(k1_relat_1(k3_xboole_0(A_42, B_43)), k3_xboole_0(k1_relat_1(A_42), k1_relat_1(B_43))) | ~v1_relat_1(B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.10/1.30  tff(c_260, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_121, c_244])).
% 2.10/1.30  tff(c_268, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_260])).
% 2.10/1.30  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.30  tff(c_274, plain, (k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_268, c_8])).
% 2.10/1.30  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.30  tff(c_278, plain, (k4_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)=k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_274, c_14])).
% 2.10/1.30  tff(c_290, plain, (k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_278])).
% 2.10/1.30  tff(c_138, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.30  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k4_xboole_0(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.30  tff(c_147, plain, (![A_36, B_37]: (v1_relat_1(k3_xboole_0(A_36, B_37)) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_138, c_20])).
% 2.10/1.30  tff(c_22, plain, (![A_13, B_15]: (r1_tarski(k1_relat_1(k3_xboole_0(A_13, B_15)), k3_xboole_0(k1_relat_1(A_13), k1_relat_1(B_15))) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.10/1.30  tff(c_302, plain, (![B_15]: (r1_tarski(k1_relat_1(k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), B_15)), k3_xboole_0(k1_xboole_0, k1_relat_1(B_15))) | ~v1_relat_1(B_15) | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_290, c_22])).
% 2.10/1.30  tff(c_418, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_302])).
% 2.10/1.30  tff(c_421, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_147, c_418])).
% 2.10/1.30  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_421])).
% 2.10/1.30  tff(c_427, plain, (v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_302])).
% 2.10/1.30  tff(c_26, plain, (![A_16]: (k1_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.10/1.30  tff(c_430, plain, (k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_427, c_26])).
% 2.10/1.30  tff(c_436, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_290, c_430])).
% 2.10/1.30  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_436])).
% 2.10/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.30  
% 2.10/1.30  Inference rules
% 2.10/1.30  ----------------------
% 2.10/1.30  #Ref     : 0
% 2.10/1.30  #Sup     : 92
% 2.10/1.30  #Fact    : 0
% 2.10/1.30  #Define  : 0
% 2.10/1.30  #Split   : 7
% 2.10/1.30  #Chain   : 0
% 2.10/1.30  #Close   : 0
% 2.10/1.30  
% 2.10/1.30  Ordering : KBO
% 2.10/1.30  
% 2.10/1.30  Simplification rules
% 2.10/1.30  ----------------------
% 2.10/1.30  #Subsume      : 5
% 2.10/1.30  #Demod        : 42
% 2.10/1.30  #Tautology    : 56
% 2.10/1.30  #SimpNegUnit  : 4
% 2.10/1.30  #BackRed      : 4
% 2.10/1.30  
% 2.10/1.30  #Partial instantiations: 0
% 2.10/1.30  #Strategies tried      : 1
% 2.10/1.31  
% 2.10/1.31  Timing (in seconds)
% 2.10/1.31  ----------------------
% 2.39/1.31  Preprocessing        : 0.29
% 2.39/1.31  Parsing              : 0.16
% 2.39/1.31  CNF conversion       : 0.02
% 2.39/1.31  Main loop            : 0.25
% 2.39/1.31  Inferencing          : 0.09
% 2.39/1.31  Reduction            : 0.08
% 2.39/1.31  Demodulation         : 0.06
% 2.39/1.31  BG Simplification    : 0.01
% 2.39/1.31  Subsumption          : 0.04
% 2.39/1.31  Abstraction          : 0.01
% 2.39/1.31  MUC search           : 0.00
% 2.39/1.31  Cooper               : 0.00
% 2.39/1.31  Total                : 0.57
% 2.39/1.31  Index Insertion      : 0.00
% 2.39/1.31  Index Deletion       : 0.00
% 2.39/1.31  Index Matching       : 0.00
% 2.39/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
