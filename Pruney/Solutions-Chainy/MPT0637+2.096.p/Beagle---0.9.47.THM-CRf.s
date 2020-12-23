%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:37 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   44 (  57 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  67 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    ! [B_29,A_30] :
      ( k5_relat_1(B_29,k6_relat_1(A_30)) = k8_relat_1(A_30,B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [A_30,A_14] :
      ( k8_relat_1(A_30,k6_relat_1(A_14)) = k7_relat_1(k6_relat_1(A_30),A_14)
      | ~ v1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_78])).

tff(c_103,plain,(
    ! [A_30,A_14] : k8_relat_1(A_30,k6_relat_1(A_14)) = k7_relat_1(k6_relat_1(A_30),A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_95])).

tff(c_16,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_115,plain,(
    ! [A_33,B_34] :
      ( k8_relat_1(A_33,B_34) = B_34
      | ~ r1_tarski(k2_relat_1(B_34),A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [A_33,A_13] :
      ( k8_relat_1(A_33,k6_relat_1(A_13)) = k6_relat_1(A_13)
      | ~ r1_tarski(A_13,A_33)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_135,plain,(
    ! [A_37,A_38] :
      ( k7_relat_1(k6_relat_1(A_37),A_38) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_103,c_118])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,k3_xboole_0(k1_relat_1(B_12),A_11)) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_142,plain,(
    ! [A_37,A_11] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_37)),A_11)) = k7_relat_1(k6_relat_1(A_37),A_11)
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_37)),A_11),A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_12])).

tff(c_155,plain,(
    ! [A_37,A_11] : k7_relat_1(k6_relat_1(A_37),A_11) = k6_relat_1(k3_xboole_0(A_37,A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14,c_20,c_14,c_142])).

tff(c_24,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_75,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_24])).

tff(c_77,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_75])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.29  
% 1.87/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.29  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.87/1.29  
% 1.87/1.29  %Foreground sorts:
% 1.87/1.29  
% 1.87/1.29  
% 1.87/1.29  %Background operators:
% 1.87/1.29  
% 1.87/1.29  
% 1.87/1.29  %Foreground operators:
% 1.87/1.29  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.87/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.87/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.87/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.87/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.87/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.87/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.87/1.29  
% 1.87/1.30  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.87/1.30  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.87/1.30  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.87/1.30  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.87/1.30  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.87/1.30  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.87/1.30  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 1.87/1.30  tff(f_60, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.87/1.30  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.30  tff(c_14, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.30  tff(c_20, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.87/1.30  tff(c_18, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.87/1.30  tff(c_78, plain, (![B_29, A_30]: (k5_relat_1(B_29, k6_relat_1(A_30))=k8_relat_1(A_30, B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.30  tff(c_95, plain, (![A_30, A_14]: (k8_relat_1(A_30, k6_relat_1(A_14))=k7_relat_1(k6_relat_1(A_30), A_14) | ~v1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_78])).
% 1.87/1.30  tff(c_103, plain, (![A_30, A_14]: (k8_relat_1(A_30, k6_relat_1(A_14))=k7_relat_1(k6_relat_1(A_30), A_14))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_95])).
% 1.87/1.30  tff(c_16, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.30  tff(c_115, plain, (![A_33, B_34]: (k8_relat_1(A_33, B_34)=B_34 | ~r1_tarski(k2_relat_1(B_34), A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.30  tff(c_118, plain, (![A_33, A_13]: (k8_relat_1(A_33, k6_relat_1(A_13))=k6_relat_1(A_13) | ~r1_tarski(A_13, A_33) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_115])).
% 1.87/1.30  tff(c_135, plain, (![A_37, A_38]: (k7_relat_1(k6_relat_1(A_37), A_38)=k6_relat_1(A_38) | ~r1_tarski(A_38, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_103, c_118])).
% 1.87/1.30  tff(c_12, plain, (![B_12, A_11]: (k7_relat_1(B_12, k3_xboole_0(k1_relat_1(B_12), A_11))=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.87/1.30  tff(c_142, plain, (![A_37, A_11]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_37)), A_11))=k7_relat_1(k6_relat_1(A_37), A_11) | ~v1_relat_1(k6_relat_1(A_37)) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_37)), A_11), A_37))), inference(superposition, [status(thm), theory('equality')], [c_135, c_12])).
% 1.87/1.30  tff(c_155, plain, (![A_37, A_11]: (k7_relat_1(k6_relat_1(A_37), A_11)=k6_relat_1(k3_xboole_0(A_37, A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14, c_20, c_14, c_142])).
% 1.87/1.30  tff(c_24, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.30  tff(c_75, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_24])).
% 1.87/1.30  tff(c_77, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_75])).
% 1.87/1.30  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_77])).
% 1.87/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.30  
% 1.87/1.30  Inference rules
% 1.87/1.30  ----------------------
% 1.87/1.30  #Ref     : 0
% 1.87/1.30  #Sup     : 27
% 1.87/1.30  #Fact    : 0
% 1.87/1.30  #Define  : 0
% 1.87/1.30  #Split   : 0
% 1.87/1.30  #Chain   : 0
% 1.87/1.30  #Close   : 0
% 1.87/1.30  
% 1.87/1.30  Ordering : KBO
% 1.87/1.30  
% 1.87/1.30  Simplification rules
% 1.87/1.30  ----------------------
% 1.87/1.30  #Subsume      : 1
% 1.87/1.30  #Demod        : 22
% 1.87/1.30  #Tautology    : 19
% 1.87/1.30  #SimpNegUnit  : 0
% 1.87/1.30  #BackRed      : 4
% 1.87/1.30  
% 1.87/1.30  #Partial instantiations: 0
% 1.87/1.30  #Strategies tried      : 1
% 1.87/1.30  
% 1.87/1.30  Timing (in seconds)
% 1.87/1.30  ----------------------
% 1.87/1.30  Preprocessing        : 0.32
% 1.87/1.30  Parsing              : 0.18
% 1.87/1.30  CNF conversion       : 0.02
% 1.87/1.31  Main loop            : 0.12
% 1.87/1.31  Inferencing          : 0.05
% 1.87/1.31  Reduction            : 0.04
% 1.87/1.31  Demodulation         : 0.03
% 1.87/1.31  BG Simplification    : 0.01
% 1.87/1.31  Subsumption          : 0.02
% 1.87/1.31  Abstraction          : 0.01
% 1.87/1.31  MUC search           : 0.00
% 1.87/1.31  Cooper               : 0.00
% 1.87/1.31  Total                : 0.47
% 1.87/1.31  Index Insertion      : 0.00
% 1.87/1.31  Index Deletion       : 0.00
% 1.87/1.31  Index Matching       : 0.00
% 1.87/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
