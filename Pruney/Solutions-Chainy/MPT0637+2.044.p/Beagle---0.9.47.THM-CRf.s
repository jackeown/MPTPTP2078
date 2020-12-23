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
% DateTime   : Thu Dec  3 10:03:29 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  67 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_18,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    ! [B_35,A_36] :
      ( k7_relat_1(B_35,k3_xboole_0(k1_relat_1(B_35),A_36)) = k7_relat_1(B_35,A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_107,plain,(
    ! [B_27,A_28] :
      ( k5_relat_1(B_27,k6_relat_1(A_28)) = k8_relat_1(A_28,B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_relat_1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_114,plain,(
    ! [A_28,A_12] :
      ( k8_relat_1(A_28,k6_relat_1(A_12)) = k7_relat_1(k6_relat_1(A_28),A_12)
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_16])).

tff(c_127,plain,(
    ! [A_28,A_12] : k8_relat_1(A_28,k6_relat_1(A_12)) = k7_relat_1(k6_relat_1(A_28),A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_114])).

tff(c_14,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_144,plain,(
    ! [A_31,B_32] :
      ( k8_relat_1(A_31,B_32) = B_32
      | ~ r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_31,A_11] :
      ( k8_relat_1(A_31,k6_relat_1(A_11)) = k6_relat_1(A_11)
      | ~ r1_tarski(A_11,A_31)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_144])).

tff(c_149,plain,(
    ! [A_31,A_11] :
      ( k7_relat_1(k6_relat_1(A_31),A_11) = k6_relat_1(A_11)
      | ~ r1_tarski(A_11,A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_127,c_147])).

tff(c_170,plain,(
    ! [A_31,A_36] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_31)),A_36)) = k7_relat_1(k6_relat_1(A_31),A_36)
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_31)),A_36),A_31)
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_149])).

tff(c_191,plain,(
    ! [A_31,A_36] : k7_relat_1(k6_relat_1(A_31),A_36) = k6_relat_1(k3_xboole_0(A_31,A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4,c_12,c_12,c_170])).

tff(c_93,plain,(
    ! [A_25,B_26] :
      ( k5_relat_1(k6_relat_1(A_25),B_26) = k7_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_22])).

tff(c_105,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_99])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.18  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.84/1.18  
% 1.84/1.18  %Foreground sorts:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Background operators:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Foreground operators:
% 1.84/1.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.84/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.84/1.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.84/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.84/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.84/1.18  
% 1.92/1.19  tff(f_55, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.92/1.19  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.92/1.19  tff(f_47, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.92/1.19  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 1.92/1.19  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.92/1.19  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.92/1.19  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.92/1.19  tff(f_58, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.92/1.19  tff(c_18, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.92/1.19  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.19  tff(c_12, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.19  tff(c_163, plain, (![B_35, A_36]: (k7_relat_1(B_35, k3_xboole_0(k1_relat_1(B_35), A_36))=k7_relat_1(B_35, A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.19  tff(c_107, plain, (![B_27, A_28]: (k5_relat_1(B_27, k6_relat_1(A_28))=k8_relat_1(A_28, B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.19  tff(c_16, plain, (![A_12, B_13]: (k5_relat_1(k6_relat_1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.19  tff(c_114, plain, (![A_28, A_12]: (k8_relat_1(A_28, k6_relat_1(A_12))=k7_relat_1(k6_relat_1(A_28), A_12) | ~v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_16])).
% 1.92/1.19  tff(c_127, plain, (![A_28, A_12]: (k8_relat_1(A_28, k6_relat_1(A_12))=k7_relat_1(k6_relat_1(A_28), A_12))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_114])).
% 1.92/1.19  tff(c_14, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.19  tff(c_144, plain, (![A_31, B_32]: (k8_relat_1(A_31, B_32)=B_32 | ~r1_tarski(k2_relat_1(B_32), A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.19  tff(c_147, plain, (![A_31, A_11]: (k8_relat_1(A_31, k6_relat_1(A_11))=k6_relat_1(A_11) | ~r1_tarski(A_11, A_31) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_144])).
% 1.92/1.19  tff(c_149, plain, (![A_31, A_11]: (k7_relat_1(k6_relat_1(A_31), A_11)=k6_relat_1(A_11) | ~r1_tarski(A_11, A_31))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_127, c_147])).
% 1.92/1.19  tff(c_170, plain, (![A_31, A_36]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_31)), A_36))=k7_relat_1(k6_relat_1(A_31), A_36) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_31)), A_36), A_31) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_149])).
% 1.92/1.19  tff(c_191, plain, (![A_31, A_36]: (k7_relat_1(k6_relat_1(A_31), A_36)=k6_relat_1(k3_xboole_0(A_31, A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4, c_12, c_12, c_170])).
% 1.92/1.19  tff(c_93, plain, (![A_25, B_26]: (k5_relat_1(k6_relat_1(A_25), B_26)=k7_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.19  tff(c_22, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.92/1.19  tff(c_99, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_22])).
% 1.92/1.19  tff(c_105, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_99])).
% 1.92/1.19  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_105])).
% 1.92/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  Inference rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Ref     : 0
% 1.92/1.19  #Sup     : 37
% 1.92/1.19  #Fact    : 0
% 1.92/1.19  #Define  : 0
% 1.92/1.19  #Split   : 1
% 1.92/1.19  #Chain   : 0
% 1.92/1.19  #Close   : 0
% 1.92/1.19  
% 1.92/1.19  Ordering : KBO
% 1.92/1.19  
% 1.92/1.19  Simplification rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Subsume      : 1
% 1.92/1.19  #Demod        : 25
% 1.92/1.19  #Tautology    : 26
% 1.92/1.19  #SimpNegUnit  : 0
% 1.92/1.19  #BackRed      : 3
% 1.92/1.19  
% 1.92/1.19  #Partial instantiations: 0
% 1.92/1.19  #Strategies tried      : 1
% 1.92/1.19  
% 1.92/1.19  Timing (in seconds)
% 1.92/1.19  ----------------------
% 1.92/1.19  Preprocessing        : 0.27
% 1.92/1.19  Parsing              : 0.16
% 1.92/1.19  CNF conversion       : 0.02
% 1.92/1.19  Main loop            : 0.16
% 1.92/1.19  Inferencing          : 0.06
% 1.92/1.19  Reduction            : 0.06
% 1.92/1.19  Demodulation         : 0.05
% 1.92/1.19  BG Simplification    : 0.01
% 1.92/1.19  Subsumption          : 0.02
% 1.92/1.19  Abstraction          : 0.01
% 1.92/1.19  MUC search           : 0.00
% 1.92/1.19  Cooper               : 0.00
% 1.92/1.19  Total                : 0.46
% 1.92/1.19  Index Insertion      : 0.00
% 1.92/1.19  Index Deletion       : 0.00
% 1.92/1.19  Index Matching       : 0.00
% 1.92/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
