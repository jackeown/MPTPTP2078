%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:43 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   47 (  54 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  59 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_47,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    ! [B_36,A_37] : k5_relat_1(k6_relat_1(B_36),k6_relat_1(A_37)) = k6_relat_1(k3_xboole_0(A_37,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = k8_relat_1(A_12,B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_93,plain,(
    ! [A_37,B_36] :
      ( k8_relat_1(A_37,k6_relat_1(B_36)) = k6_relat_1(k3_xboole_0(A_37,B_36))
      | ~ v1_relat_1(k6_relat_1(B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_10])).

tff(c_103,plain,(
    ! [A_37,B_36] : k8_relat_1(A_37,k6_relat_1(B_36)) = k6_relat_1(k3_xboole_0(A_37,B_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_93])).

tff(c_16,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [A_40,B_41] :
      ( k8_relat_1(A_40,B_41) = B_41
      | ~ r1_tarski(k2_relat_1(B_41),A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_120,plain,(
    ! [A_40,A_16] :
      ( k8_relat_1(A_40,k6_relat_1(A_16)) = k6_relat_1(A_16)
      | ~ r1_tarski(A_16,A_40)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_117])).

tff(c_132,plain,(
    ! [A_46,A_47] :
      ( k6_relat_1(k3_xboole_0(A_46,A_47)) = k6_relat_1(A_47)
      | ~ r1_tarski(A_47,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_103,c_120])).

tff(c_150,plain,(
    ! [A_46,A_47] :
      ( k3_xboole_0(A_46,A_47) = k1_relat_1(k6_relat_1(A_47))
      | ~ r1_tarski(A_47,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_14])).

tff(c_170,plain,(
    ! [A_48,A_49] :
      ( k3_xboole_0(A_48,A_49) = A_49
      | ~ r1_tarski(A_49,A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_150])).

tff(c_174,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_170])).

tff(c_185,plain,(
    ! [C_50,A_51,B_52] :
      ( k2_wellord1(k2_wellord1(C_50,A_51),B_52) = k2_wellord1(C_50,k3_xboole_0(A_51,B_52))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_194,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_26])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_174,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:09:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.72/1.14  
% 1.72/1.14  %Foreground sorts:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Background operators:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Foreground operators:
% 1.72/1.14  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.72/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.72/1.14  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.72/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.72/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.72/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.14  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.72/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.72/1.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.72/1.14  
% 1.92/1.15  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 1.92/1.15  tff(f_47, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.92/1.15  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.92/1.15  tff(f_53, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.92/1.15  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.92/1.15  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 1.92/1.15  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 1.92/1.15  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.15  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.15  tff(c_14, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.15  tff(c_18, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.15  tff(c_87, plain, (![B_36, A_37]: (k5_relat_1(k6_relat_1(B_36), k6_relat_1(A_37))=k6_relat_1(k3_xboole_0(A_37, B_36)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.15  tff(c_10, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=k8_relat_1(A_12, B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.15  tff(c_93, plain, (![A_37, B_36]: (k8_relat_1(A_37, k6_relat_1(B_36))=k6_relat_1(k3_xboole_0(A_37, B_36)) | ~v1_relat_1(k6_relat_1(B_36)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_10])).
% 1.92/1.15  tff(c_103, plain, (![A_37, B_36]: (k8_relat_1(A_37, k6_relat_1(B_36))=k6_relat_1(k3_xboole_0(A_37, B_36)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_93])).
% 1.92/1.15  tff(c_16, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.15  tff(c_117, plain, (![A_40, B_41]: (k8_relat_1(A_40, B_41)=B_41 | ~r1_tarski(k2_relat_1(B_41), A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.15  tff(c_120, plain, (![A_40, A_16]: (k8_relat_1(A_40, k6_relat_1(A_16))=k6_relat_1(A_16) | ~r1_tarski(A_16, A_40) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_117])).
% 1.92/1.15  tff(c_132, plain, (![A_46, A_47]: (k6_relat_1(k3_xboole_0(A_46, A_47))=k6_relat_1(A_47) | ~r1_tarski(A_47, A_46))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_103, c_120])).
% 1.92/1.15  tff(c_150, plain, (![A_46, A_47]: (k3_xboole_0(A_46, A_47)=k1_relat_1(k6_relat_1(A_47)) | ~r1_tarski(A_47, A_46))), inference(superposition, [status(thm), theory('equality')], [c_132, c_14])).
% 1.92/1.15  tff(c_170, plain, (![A_48, A_49]: (k3_xboole_0(A_48, A_49)=A_49 | ~r1_tarski(A_49, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_150])).
% 1.92/1.15  tff(c_174, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_28, c_170])).
% 1.92/1.15  tff(c_185, plain, (![C_50, A_51, B_52]: (k2_wellord1(k2_wellord1(C_50, A_51), B_52)=k2_wellord1(C_50, k3_xboole_0(A_51, B_52)) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.15  tff(c_26, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.15  tff(c_194, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_185, c_26])).
% 1.92/1.15  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_174, c_194])).
% 1.92/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.15  
% 1.92/1.15  Inference rules
% 1.92/1.15  ----------------------
% 1.92/1.15  #Ref     : 0
% 1.92/1.15  #Sup     : 40
% 1.92/1.15  #Fact    : 0
% 1.92/1.15  #Define  : 0
% 1.92/1.15  #Split   : 0
% 1.92/1.15  #Chain   : 0
% 1.92/1.15  #Close   : 0
% 1.92/1.15  
% 1.92/1.15  Ordering : KBO
% 1.92/1.15  
% 1.92/1.15  Simplification rules
% 1.92/1.15  ----------------------
% 1.92/1.15  #Subsume      : 0
% 1.92/1.15  #Demod        : 15
% 1.92/1.15  #Tautology    : 27
% 1.92/1.15  #SimpNegUnit  : 0
% 1.92/1.15  #BackRed      : 0
% 1.92/1.15  
% 1.92/1.15  #Partial instantiations: 0
% 1.92/1.15  #Strategies tried      : 1
% 1.92/1.15  
% 1.92/1.15  Timing (in seconds)
% 1.92/1.15  ----------------------
% 1.92/1.16  Preprocessing        : 0.29
% 1.92/1.16  Parsing              : 0.15
% 1.92/1.16  CNF conversion       : 0.02
% 1.92/1.16  Main loop            : 0.13
% 1.92/1.16  Inferencing          : 0.05
% 1.92/1.16  Reduction            : 0.04
% 1.92/1.16  Demodulation         : 0.03
% 1.92/1.16  BG Simplification    : 0.01
% 1.92/1.16  Subsumption          : 0.01
% 1.92/1.16  Abstraction          : 0.01
% 1.92/1.16  MUC search           : 0.00
% 1.92/1.16  Cooper               : 0.00
% 1.92/1.16  Total                : 0.44
% 1.92/1.16  Index Insertion      : 0.00
% 1.92/1.16  Index Deletion       : 0.00
% 1.92/1.16  Index Matching       : 0.00
% 1.92/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
