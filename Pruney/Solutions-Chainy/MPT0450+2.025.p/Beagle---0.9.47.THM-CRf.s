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
% DateTime   : Thu Dec  3 09:58:39 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   51 (  86 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 117 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [B_30,A_31] : k1_setfam_1(k2_tarski(B_30,A_31)) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    ! [B_32,A_33] : k3_xboole_0(B_32,A_33) = k3_xboole_0(A_33,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k3_xboole_0(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_123,plain,(
    ! [A_33,B_32] :
      ( v1_relat_1(k3_xboole_0(A_33,B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_14])).

tff(c_88,plain,(
    ! [B_30,A_31] : k3_xboole_0(B_30,A_31) = k3_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_152,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_181,plain,(
    ! [A_41,B_42] : r1_tarski(k3_xboole_0(A_41,B_42),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_4])).

tff(c_184,plain,(
    ! [B_30,A_31] : r1_tarski(k3_xboole_0(B_30,A_31),A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_181])).

tff(c_276,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k3_relat_1(A_51),k3_relat_1(B_52))
      | ~ r1_tarski(A_51,B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_161,plain,(
    ! [A_36,B_37] : r1_tarski(k3_xboole_0(A_36,B_37),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_4])).

tff(c_257,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(k3_relat_1(A_49),k3_relat_1(B_50))
      | ~ r1_tarski(A_49,B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_170,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(A_38,k3_xboole_0(B_39,C_40))
      | ~ r1_tarski(A_38,C_40)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_180,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_170,c_18])).

tff(c_198,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_260,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_257,c_198])).

tff(c_263,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_161,c_260])).

tff(c_266,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_123,c_263])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_266])).

tff(c_274,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_279,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_276,c_274])).

tff(c_282,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_184,c_279])).

tff(c_285,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_123,c_282])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_285])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_2 > #skF_1
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.21  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.88/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.88/1.21  
% 2.02/1.22  tff(f_62, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 2.02/1.22  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.02/1.22  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.02/1.22  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.02/1.22  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.02/1.22  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.02/1.22  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.02/1.22  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.02/1.22  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.22  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.22  tff(c_67, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.22  tff(c_82, plain, (![B_30, A_31]: (k1_setfam_1(k2_tarski(B_30, A_31))=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_8, c_67])).
% 2.02/1.22  tff(c_12, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.22  tff(c_105, plain, (![B_32, A_33]: (k3_xboole_0(B_32, A_33)=k3_xboole_0(A_33, B_32))), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 2.02/1.22  tff(c_14, plain, (![A_14, B_15]: (v1_relat_1(k3_xboole_0(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.22  tff(c_123, plain, (![A_33, B_32]: (v1_relat_1(k3_xboole_0(A_33, B_32)) | ~v1_relat_1(B_32))), inference(superposition, [status(thm), theory('equality')], [c_105, c_14])).
% 2.02/1.22  tff(c_88, plain, (![B_30, A_31]: (k3_xboole_0(B_30, A_31)=k3_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 2.02/1.22  tff(c_152, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.22  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.22  tff(c_181, plain, (![A_41, B_42]: (r1_tarski(k3_xboole_0(A_41, B_42), A_41))), inference(superposition, [status(thm), theory('equality')], [c_152, c_4])).
% 2.02/1.22  tff(c_184, plain, (![B_30, A_31]: (r1_tarski(k3_xboole_0(B_30, A_31), A_31))), inference(superposition, [status(thm), theory('equality')], [c_88, c_181])).
% 2.02/1.22  tff(c_276, plain, (![A_51, B_52]: (r1_tarski(k3_relat_1(A_51), k3_relat_1(B_52)) | ~r1_tarski(A_51, B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.02/1.22  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.22  tff(c_161, plain, (![A_36, B_37]: (r1_tarski(k3_xboole_0(A_36, B_37), A_36))), inference(superposition, [status(thm), theory('equality')], [c_152, c_4])).
% 2.02/1.22  tff(c_257, plain, (![A_49, B_50]: (r1_tarski(k3_relat_1(A_49), k3_relat_1(B_50)) | ~r1_tarski(A_49, B_50) | ~v1_relat_1(B_50) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.02/1.22  tff(c_170, plain, (![A_38, B_39, C_40]: (r1_tarski(A_38, k3_xboole_0(B_39, C_40)) | ~r1_tarski(A_38, C_40) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.22  tff(c_18, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.22  tff(c_180, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_170, c_18])).
% 2.02/1.22  tff(c_198, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_180])).
% 2.02/1.22  tff(c_260, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_257, c_198])).
% 2.02/1.22  tff(c_263, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_161, c_260])).
% 2.02/1.22  tff(c_266, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_123, c_263])).
% 2.02/1.22  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_266])).
% 2.02/1.22  tff(c_274, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_180])).
% 2.02/1.22  tff(c_279, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_276, c_274])).
% 2.02/1.22  tff(c_282, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_184, c_279])).
% 2.02/1.22  tff(c_285, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_123, c_282])).
% 2.02/1.22  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_285])).
% 2.02/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.22  
% 2.02/1.22  Inference rules
% 2.02/1.22  ----------------------
% 2.02/1.22  #Ref     : 0
% 2.02/1.22  #Sup     : 64
% 2.02/1.22  #Fact    : 0
% 2.02/1.22  #Define  : 0
% 2.02/1.22  #Split   : 1
% 2.02/1.22  #Chain   : 0
% 2.02/1.22  #Close   : 0
% 2.02/1.22  
% 2.02/1.22  Ordering : KBO
% 2.02/1.22  
% 2.02/1.22  Simplification rules
% 2.02/1.22  ----------------------
% 2.02/1.22  #Subsume      : 6
% 2.02/1.23  #Demod        : 18
% 2.02/1.23  #Tautology    : 42
% 2.02/1.23  #SimpNegUnit  : 0
% 2.02/1.23  #BackRed      : 0
% 2.02/1.23  
% 2.02/1.23  #Partial instantiations: 0
% 2.02/1.23  #Strategies tried      : 1
% 2.02/1.23  
% 2.02/1.23  Timing (in seconds)
% 2.02/1.23  ----------------------
% 2.02/1.23  Preprocessing        : 0.27
% 2.02/1.23  Parsing              : 0.14
% 2.02/1.23  CNF conversion       : 0.02
% 2.02/1.23  Main loop            : 0.18
% 2.02/1.23  Inferencing          : 0.07
% 2.02/1.23  Reduction            : 0.06
% 2.02/1.23  Demodulation         : 0.05
% 2.02/1.23  BG Simplification    : 0.01
% 2.02/1.23  Subsumption          : 0.03
% 2.02/1.23  Abstraction          : 0.01
% 2.02/1.23  MUC search           : 0.00
% 2.02/1.23  Cooper               : 0.00
% 2.02/1.23  Total                : 0.48
% 2.02/1.23  Index Insertion      : 0.00
% 2.02/1.23  Index Deletion       : 0.00
% 2.02/1.23  Index Matching       : 0.00
% 2.02/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
