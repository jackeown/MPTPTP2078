%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:40 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   46 (  69 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 ( 101 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k4_xboole_0(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(k3_xboole_0(A_37,B_38))
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_16])).

tff(c_115,plain,(
    ! [B_2,A_1] :
      ( v1_relat_1(k3_xboole_0(B_2,A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_112])).

tff(c_27,plain,(
    ! [B_27,A_28] : k3_xboole_0(B_27,A_28) = k3_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [B_27,A_28] : r1_tarski(k3_xboole_0(B_27,A_28),A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_4])).

tff(c_222,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k3_relat_1(A_53),k3_relat_1(B_54))
      | ~ r1_tarski(A_53,B_54)
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_203,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k3_relat_1(A_51),k3_relat_1(B_52))
      | ~ r1_tarski(A_51,B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_135,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(A_44,k3_xboole_0(B_45,C_46))
      | ~ r1_tarski(A_44,C_46)
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_135,c_20])).

tff(c_201,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_206,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_203,c_201])).

tff(c_209,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4,c_206])).

tff(c_212,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_115,c_209])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_212])).

tff(c_220,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_225,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_222,c_220])).

tff(c_228,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_42,c_225])).

tff(c_231,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_115,c_228])).

tff(c_238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:27:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.40  
% 2.23/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.40  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_2 > #skF_1
% 2.23/1.40  
% 2.23/1.40  %Foreground sorts:
% 2.23/1.40  
% 2.23/1.40  
% 2.23/1.40  %Background operators:
% 2.23/1.40  
% 2.23/1.40  
% 2.23/1.40  %Foreground operators:
% 2.23/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.40  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.23/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.40  
% 2.23/1.42  tff(f_64, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 2.23/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.23/1.42  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.23/1.42  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.23/1.42  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.23/1.42  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.23/1.42  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.23/1.42  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.42  tff(c_94, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.42  tff(c_16, plain, (![A_17, B_18]: (v1_relat_1(k4_xboole_0(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.42  tff(c_112, plain, (![A_37, B_38]: (v1_relat_1(k3_xboole_0(A_37, B_38)) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_94, c_16])).
% 2.23/1.42  tff(c_115, plain, (![B_2, A_1]: (v1_relat_1(k3_xboole_0(B_2, A_1)) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_112])).
% 2.23/1.42  tff(c_27, plain, (![B_27, A_28]: (k3_xboole_0(B_27, A_28)=k3_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.42  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.42  tff(c_42, plain, (![B_27, A_28]: (r1_tarski(k3_xboole_0(B_27, A_28), A_28))), inference(superposition, [status(thm), theory('equality')], [c_27, c_4])).
% 2.23/1.42  tff(c_222, plain, (![A_53, B_54]: (r1_tarski(k3_relat_1(A_53), k3_relat_1(B_54)) | ~r1_tarski(A_53, B_54) | ~v1_relat_1(B_54) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.42  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.42  tff(c_203, plain, (![A_51, B_52]: (r1_tarski(k3_relat_1(A_51), k3_relat_1(B_52)) | ~r1_tarski(A_51, B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.42  tff(c_135, plain, (![A_44, B_45, C_46]: (r1_tarski(A_44, k3_xboole_0(B_45, C_46)) | ~r1_tarski(A_44, C_46) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.42  tff(c_20, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.42  tff(c_145, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_135, c_20])).
% 2.23/1.42  tff(c_201, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_145])).
% 2.23/1.42  tff(c_206, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_203, c_201])).
% 2.23/1.42  tff(c_209, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4, c_206])).
% 2.23/1.42  tff(c_212, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_115, c_209])).
% 2.23/1.42  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_212])).
% 2.23/1.42  tff(c_220, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_145])).
% 2.23/1.42  tff(c_225, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_222, c_220])).
% 2.23/1.42  tff(c_228, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_42, c_225])).
% 2.23/1.42  tff(c_231, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_115, c_228])).
% 2.23/1.42  tff(c_238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_231])).
% 2.23/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.42  
% 2.23/1.42  Inference rules
% 2.23/1.42  ----------------------
% 2.23/1.42  #Ref     : 0
% 2.23/1.42  #Sup     : 50
% 2.23/1.42  #Fact    : 0
% 2.23/1.42  #Define  : 0
% 2.23/1.42  #Split   : 1
% 2.23/1.42  #Chain   : 0
% 2.23/1.42  #Close   : 0
% 2.23/1.42  
% 2.23/1.42  Ordering : KBO
% 2.23/1.42  
% 2.23/1.42  Simplification rules
% 2.23/1.42  ----------------------
% 2.23/1.42  #Subsume      : 7
% 2.23/1.42  #Demod        : 13
% 2.23/1.42  #Tautology    : 29
% 2.23/1.42  #SimpNegUnit  : 0
% 2.23/1.42  #BackRed      : 0
% 2.23/1.42  
% 2.23/1.42  #Partial instantiations: 0
% 2.23/1.42  #Strategies tried      : 1
% 2.23/1.42  
% 2.23/1.42  Timing (in seconds)
% 2.23/1.42  ----------------------
% 2.23/1.42  Preprocessing        : 0.33
% 2.23/1.43  Parsing              : 0.17
% 2.23/1.43  CNF conversion       : 0.02
% 2.23/1.43  Main loop            : 0.22
% 2.23/1.43  Inferencing          : 0.08
% 2.23/1.43  Reduction            : 0.08
% 2.23/1.43  Demodulation         : 0.06
% 2.23/1.43  BG Simplification    : 0.01
% 2.23/1.43  Subsumption          : 0.04
% 2.23/1.43  Abstraction          : 0.01
% 2.23/1.43  MUC search           : 0.00
% 2.23/1.43  Cooper               : 0.00
% 2.23/1.43  Total                : 0.59
% 2.23/1.43  Index Insertion      : 0.00
% 2.23/1.43  Index Deletion       : 0.00
% 2.23/1.43  Index Matching       : 0.00
% 2.23/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
