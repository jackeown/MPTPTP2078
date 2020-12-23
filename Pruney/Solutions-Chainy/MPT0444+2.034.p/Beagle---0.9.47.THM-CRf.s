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
% DateTime   : Thu Dec  3 09:58:25 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   45 (  62 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  90 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_81,plain,(
    ! [A_43,B_44,C_45] : r1_tarski(k2_xboole_0(k3_xboole_0(A_43,B_44),k3_xboole_0(A_43,C_45)),k2_xboole_0(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [A_43,B_44] : r1_tarski(k3_xboole_0(A_43,B_44),k2_xboole_0(B_44,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_81])).

tff(c_89,plain,(
    ! [A_43,B_44] : r1_tarski(k3_xboole_0(A_43,B_44),B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_85])).

tff(c_20,plain,(
    ! [A_22,B_24] :
      ( r1_tarski(k2_relat_1(A_22),k2_relat_1(B_24))
      | ~ r1_tarski(A_22,B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(A_40,k3_xboole_0(B_41,C_42))
      | ~ r1_tarski(A_40,C_42)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_24])).

tff(c_95,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_98,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_95])).

tff(c_101,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4,c_98])).

tff(c_104,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_101])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_104])).

tff(c_109,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_113,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_109])).

tff(c_116,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_89,c_113])).

tff(c_119,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.29  % Computer   : n005.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 12:20:47 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.13  
% 1.75/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.13  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.75/1.13  
% 1.75/1.13  %Foreground sorts:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Background operators:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Foreground operators:
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.75/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.75/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.75/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.75/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.75/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.75/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.75/1.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.75/1.13  
% 1.75/1.14  tff(f_68, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 1.75/1.14  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.75/1.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.75/1.14  tff(f_37, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 1.75/1.14  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.75/1.14  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.75/1.14  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.75/1.14  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.75/1.14  tff(c_18, plain, (![A_20, B_21]: (v1_relat_1(k3_xboole_0(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.75/1.14  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.75/1.14  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.14  tff(c_81, plain, (![A_43, B_44, C_45]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_43, B_44), k3_xboole_0(A_43, C_45)), k2_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.14  tff(c_85, plain, (![A_43, B_44]: (r1_tarski(k3_xboole_0(A_43, B_44), k2_xboole_0(B_44, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_81])).
% 1.75/1.14  tff(c_89, plain, (![A_43, B_44]: (r1_tarski(k3_xboole_0(A_43, B_44), B_44))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_85])).
% 1.75/1.14  tff(c_20, plain, (![A_22, B_24]: (r1_tarski(k2_relat_1(A_22), k2_relat_1(B_24)) | ~r1_tarski(A_22, B_24) | ~v1_relat_1(B_24) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.75/1.14  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.14  tff(c_76, plain, (![A_40, B_41, C_42]: (r1_tarski(A_40, k3_xboole_0(B_41, C_42)) | ~r1_tarski(A_40, C_42) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.75/1.14  tff(c_24, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.75/1.14  tff(c_80, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_76, c_24])).
% 1.75/1.14  tff(c_95, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_80])).
% 1.75/1.14  tff(c_98, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_95])).
% 1.75/1.14  tff(c_101, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4, c_98])).
% 1.75/1.14  tff(c_104, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_101])).
% 1.75/1.14  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_104])).
% 1.75/1.14  tff(c_109, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_80])).
% 1.75/1.14  tff(c_113, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_109])).
% 1.75/1.14  tff(c_116, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_89, c_113])).
% 1.75/1.14  tff(c_119, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_116])).
% 1.75/1.14  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_119])).
% 1.75/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.14  
% 1.75/1.14  Inference rules
% 1.75/1.14  ----------------------
% 1.75/1.14  #Ref     : 0
% 1.75/1.14  #Sup     : 17
% 1.75/1.14  #Fact    : 0
% 1.75/1.14  #Define  : 0
% 1.75/1.14  #Split   : 1
% 1.75/1.14  #Chain   : 0
% 1.75/1.14  #Close   : 0
% 1.75/1.14  
% 1.75/1.14  Ordering : KBO
% 1.75/1.14  
% 1.75/1.14  Simplification rules
% 1.75/1.14  ----------------------
% 1.75/1.14  #Subsume      : 0
% 1.75/1.14  #Demod        : 9
% 1.75/1.14  #Tautology    : 11
% 1.75/1.14  #SimpNegUnit  : 0
% 1.75/1.14  #BackRed      : 0
% 1.75/1.14  
% 1.75/1.14  #Partial instantiations: 0
% 1.75/1.14  #Strategies tried      : 1
% 1.75/1.14  
% 1.75/1.14  Timing (in seconds)
% 1.75/1.14  ----------------------
% 1.75/1.15  Preprocessing        : 0.30
% 1.75/1.15  Parsing              : 0.16
% 1.75/1.15  CNF conversion       : 0.02
% 1.75/1.15  Main loop            : 0.13
% 1.75/1.15  Inferencing          : 0.05
% 1.75/1.15  Reduction            : 0.04
% 1.75/1.15  Demodulation         : 0.03
% 1.75/1.15  BG Simplification    : 0.01
% 1.75/1.15  Subsumption          : 0.02
% 1.75/1.15  Abstraction          : 0.01
% 1.75/1.15  MUC search           : 0.00
% 1.75/1.15  Cooper               : 0.00
% 1.75/1.15  Total                : 0.47
% 1.75/1.15  Index Insertion      : 0.00
% 1.75/1.15  Index Deletion       : 0.00
% 1.75/1.15  Index Matching       : 0.00
% 1.75/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
