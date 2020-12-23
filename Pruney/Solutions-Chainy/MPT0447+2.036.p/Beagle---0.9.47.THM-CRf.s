%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:32 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   45 (  76 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 158 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k2_relat_1(A_10),k2_relat_1(B_12))
      | ~ r1_tarski(A_10,B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_22] :
      ( k2_xboole_0(k1_relat_1(A_22),k2_relat_1(A_22)) = k3_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_3,A_22] :
      ( r1_tarski(A_3,k3_relat_1(A_22))
      | ~ r1_tarski(A_3,k2_relat_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_4])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k1_relat_1(A_10),k1_relat_1(B_12))
      | ~ r1_tarski(A_10,B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_16,C_17,B_18] :
      ( r1_tarski(A_16,k2_xboole_0(C_17,B_18))
      | ~ r1_tarski(A_16,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_16,B_2,A_1] :
      ( r1_tarski(A_16,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_16,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_74,plain,(
    ! [A_16,A_22] :
      ( r1_tarski(A_16,k3_relat_1(A_22))
      | ~ r1_tarski(A_16,k1_relat_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_57])).

tff(c_8,plain,(
    ! [A_9] :
      ( k2_xboole_0(k1_relat_1(A_9),k2_relat_1(A_9)) = k3_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(k2_xboole_0(A_23,C_24),B_25)
      | ~ r1_tarski(C_24,B_25)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k3_relat_1(A_34),B_35)
      | ~ r1_tarski(k2_relat_1(A_34),B_35)
      | ~ r1_tarski(k1_relat_1(A_34),B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_83])).

tff(c_14,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_118,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_109,c_14])).

tff(c_127,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_118])).

tff(c_128,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_131,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_128])).

tff(c_137,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_131])).

tff(c_144,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_137])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_144])).

tff(c_149,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_156,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_149])).

tff(c_162,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_156])).

tff(c_165,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_162])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.18  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.69/1.18  
% 1.69/1.18  %Foreground sorts:
% 1.69/1.18  
% 1.69/1.18  
% 1.69/1.18  %Background operators:
% 1.69/1.18  
% 1.69/1.18  
% 1.69/1.18  %Foreground operators:
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.18  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.69/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.18  
% 1.91/1.19  tff(f_62, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 1.91/1.19  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.91/1.19  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.91/1.19  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.91/1.19  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.91/1.19  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.91/1.19  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.19  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.19  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.19  tff(c_10, plain, (![A_10, B_12]: (r1_tarski(k2_relat_1(A_10), k2_relat_1(B_12)) | ~r1_tarski(A_10, B_12) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.19  tff(c_68, plain, (![A_22]: (k2_xboole_0(k1_relat_1(A_22), k2_relat_1(A_22))=k3_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.19  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.19  tff(c_77, plain, (![A_3, A_22]: (r1_tarski(A_3, k3_relat_1(A_22)) | ~r1_tarski(A_3, k2_relat_1(A_22)) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_68, c_4])).
% 1.91/1.19  tff(c_12, plain, (![A_10, B_12]: (r1_tarski(k1_relat_1(A_10), k1_relat_1(B_12)) | ~r1_tarski(A_10, B_12) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.19  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.19  tff(c_54, plain, (![A_16, C_17, B_18]: (r1_tarski(A_16, k2_xboole_0(C_17, B_18)) | ~r1_tarski(A_16, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.19  tff(c_57, plain, (![A_16, B_2, A_1]: (r1_tarski(A_16, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_16, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_54])).
% 1.91/1.19  tff(c_74, plain, (![A_16, A_22]: (r1_tarski(A_16, k3_relat_1(A_22)) | ~r1_tarski(A_16, k1_relat_1(A_22)) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_68, c_57])).
% 1.91/1.19  tff(c_8, plain, (![A_9]: (k2_xboole_0(k1_relat_1(A_9), k2_relat_1(A_9))=k3_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.19  tff(c_83, plain, (![A_23, C_24, B_25]: (r1_tarski(k2_xboole_0(A_23, C_24), B_25) | ~r1_tarski(C_24, B_25) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.19  tff(c_109, plain, (![A_34, B_35]: (r1_tarski(k3_relat_1(A_34), B_35) | ~r1_tarski(k2_relat_1(A_34), B_35) | ~r1_tarski(k1_relat_1(A_34), B_35) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_8, c_83])).
% 1.91/1.19  tff(c_14, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.19  tff(c_118, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_109, c_14])).
% 1.91/1.19  tff(c_127, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_118])).
% 1.91/1.19  tff(c_128, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_127])).
% 1.91/1.19  tff(c_131, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_128])).
% 1.91/1.19  tff(c_137, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_131])).
% 1.91/1.19  tff(c_144, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_137])).
% 1.91/1.19  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_144])).
% 1.91/1.19  tff(c_149, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_127])).
% 1.91/1.19  tff(c_156, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_77, c_149])).
% 1.91/1.19  tff(c_162, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_156])).
% 1.91/1.19  tff(c_165, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_162])).
% 1.91/1.19  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_165])).
% 1.91/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  Inference rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Ref     : 0
% 1.91/1.19  #Sup     : 30
% 1.91/1.19  #Fact    : 0
% 1.91/1.19  #Define  : 0
% 1.91/1.19  #Split   : 2
% 1.91/1.19  #Chain   : 0
% 1.91/1.19  #Close   : 0
% 1.91/1.19  
% 1.91/1.19  Ordering : KBO
% 1.91/1.19  
% 1.91/1.19  Simplification rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Subsume      : 5
% 1.91/1.19  #Demod        : 15
% 1.91/1.19  #Tautology    : 10
% 1.91/1.19  #SimpNegUnit  : 0
% 1.91/1.19  #BackRed      : 0
% 1.91/1.19  
% 1.91/1.19  #Partial instantiations: 0
% 1.91/1.19  #Strategies tried      : 1
% 1.91/1.19  
% 1.91/1.19  Timing (in seconds)
% 1.91/1.19  ----------------------
% 1.91/1.19  Preprocessing        : 0.27
% 1.91/1.19  Parsing              : 0.15
% 1.91/1.19  CNF conversion       : 0.02
% 1.91/1.19  Main loop            : 0.16
% 1.91/1.19  Inferencing          : 0.06
% 1.91/1.19  Reduction            : 0.05
% 1.91/1.19  Demodulation         : 0.04
% 1.91/1.19  BG Simplification    : 0.01
% 1.91/1.19  Subsumption          : 0.03
% 1.91/1.19  Abstraction          : 0.01
% 1.91/1.19  MUC search           : 0.00
% 1.91/1.19  Cooper               : 0.00
% 1.91/1.19  Total                : 0.46
% 1.91/1.19  Index Insertion      : 0.00
% 1.91/1.19  Index Deletion       : 0.00
% 1.91/1.19  Index Matching       : 0.00
% 1.91/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
