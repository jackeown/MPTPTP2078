%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:24 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  60 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 101 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k3_xboole_0(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_1'(A_35,B_36),A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_110,plain,(
    ! [A_54,B_55,B_56] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_54,B_55),B_56),B_55)
      | r1_tarski(k3_xboole_0(A_54,B_55),B_56) ) ),
    inference(resolution,[status(thm)],[c_46,c_10])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [A_54,B_55] : r1_tarski(k3_xboole_0(A_54,B_55),B_55) ),
    inference(resolution,[status(thm)],[c_110,c_4])).

tff(c_32,plain,(
    ! [A_19,B_21] :
      ( r1_tarski(k2_relat_1(A_19),k2_relat_1(B_21))
      | ~ r1_tarski(A_19,B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(A_44,k3_xboole_0(B_45,C_46))
      | ~ r1_tarski(A_44,C_46)
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k2_relat_1('#skF_4'),k2_relat_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_88,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_5')),k2_relat_1('#skF_5'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_5')),k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_84,c_36])).

tff(c_150,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_5')),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_153,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_32,c_150])).

tff(c_156,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_26,c_153])).

tff(c_159,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_156])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_159])).

tff(c_164,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_5')),k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_168,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_32,c_164])).

tff(c_171,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_128,c_168])).

tff(c_174,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_171])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:27:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.20  
% 2.13/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.20  %$ r2_hidden > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.13/1.20  
% 2.13/1.20  %Foreground sorts:
% 2.13/1.20  
% 2.13/1.20  
% 2.13/1.20  %Background operators:
% 2.13/1.20  
% 2.13/1.20  
% 2.13/1.20  %Foreground operators:
% 2.13/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.20  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.13/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.13/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.13/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.20  
% 2.21/1.21  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 2.21/1.21  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.21/1.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.21/1.21  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.21/1.21  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.21/1.21  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.21/1.21  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.21/1.21  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.21  tff(c_30, plain, (![A_17, B_18]: (v1_relat_1(k3_xboole_0(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.21  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.21  tff(c_46, plain, (![A_35, B_36]: (r2_hidden('#skF_1'(A_35, B_36), A_35) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.21  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.21/1.21  tff(c_110, plain, (![A_54, B_55, B_56]: (r2_hidden('#skF_1'(k3_xboole_0(A_54, B_55), B_56), B_55) | r1_tarski(k3_xboole_0(A_54, B_55), B_56))), inference(resolution, [status(thm)], [c_46, c_10])).
% 2.21/1.21  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.21  tff(c_128, plain, (![A_54, B_55]: (r1_tarski(k3_xboole_0(A_54, B_55), B_55))), inference(resolution, [status(thm)], [c_110, c_4])).
% 2.21/1.21  tff(c_32, plain, (![A_19, B_21]: (r1_tarski(k2_relat_1(A_19), k2_relat_1(B_21)) | ~r1_tarski(A_19, B_21) | ~v1_relat_1(B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.21/1.21  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.21  tff(c_84, plain, (![A_44, B_45, C_46]: (r1_tarski(A_44, k3_xboole_0(B_45, C_46)) | ~r1_tarski(A_44, C_46) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.21  tff(c_36, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k2_relat_1('#skF_4'), k2_relat_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.21  tff(c_88, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k2_relat_1('#skF_5')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_84, c_36])).
% 2.21/1.21  tff(c_150, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_88])).
% 2.21/1.21  tff(c_153, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_150])).
% 2.21/1.21  tff(c_156, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_26, c_153])).
% 2.21/1.21  tff(c_159, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_156])).
% 2.21/1.21  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_159])).
% 2.21/1.21  tff(c_164, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_88])).
% 2.21/1.21  tff(c_168, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_164])).
% 2.21/1.21  tff(c_171, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_128, c_168])).
% 2.21/1.21  tff(c_174, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_171])).
% 2.21/1.21  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_174])).
% 2.21/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.21  
% 2.21/1.21  Inference rules
% 2.21/1.21  ----------------------
% 2.21/1.21  #Ref     : 0
% 2.21/1.21  #Sup     : 25
% 2.21/1.21  #Fact    : 0
% 2.21/1.21  #Define  : 0
% 2.21/1.21  #Split   : 1
% 2.21/1.21  #Chain   : 0
% 2.21/1.21  #Close   : 0
% 2.21/1.21  
% 2.21/1.21  Ordering : KBO
% 2.21/1.21  
% 2.21/1.21  Simplification rules
% 2.21/1.21  ----------------------
% 2.21/1.21  #Subsume      : 0
% 2.21/1.21  #Demod        : 7
% 2.21/1.21  #Tautology    : 4
% 2.21/1.21  #SimpNegUnit  : 0
% 2.21/1.21  #BackRed      : 0
% 2.21/1.21  
% 2.21/1.21  #Partial instantiations: 0
% 2.21/1.21  #Strategies tried      : 1
% 2.21/1.21  
% 2.21/1.21  Timing (in seconds)
% 2.21/1.21  ----------------------
% 2.21/1.22  Preprocessing        : 0.28
% 2.21/1.22  Parsing              : 0.15
% 2.21/1.22  CNF conversion       : 0.02
% 2.21/1.22  Main loop            : 0.17
% 2.21/1.22  Inferencing          : 0.06
% 2.21/1.22  Reduction            : 0.05
% 2.21/1.22  Demodulation         : 0.04
% 2.21/1.22  BG Simplification    : 0.01
% 2.21/1.22  Subsumption          : 0.04
% 2.21/1.22  Abstraction          : 0.01
% 2.21/1.22  MUC search           : 0.00
% 2.21/1.22  Cooper               : 0.00
% 2.21/1.22  Total                : 0.49
% 2.21/1.22  Index Insertion      : 0.00
% 2.21/1.22  Index Deletion       : 0.00
% 2.21/1.22  Index Matching       : 0.00
% 2.21/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
