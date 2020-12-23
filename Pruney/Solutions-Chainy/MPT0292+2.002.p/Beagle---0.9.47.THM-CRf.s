%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:35 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  55 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [A_20,B_21] : r1_tarski(k3_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_38])).

tff(c_12,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_116,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,k3_tarski(B_34))
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_170,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,k3_tarski(B_38)) = A_37
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_116,c_8])).

tff(c_211,plain,(
    ! [B_38,B_2] :
      ( k3_xboole_0(k3_tarski(B_38),B_2) = B_2
      | ~ r2_hidden(B_2,B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_170])).

tff(c_611,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_3'(A_51,B_52),A_51)
      | r1_tarski(k3_tarski(A_51),B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1027,plain,(
    ! [A_67,B_68] :
      ( r1_tarski('#skF_3'(k1_zfmisc_1(A_67),B_68),A_67)
      | r1_tarski(k3_tarski(k1_zfmisc_1(A_67)),B_68) ) ),
    inference(resolution,[status(thm)],[c_611,c_10])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( ~ r1_tarski('#skF_3'(A_16,B_17),B_17)
      | r1_tarski(k3_tarski(A_16),B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1041,plain,(
    ! [A_69] : r1_tarski(k3_tarski(k1_zfmisc_1(A_69)),A_69) ),
    inference(resolution,[status(thm)],[c_1027,c_24])).

tff(c_1049,plain,(
    ! [A_70] : k3_xboole_0(k3_tarski(k1_zfmisc_1(A_70)),A_70) = k3_tarski(k1_zfmisc_1(A_70)) ),
    inference(resolution,[status(thm)],[c_1041,c_8])).

tff(c_1372,plain,(
    ! [B_76] :
      ( k3_tarski(k1_zfmisc_1(B_76)) = B_76
      | ~ r2_hidden(B_76,k1_zfmisc_1(B_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_1049])).

tff(c_1376,plain,(
    ! [A_9] :
      ( k3_tarski(k1_zfmisc_1(A_9)) = A_9
      | ~ r1_tarski(A_9,A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_1372])).

tff(c_1379,plain,(
    ! [A_9] : k3_tarski(k1_zfmisc_1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_1376])).

tff(c_28,plain,(
    k3_tarski(k1_zfmisc_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.44  
% 2.72/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.44  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.72/1.44  
% 2.72/1.44  %Foreground sorts:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Background operators:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Foreground operators:
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.72/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.72/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.72/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.72/1.44  
% 2.72/1.45  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.72/1.45  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.72/1.45  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.72/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.72/1.45  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.72/1.45  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.72/1.45  tff(f_53, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.72/1.45  tff(f_56, negated_conjecture, ~(![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.72/1.45  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.45  tff(c_38, plain, (![A_20, B_21]: (r1_tarski(k3_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.45  tff(c_41, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_38])).
% 2.72/1.45  tff(c_12, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.72/1.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.45  tff(c_116, plain, (![A_33, B_34]: (r1_tarski(A_33, k3_tarski(B_34)) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.72/1.45  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.45  tff(c_170, plain, (![A_37, B_38]: (k3_xboole_0(A_37, k3_tarski(B_38))=A_37 | ~r2_hidden(A_37, B_38))), inference(resolution, [status(thm)], [c_116, c_8])).
% 2.72/1.45  tff(c_211, plain, (![B_38, B_2]: (k3_xboole_0(k3_tarski(B_38), B_2)=B_2 | ~r2_hidden(B_2, B_38))), inference(superposition, [status(thm), theory('equality')], [c_2, c_170])).
% 2.72/1.45  tff(c_611, plain, (![A_51, B_52]: (r2_hidden('#skF_3'(A_51, B_52), A_51) | r1_tarski(k3_tarski(A_51), B_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.45  tff(c_10, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.72/1.45  tff(c_1027, plain, (![A_67, B_68]: (r1_tarski('#skF_3'(k1_zfmisc_1(A_67), B_68), A_67) | r1_tarski(k3_tarski(k1_zfmisc_1(A_67)), B_68))), inference(resolution, [status(thm)], [c_611, c_10])).
% 2.72/1.45  tff(c_24, plain, (![A_16, B_17]: (~r1_tarski('#skF_3'(A_16, B_17), B_17) | r1_tarski(k3_tarski(A_16), B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.45  tff(c_1041, plain, (![A_69]: (r1_tarski(k3_tarski(k1_zfmisc_1(A_69)), A_69))), inference(resolution, [status(thm)], [c_1027, c_24])).
% 2.72/1.45  tff(c_1049, plain, (![A_70]: (k3_xboole_0(k3_tarski(k1_zfmisc_1(A_70)), A_70)=k3_tarski(k1_zfmisc_1(A_70)))), inference(resolution, [status(thm)], [c_1041, c_8])).
% 2.72/1.45  tff(c_1372, plain, (![B_76]: (k3_tarski(k1_zfmisc_1(B_76))=B_76 | ~r2_hidden(B_76, k1_zfmisc_1(B_76)))), inference(superposition, [status(thm), theory('equality')], [c_211, c_1049])).
% 2.72/1.45  tff(c_1376, plain, (![A_9]: (k3_tarski(k1_zfmisc_1(A_9))=A_9 | ~r1_tarski(A_9, A_9))), inference(resolution, [status(thm)], [c_12, c_1372])).
% 2.72/1.45  tff(c_1379, plain, (![A_9]: (k3_tarski(k1_zfmisc_1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_41, c_1376])).
% 2.72/1.45  tff(c_28, plain, (k3_tarski(k1_zfmisc_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.72/1.45  tff(c_1390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1379, c_28])).
% 2.72/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.45  
% 2.72/1.45  Inference rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Ref     : 0
% 2.72/1.45  #Sup     : 324
% 2.72/1.45  #Fact    : 0
% 2.72/1.45  #Define  : 0
% 2.72/1.45  #Split   : 0
% 2.72/1.45  #Chain   : 0
% 2.72/1.45  #Close   : 0
% 2.72/1.45  
% 2.72/1.45  Ordering : KBO
% 2.72/1.45  
% 2.72/1.45  Simplification rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Subsume      : 47
% 2.72/1.45  #Demod        : 333
% 2.72/1.45  #Tautology    : 216
% 2.72/1.45  #SimpNegUnit  : 0
% 2.72/1.45  #BackRed      : 5
% 2.72/1.45  
% 2.72/1.45  #Partial instantiations: 0
% 2.72/1.45  #Strategies tried      : 1
% 2.72/1.45  
% 2.72/1.45  Timing (in seconds)
% 2.72/1.45  ----------------------
% 2.72/1.45  Preprocessing        : 0.27
% 2.72/1.45  Parsing              : 0.15
% 2.72/1.45  CNF conversion       : 0.02
% 2.72/1.45  Main loop            : 0.42
% 2.72/1.45  Inferencing          : 0.15
% 2.72/1.45  Reduction            : 0.17
% 2.72/1.45  Demodulation         : 0.14
% 2.72/1.45  BG Simplification    : 0.02
% 2.72/1.45  Subsumption          : 0.06
% 2.72/1.45  Abstraction          : 0.02
% 2.72/1.45  MUC search           : 0.00
% 2.72/1.45  Cooper               : 0.00
% 2.72/1.45  Total                : 0.72
% 2.72/1.45  Index Insertion      : 0.00
% 2.72/1.45  Index Deletion       : 0.00
% 2.72/1.45  Index Matching       : 0.00
% 2.72/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
