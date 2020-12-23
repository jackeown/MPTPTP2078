%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:29 EST 2020

% Result     : Theorem 15.43s
% Output     : CNFRefutation 15.79s
% Verified   : 
% Statistics : Number of formulae       :   31 (  41 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   49 (  81 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_39,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k2_xboole_0(A,C),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).

tff(c_869,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden('#skF_1'(A_103,B_104,C_105),B_104)
      | r2_hidden('#skF_1'(A_103,B_104,C_105),A_103)
      | r2_hidden('#skF_2'(A_103,B_104,C_105),C_105)
      | k2_xboole_0(A_103,B_104) = C_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4490,plain,(
    ! [A_204,B_205] :
      ( r2_hidden('#skF_1'(A_204,B_205,B_205),A_204)
      | r2_hidden('#skF_2'(A_204,B_205,B_205),B_205)
      | k2_xboole_0(A_204,B_205) = B_205 ) ),
    inference(resolution,[status(thm)],[c_869,c_16])).

tff(c_636,plain,(
    ! [A_95,B_96,C_97] :
      ( r2_hidden('#skF_1'(A_95,B_96,C_97),B_96)
      | r2_hidden('#skF_1'(A_95,B_96,C_97),A_95)
      | ~ r2_hidden('#skF_2'(A_95,B_96,C_97),B_96)
      | k2_xboole_0(A_95,B_96) = C_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_697,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_1'(A_95,B_96,B_96),A_95)
      | ~ r2_hidden('#skF_2'(A_95,B_96,B_96),B_96)
      | k2_xboole_0(A_95,B_96) = B_96 ) ),
    inference(resolution,[status(thm)],[c_636,c_8])).

tff(c_4648,plain,(
    ! [A_204,B_205] :
      ( r2_hidden('#skF_1'(A_204,B_205,B_205),A_204)
      | k2_xboole_0(A_204,B_205) = B_205 ) ),
    inference(resolution,[status(thm)],[c_4490,c_697])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_295,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r2_hidden('#skF_1'(A_65,B_66,C_67),C_67)
      | r2_hidden('#skF_2'(A_65,B_66,C_67),C_67)
      | k2_xboole_0(A_65,B_66) = C_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_19094,plain,(
    ! [A_475,B_476,A_477,B_478] :
      ( r2_hidden('#skF_2'(A_475,B_476,k2_xboole_0(A_477,B_478)),k2_xboole_0(A_477,B_478))
      | k2_xboole_0(A_477,B_478) = k2_xboole_0(A_475,B_476)
      | ~ r2_hidden('#skF_1'(A_475,B_476,k2_xboole_0(A_477,B_478)),B_478) ) ),
    inference(resolution,[status(thm)],[c_4,c_295])).

tff(c_102,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r2_hidden('#skF_1'(A_35,B_36,C_37),C_37)
      | ~ r2_hidden('#skF_2'(A_35,B_36,C_37),B_36)
      | k2_xboole_0(A_35,B_36) = C_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_121,plain,(
    ! [A_35,B_36,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_35,B_36,k2_xboole_0(A_1,B_2)),B_36)
      | k2_xboole_0(A_35,B_36) = k2_xboole_0(A_1,B_2)
      | ~ r2_hidden('#skF_1'(A_35,B_36,k2_xboole_0(A_1,B_2)),B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_33594,plain,(
    ! [A_628,A_629,B_630] :
      ( k2_xboole_0(A_628,k2_xboole_0(A_629,B_630)) = k2_xboole_0(A_629,B_630)
      | ~ r2_hidden('#skF_1'(A_628,k2_xboole_0(A_629,B_630),k2_xboole_0(A_629,B_630)),B_630) ) ),
    inference(resolution,[status(thm)],[c_19094,c_121])).

tff(c_33963,plain,(
    ! [A_204,A_629] : k2_xboole_0(A_204,k2_xboole_0(A_629,A_204)) = k2_xboole_0(A_629,A_204) ),
    inference(resolution,[status(thm)],[c_4648,c_33594])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] : k2_xboole_0(k2_xboole_0(A_7,B_8),C_9) = k2_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    k2_xboole_0(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_5')) != k2_xboole_0(k2_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_23,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_5'))) != k2_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_34017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33963,c_23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:23:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.43/7.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.43/7.17  
% 15.43/7.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.43/7.17  %$ r2_hidden > k2_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 15.43/7.17  
% 15.43/7.17  %Foreground sorts:
% 15.43/7.17  
% 15.43/7.17  
% 15.43/7.17  %Background operators:
% 15.43/7.17  
% 15.43/7.17  
% 15.43/7.17  %Foreground operators:
% 15.43/7.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.43/7.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.43/7.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.43/7.17  tff('#skF_5', type, '#skF_5': $i).
% 15.43/7.17  tff('#skF_3', type, '#skF_3': $i).
% 15.43/7.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.43/7.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.43/7.17  tff('#skF_4', type, '#skF_4': $i).
% 15.43/7.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.43/7.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.43/7.17  
% 15.79/7.18  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 15.79/7.18  tff(f_36, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 15.79/7.18  tff(f_39, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_1)).
% 15.79/7.18  tff(c_869, plain, (![A_103, B_104, C_105]: (r2_hidden('#skF_1'(A_103, B_104, C_105), B_104) | r2_hidden('#skF_1'(A_103, B_104, C_105), A_103) | r2_hidden('#skF_2'(A_103, B_104, C_105), C_105) | k2_xboole_0(A_103, B_104)=C_105)), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.79/7.18  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.79/7.18  tff(c_4490, plain, (![A_204, B_205]: (r2_hidden('#skF_1'(A_204, B_205, B_205), A_204) | r2_hidden('#skF_2'(A_204, B_205, B_205), B_205) | k2_xboole_0(A_204, B_205)=B_205)), inference(resolution, [status(thm)], [c_869, c_16])).
% 15.79/7.18  tff(c_636, plain, (![A_95, B_96, C_97]: (r2_hidden('#skF_1'(A_95, B_96, C_97), B_96) | r2_hidden('#skF_1'(A_95, B_96, C_97), A_95) | ~r2_hidden('#skF_2'(A_95, B_96, C_97), B_96) | k2_xboole_0(A_95, B_96)=C_97)), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.79/7.18  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.79/7.18  tff(c_697, plain, (![A_95, B_96]: (r2_hidden('#skF_1'(A_95, B_96, B_96), A_95) | ~r2_hidden('#skF_2'(A_95, B_96, B_96), B_96) | k2_xboole_0(A_95, B_96)=B_96)), inference(resolution, [status(thm)], [c_636, c_8])).
% 15.79/7.18  tff(c_4648, plain, (![A_204, B_205]: (r2_hidden('#skF_1'(A_204, B_205, B_205), A_204) | k2_xboole_0(A_204, B_205)=B_205)), inference(resolution, [status(thm)], [c_4490, c_697])).
% 15.79/7.18  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.79/7.18  tff(c_295, plain, (![A_65, B_66, C_67]: (~r2_hidden('#skF_1'(A_65, B_66, C_67), C_67) | r2_hidden('#skF_2'(A_65, B_66, C_67), C_67) | k2_xboole_0(A_65, B_66)=C_67)), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.79/7.18  tff(c_19094, plain, (![A_475, B_476, A_477, B_478]: (r2_hidden('#skF_2'(A_475, B_476, k2_xboole_0(A_477, B_478)), k2_xboole_0(A_477, B_478)) | k2_xboole_0(A_477, B_478)=k2_xboole_0(A_475, B_476) | ~r2_hidden('#skF_1'(A_475, B_476, k2_xboole_0(A_477, B_478)), B_478))), inference(resolution, [status(thm)], [c_4, c_295])).
% 15.79/7.18  tff(c_102, plain, (![A_35, B_36, C_37]: (~r2_hidden('#skF_1'(A_35, B_36, C_37), C_37) | ~r2_hidden('#skF_2'(A_35, B_36, C_37), B_36) | k2_xboole_0(A_35, B_36)=C_37)), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.79/7.18  tff(c_121, plain, (![A_35, B_36, A_1, B_2]: (~r2_hidden('#skF_2'(A_35, B_36, k2_xboole_0(A_1, B_2)), B_36) | k2_xboole_0(A_35, B_36)=k2_xboole_0(A_1, B_2) | ~r2_hidden('#skF_1'(A_35, B_36, k2_xboole_0(A_1, B_2)), B_2))), inference(resolution, [status(thm)], [c_4, c_102])).
% 15.79/7.18  tff(c_33594, plain, (![A_628, A_629, B_630]: (k2_xboole_0(A_628, k2_xboole_0(A_629, B_630))=k2_xboole_0(A_629, B_630) | ~r2_hidden('#skF_1'(A_628, k2_xboole_0(A_629, B_630), k2_xboole_0(A_629, B_630)), B_630))), inference(resolution, [status(thm)], [c_19094, c_121])).
% 15.79/7.18  tff(c_33963, plain, (![A_204, A_629]: (k2_xboole_0(A_204, k2_xboole_0(A_629, A_204))=k2_xboole_0(A_629, A_204))), inference(resolution, [status(thm)], [c_4648, c_33594])).
% 15.79/7.18  tff(c_20, plain, (![A_7, B_8, C_9]: (k2_xboole_0(k2_xboole_0(A_7, B_8), C_9)=k2_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.79/7.18  tff(c_22, plain, (k2_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_5'))!=k2_xboole_0(k2_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.79/7.18  tff(c_23, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_5')))!=k2_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 15.79/7.18  tff(c_34017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33963, c_23])).
% 15.79/7.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.79/7.18  
% 15.79/7.18  Inference rules
% 15.79/7.18  ----------------------
% 15.79/7.18  #Ref     : 0
% 15.79/7.18  #Sup     : 8051
% 15.79/7.18  #Fact    : 36
% 15.79/7.18  #Define  : 0
% 15.79/7.18  #Split   : 0
% 15.79/7.18  #Chain   : 0
% 15.79/7.18  #Close   : 0
% 15.79/7.18  
% 15.79/7.18  Ordering : KBO
% 15.79/7.18  
% 15.79/7.18  Simplification rules
% 15.79/7.18  ----------------------
% 15.79/7.18  #Subsume      : 3353
% 15.79/7.18  #Demod        : 12740
% 15.79/7.18  #Tautology    : 479
% 15.79/7.18  #SimpNegUnit  : 0
% 15.79/7.18  #BackRed      : 19
% 15.79/7.18  
% 15.79/7.18  #Partial instantiations: 0
% 15.79/7.18  #Strategies tried      : 1
% 15.79/7.18  
% 15.79/7.18  Timing (in seconds)
% 15.79/7.18  ----------------------
% 15.79/7.19  Preprocessing        : 0.26
% 15.79/7.19  Parsing              : 0.14
% 15.79/7.19  CNF conversion       : 0.02
% 15.79/7.19  Main loop            : 6.13
% 15.79/7.19  Inferencing          : 1.08
% 15.79/7.19  Reduction            : 1.90
% 15.79/7.19  Demodulation         : 1.61
% 15.79/7.19  BG Simplification    : 0.16
% 15.79/7.19  Subsumption          : 2.75
% 15.79/7.19  Abstraction          : 0.25
% 15.79/7.19  MUC search           : 0.00
% 15.79/7.19  Cooper               : 0.00
% 15.79/7.19  Total                : 6.41
% 15.79/7.19  Index Insertion      : 0.00
% 15.79/7.19  Index Deletion       : 0.00
% 15.79/7.19  Index Matching       : 0.00
% 15.79/7.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
