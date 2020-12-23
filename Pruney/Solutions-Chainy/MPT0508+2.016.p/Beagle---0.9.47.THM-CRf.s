%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:56 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  69 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [B_15,A_14,C_17] :
      ( r1_tarski(k7_relat_1(B_15,A_14),k7_relat_1(C_17,A_14))
      | ~ r1_tarski(B_15,C_17)
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,(
    ! [C_35,A_36,B_37] :
      ( r1_tarski(k7_relat_1(C_35,A_36),k7_relat_1(C_35,B_37))
      | ~ r1_tarski(A_36,B_37)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_379,plain,(
    ! [C_76,A_77,B_78] :
      ( k2_xboole_0(k7_relat_1(C_76,A_77),k7_relat_1(C_76,B_78)) = k7_relat_1(C_76,B_78)
      | ~ r1_tarski(A_77,B_78)
      | ~ v1_relat_1(C_76) ) ),
    inference(resolution,[status(thm)],[c_74,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_566,plain,(
    ! [C_92,A_93,C_94,B_95] :
      ( r1_tarski(k7_relat_1(C_92,A_93),C_94)
      | ~ r1_tarski(k7_relat_1(C_92,B_95),C_94)
      | ~ r1_tarski(A_93,B_95)
      | ~ v1_relat_1(C_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_2])).

tff(c_1724,plain,(
    ! [B_188,A_189,C_190,A_191] :
      ( r1_tarski(k7_relat_1(B_188,A_189),k7_relat_1(C_190,A_191))
      | ~ r1_tarski(A_189,A_191)
      | ~ r1_tarski(B_188,C_190)
      | ~ v1_relat_1(C_190)
      | ~ v1_relat_1(B_188) ) ),
    inference(resolution,[status(thm)],[c_12,c_566])).

tff(c_16,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1747,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1724,c_16])).

tff(c_1770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_18,c_1747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.68  
% 3.82/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.68  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.82/1.68  
% 3.82/1.68  %Foreground sorts:
% 3.82/1.68  
% 3.82/1.68  
% 3.82/1.68  %Background operators:
% 3.82/1.68  
% 3.82/1.68  
% 3.82/1.68  %Foreground operators:
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.82/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.82/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.82/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.82/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.82/1.68  
% 3.82/1.69  tff(f_74, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 3.82/1.69  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 3.82/1.69  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_relat_1)).
% 3.82/1.69  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.82/1.69  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.82/1.69  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.69  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.69  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.69  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.69  tff(c_12, plain, (![B_15, A_14, C_17]: (r1_tarski(k7_relat_1(B_15, A_14), k7_relat_1(C_17, A_14)) | ~r1_tarski(B_15, C_17) | ~v1_relat_1(C_17) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.82/1.69  tff(c_74, plain, (![C_35, A_36, B_37]: (r1_tarski(k7_relat_1(C_35, A_36), k7_relat_1(C_35, B_37)) | ~r1_tarski(A_36, B_37) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.82/1.69  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/1.69  tff(c_379, plain, (![C_76, A_77, B_78]: (k2_xboole_0(k7_relat_1(C_76, A_77), k7_relat_1(C_76, B_78))=k7_relat_1(C_76, B_78) | ~r1_tarski(A_77, B_78) | ~v1_relat_1(C_76))), inference(resolution, [status(thm)], [c_74, c_4])).
% 3.82/1.69  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.82/1.69  tff(c_566, plain, (![C_92, A_93, C_94, B_95]: (r1_tarski(k7_relat_1(C_92, A_93), C_94) | ~r1_tarski(k7_relat_1(C_92, B_95), C_94) | ~r1_tarski(A_93, B_95) | ~v1_relat_1(C_92))), inference(superposition, [status(thm), theory('equality')], [c_379, c_2])).
% 3.82/1.69  tff(c_1724, plain, (![B_188, A_189, C_190, A_191]: (r1_tarski(k7_relat_1(B_188, A_189), k7_relat_1(C_190, A_191)) | ~r1_tarski(A_189, A_191) | ~r1_tarski(B_188, C_190) | ~v1_relat_1(C_190) | ~v1_relat_1(B_188))), inference(resolution, [status(thm)], [c_12, c_566])).
% 3.82/1.69  tff(c_16, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.69  tff(c_1747, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1724, c_16])).
% 3.82/1.69  tff(c_1770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_18, c_1747])).
% 3.82/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.69  
% 3.82/1.69  Inference rules
% 3.82/1.69  ----------------------
% 3.82/1.69  #Ref     : 0
% 3.82/1.69  #Sup     : 475
% 3.82/1.69  #Fact    : 0
% 3.82/1.69  #Define  : 0
% 3.82/1.69  #Split   : 7
% 3.82/1.69  #Chain   : 0
% 3.82/1.69  #Close   : 0
% 3.82/1.69  
% 3.82/1.69  Ordering : KBO
% 3.82/1.69  
% 3.82/1.69  Simplification rules
% 3.82/1.69  ----------------------
% 3.82/1.69  #Subsume      : 99
% 3.82/1.69  #Demod        : 26
% 3.82/1.69  #Tautology    : 108
% 3.82/1.69  #SimpNegUnit  : 0
% 3.82/1.69  #BackRed      : 0
% 3.82/1.69  
% 3.82/1.69  #Partial instantiations: 0
% 3.82/1.69  #Strategies tried      : 1
% 3.82/1.69  
% 3.82/1.69  Timing (in seconds)
% 3.82/1.69  ----------------------
% 4.16/1.69  Preprocessing        : 0.28
% 4.16/1.69  Parsing              : 0.16
% 4.16/1.69  CNF conversion       : 0.02
% 4.16/1.69  Main loop            : 0.67
% 4.16/1.69  Inferencing          : 0.22
% 4.16/1.69  Reduction            : 0.15
% 4.16/1.69  Demodulation         : 0.10
% 4.16/1.69  BG Simplification    : 0.03
% 4.16/1.69  Subsumption          : 0.22
% 4.16/1.69  Abstraction          : 0.03
% 4.16/1.69  MUC search           : 0.00
% 4.16/1.69  Cooper               : 0.00
% 4.16/1.69  Total                : 0.97
% 4.16/1.69  Index Insertion      : 0.00
% 4.16/1.69  Index Deletion       : 0.00
% 4.16/1.69  Index Matching       : 0.00
% 4.16/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
