%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:26 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  60 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_150,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | k4_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_158,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_150,c_20])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    ! [A_41,B_42] : k5_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_171,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k5_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_159])).

tff(c_175,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_171])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ r1_tarski(A_45,B_44)
      | ~ v1_zfmisc_1(B_44)
      | v1_xboole_0(B_44)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_222,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ v1_zfmisc_1(A_49)
      | v1_xboole_0(A_49)
      | v1_xboole_0(k3_xboole_0(A_49,B_50)) ) ),
    inference(resolution,[status(thm)],[c_10,c_184])).

tff(c_22,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_225,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_222,c_22])).

tff(c_234,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_225])).

tff(c_235,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_234])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_245,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_8])).

tff(c_263,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_245])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:05:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.20  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.90/1.20  
% 1.90/1.20  %Foreground sorts:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Background operators:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Foreground operators:
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.90/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.20  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.90/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.20  
% 1.98/1.21  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.98/1.21  tff(f_70, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 1.98/1.21  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.98/1.21  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.98/1.21  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.98/1.21  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.98/1.21  tff(f_58, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 1.98/1.21  tff(c_150, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | k4_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.21  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.21  tff(c_158, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_150, c_20])).
% 1.98/1.21  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.21  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k2_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.21  tff(c_159, plain, (![A_41, B_42]: (k5_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.98/1.21  tff(c_171, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k5_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_159])).
% 1.98/1.21  tff(c_175, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_171])).
% 1.98/1.21  tff(c_26, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.21  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.21  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.21  tff(c_184, plain, (![B_44, A_45]: (B_44=A_45 | ~r1_tarski(A_45, B_44) | ~v1_zfmisc_1(B_44) | v1_xboole_0(B_44) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.21  tff(c_222, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~v1_zfmisc_1(A_49) | v1_xboole_0(A_49) | v1_xboole_0(k3_xboole_0(A_49, B_50)))), inference(resolution, [status(thm)], [c_10, c_184])).
% 1.98/1.21  tff(c_22, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.21  tff(c_225, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_222, c_22])).
% 1.98/1.21  tff(c_234, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_225])).
% 1.98/1.21  tff(c_235, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_26, c_234])).
% 1.98/1.21  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.98/1.21  tff(c_245, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_235, c_8])).
% 1.98/1.21  tff(c_263, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_175, c_245])).
% 1.98/1.21  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_263])).
% 1.98/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  Inference rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Ref     : 0
% 1.98/1.21  #Sup     : 57
% 1.98/1.21  #Fact    : 0
% 1.98/1.21  #Define  : 0
% 1.98/1.21  #Split   : 0
% 1.98/1.21  #Chain   : 0
% 1.98/1.21  #Close   : 0
% 1.98/1.21  
% 1.98/1.21  Ordering : KBO
% 1.98/1.21  
% 1.98/1.21  Simplification rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Subsume      : 2
% 1.98/1.21  #Demod        : 19
% 1.98/1.21  #Tautology    : 36
% 1.98/1.21  #SimpNegUnit  : 4
% 1.98/1.21  #BackRed      : 1
% 1.98/1.21  
% 1.98/1.21  #Partial instantiations: 0
% 1.98/1.22  #Strategies tried      : 1
% 1.98/1.22  
% 1.98/1.22  Timing (in seconds)
% 1.98/1.22  ----------------------
% 1.98/1.22  Preprocessing        : 0.28
% 1.98/1.22  Parsing              : 0.16
% 1.98/1.22  CNF conversion       : 0.02
% 1.98/1.22  Main loop            : 0.18
% 1.98/1.22  Inferencing          : 0.08
% 1.98/1.22  Reduction            : 0.05
% 1.98/1.22  Demodulation         : 0.04
% 1.98/1.22  BG Simplification    : 0.01
% 1.98/1.22  Subsumption          : 0.03
% 1.98/1.22  Abstraction          : 0.01
% 1.98/1.22  MUC search           : 0.00
% 1.98/1.22  Cooper               : 0.00
% 1.98/1.22  Total                : 0.49
% 1.98/1.22  Index Insertion      : 0.00
% 1.98/1.22  Index Deletion       : 0.00
% 1.98/1.22  Index Matching       : 0.00
% 1.98/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
