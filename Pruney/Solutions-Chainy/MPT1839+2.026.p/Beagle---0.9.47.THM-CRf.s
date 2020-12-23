%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:24 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  61 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_34,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_24])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(A_47,B_46)
      | ~ v1_zfmisc_1(B_46)
      | v1_xboole_0(B_46)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_292,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ v1_zfmisc_1(A_56)
      | v1_xboole_0(A_56)
      | v1_xboole_0(k3_xboole_0(A_56,B_57)) ) ),
    inference(resolution,[status(thm)],[c_12,c_160])).

tff(c_26,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_295,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_292,c_26])).

tff(c_307,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_295])).

tff(c_308,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_307])).

tff(c_14,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_333,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_14])).

tff(c_349,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_333])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.21  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.96/1.21  
% 1.96/1.21  %Foreground sorts:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Background operators:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Foreground operators:
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.21  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.96/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.96/1.21  
% 1.96/1.22  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.96/1.22  tff(f_70, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 1.96/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.96/1.22  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.96/1.22  tff(f_58, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 1.96/1.22  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.96/1.22  tff(c_34, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | k4_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.22  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.22  tff(c_38, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_24])).
% 1.96/1.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.22  tff(c_57, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.22  tff(c_69, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_57])).
% 1.96/1.22  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.22  tff(c_28, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.22  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.22  tff(c_160, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(A_47, B_46) | ~v1_zfmisc_1(B_46) | v1_xboole_0(B_46) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.22  tff(c_292, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~v1_zfmisc_1(A_56) | v1_xboole_0(A_56) | v1_xboole_0(k3_xboole_0(A_56, B_57)))), inference(resolution, [status(thm)], [c_12, c_160])).
% 1.96/1.22  tff(c_26, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.22  tff(c_295, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_292, c_26])).
% 1.96/1.22  tff(c_307, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_295])).
% 1.96/1.22  tff(c_308, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_30, c_307])).
% 1.96/1.22  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.22  tff(c_333, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_308, c_14])).
% 1.96/1.22  tff(c_349, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_69, c_333])).
% 1.96/1.22  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_349])).
% 1.96/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  Inference rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Ref     : 0
% 1.96/1.22  #Sup     : 72
% 1.96/1.22  #Fact    : 0
% 1.96/1.22  #Define  : 0
% 1.96/1.22  #Split   : 0
% 1.96/1.22  #Chain   : 0
% 1.96/1.22  #Close   : 0
% 1.96/1.22  
% 1.96/1.22  Ordering : KBO
% 1.96/1.22  
% 1.96/1.22  Simplification rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Subsume      : 8
% 1.96/1.22  #Demod        : 52
% 1.96/1.22  #Tautology    : 48
% 1.96/1.22  #SimpNegUnit  : 4
% 1.96/1.22  #BackRed      : 1
% 1.96/1.22  
% 1.96/1.22  #Partial instantiations: 0
% 1.96/1.22  #Strategies tried      : 1
% 1.96/1.22  
% 1.96/1.22  Timing (in seconds)
% 1.96/1.22  ----------------------
% 1.96/1.22  Preprocessing        : 0.29
% 1.96/1.22  Parsing              : 0.15
% 1.96/1.22  CNF conversion       : 0.02
% 1.96/1.22  Main loop            : 0.19
% 1.96/1.22  Inferencing          : 0.08
% 1.96/1.22  Reduction            : 0.06
% 1.96/1.22  Demodulation         : 0.05
% 1.96/1.22  BG Simplification    : 0.01
% 1.96/1.22  Subsumption          : 0.03
% 1.96/1.22  Abstraction          : 0.01
% 1.96/1.22  MUC search           : 0.00
% 1.96/1.22  Cooper               : 0.00
% 1.96/1.22  Total                : 0.50
% 1.96/1.22  Index Insertion      : 0.00
% 1.96/1.22  Index Deletion       : 0.00
% 1.96/1.22  Index Matching       : 0.00
% 1.96/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
