%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:21 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  55 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_10,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [B_21,A_22] :
      ( B_21 = A_22
      | ~ r1_tarski(A_22,B_21)
      | ~ v1_zfmisc_1(B_21)
      | v1_xboole_0(B_21)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_148,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ v1_zfmisc_1(A_25)
      | v1_xboole_0(A_25)
      | v1_xboole_0(k3_xboole_0(A_25,B_26)) ) ),
    inference(resolution,[status(thm)],[c_2,c_128])).

tff(c_12,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_151,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_148,c_12])).

tff(c_160,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_151])).

tff(c_161,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_160])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [B_17,A_18] : k1_setfam_1(k2_tarski(B_17,A_18)) = k3_xboole_0(A_18,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_51])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [B_19,A_20] : k3_xboole_0(B_19,A_20) = k3_xboole_0(A_20,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6])).

tff(c_104,plain,(
    ! [B_19,A_20] : r1_tarski(k3_xboole_0(B_19,A_20),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_2])).

tff(c_169,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_104])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.15  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_1
% 1.67/1.15  
% 1.67/1.15  %Foreground sorts:
% 1.67/1.15  
% 1.67/1.15  
% 1.67/1.15  %Background operators:
% 1.67/1.15  
% 1.67/1.15  
% 1.67/1.15  %Foreground operators:
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.15  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.67/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.67/1.15  
% 1.67/1.15  tff(f_56, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 1.67/1.15  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.67/1.15  tff(f_44, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 1.67/1.15  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.67/1.15  tff(f_31, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.67/1.15  tff(c_10, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.15  tff(c_16, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.15  tff(c_14, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.15  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.15  tff(c_128, plain, (![B_21, A_22]: (B_21=A_22 | ~r1_tarski(A_22, B_21) | ~v1_zfmisc_1(B_21) | v1_xboole_0(B_21) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.15  tff(c_148, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~v1_zfmisc_1(A_25) | v1_xboole_0(A_25) | v1_xboole_0(k3_xboole_0(A_25, B_26)))), inference(resolution, [status(thm)], [c_2, c_128])).
% 1.67/1.15  tff(c_12, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.15  tff(c_151, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_148, c_12])).
% 1.67/1.15  tff(c_160, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_151])).
% 1.67/1.15  tff(c_161, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_16, c_160])).
% 1.67/1.15  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.15  tff(c_51, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.15  tff(c_66, plain, (![B_17, A_18]: (k1_setfam_1(k2_tarski(B_17, A_18))=k3_xboole_0(A_18, B_17))), inference(superposition, [status(thm), theory('equality')], [c_4, c_51])).
% 1.67/1.15  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.15  tff(c_89, plain, (![B_19, A_20]: (k3_xboole_0(B_19, A_20)=k3_xboole_0(A_20, B_19))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6])).
% 1.67/1.15  tff(c_104, plain, (![B_19, A_20]: (r1_tarski(k3_xboole_0(B_19, A_20), A_20))), inference(superposition, [status(thm), theory('equality')], [c_89, c_2])).
% 1.67/1.15  tff(c_169, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_161, c_104])).
% 1.67/1.15  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_169])).
% 1.67/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.15  
% 1.67/1.15  Inference rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Ref     : 0
% 1.67/1.15  #Sup     : 40
% 1.67/1.15  #Fact    : 0
% 1.67/1.15  #Define  : 0
% 1.67/1.15  #Split   : 0
% 1.67/1.15  #Chain   : 0
% 1.67/1.15  #Close   : 0
% 1.67/1.15  
% 1.67/1.15  Ordering : KBO
% 1.67/1.15  
% 1.67/1.15  Simplification rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Subsume      : 2
% 1.67/1.15  #Demod        : 10
% 1.67/1.15  #Tautology    : 28
% 1.67/1.15  #SimpNegUnit  : 3
% 1.67/1.15  #BackRed      : 1
% 1.67/1.15  
% 1.67/1.15  #Partial instantiations: 0
% 1.67/1.15  #Strategies tried      : 1
% 1.67/1.15  
% 1.67/1.16  Timing (in seconds)
% 1.67/1.16  ----------------------
% 1.67/1.16  Preprocessing        : 0.25
% 1.67/1.16  Parsing              : 0.14
% 1.67/1.16  CNF conversion       : 0.02
% 1.67/1.16  Main loop            : 0.15
% 1.67/1.16  Inferencing          : 0.05
% 1.67/1.16  Reduction            : 0.05
% 1.67/1.16  Demodulation         : 0.05
% 1.67/1.16  BG Simplification    : 0.01
% 1.67/1.16  Subsumption          : 0.02
% 1.67/1.16  Abstraction          : 0.01
% 1.67/1.16  MUC search           : 0.00
% 1.67/1.16  Cooper               : 0.00
% 1.67/1.16  Total                : 0.42
% 1.67/1.16  Index Insertion      : 0.00
% 1.67/1.16  Index Deletion       : 0.00
% 1.67/1.16  Index Matching       : 0.00
% 1.67/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
