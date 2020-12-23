%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:23 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  49 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_8,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [B_15,A_16] :
      ( B_15 = A_16
      | ~ r1_tarski(A_16,B_15)
      | ~ v1_zfmisc_1(B_15)
      | v1_xboole_0(B_15)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17)
      | v1_xboole_0(k3_xboole_0(A_17,B_18)) ) ),
    inference(resolution,[status(thm)],[c_4,c_65])).

tff(c_10,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_77,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_10])).

tff(c_86,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_77])).

tff(c_87,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_86])).

tff(c_16,plain,(
    ! [B_11,A_12] : k3_xboole_0(B_11,A_12) = k3_xboole_0(A_12,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_31,plain,(
    ! [B_11,A_12] : r1_tarski(k3_xboole_0(B_11,A_12),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4])).

tff(c_95,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_31])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_95])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.16  
% 1.62/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.16  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.62/1.16  
% 1.62/1.16  %Foreground sorts:
% 1.62/1.16  
% 1.62/1.16  
% 1.62/1.16  %Background operators:
% 1.62/1.16  
% 1.62/1.16  
% 1.62/1.16  %Foreground operators:
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.16  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.62/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.62/1.16  
% 1.62/1.17  tff(f_54, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 1.62/1.17  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.62/1.17  tff(f_42, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 1.62/1.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.62/1.17  tff(c_8, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.17  tff(c_14, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.17  tff(c_12, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.17  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.17  tff(c_65, plain, (![B_15, A_16]: (B_15=A_16 | ~r1_tarski(A_16, B_15) | ~v1_zfmisc_1(B_15) | v1_xboole_0(B_15) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.17  tff(c_74, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17) | v1_xboole_0(k3_xboole_0(A_17, B_18)))), inference(resolution, [status(thm)], [c_4, c_65])).
% 1.62/1.17  tff(c_10, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.17  tff(c_77, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_10])).
% 1.62/1.17  tff(c_86, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_77])).
% 1.62/1.17  tff(c_87, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_14, c_86])).
% 1.62/1.17  tff(c_16, plain, (![B_11, A_12]: (k3_xboole_0(B_11, A_12)=k3_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.17  tff(c_31, plain, (![B_11, A_12]: (r1_tarski(k3_xboole_0(B_11, A_12), A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4])).
% 1.62/1.17  tff(c_95, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_87, c_31])).
% 1.62/1.17  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_95])).
% 1.62/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.17  
% 1.62/1.17  Inference rules
% 1.62/1.17  ----------------------
% 1.62/1.17  #Ref     : 0
% 1.62/1.17  #Sup     : 22
% 1.62/1.17  #Fact    : 0
% 1.62/1.17  #Define  : 0
% 1.62/1.17  #Split   : 0
% 1.62/1.17  #Chain   : 0
% 1.62/1.17  #Close   : 0
% 1.62/1.17  
% 1.62/1.17  Ordering : KBO
% 1.62/1.17  
% 1.62/1.17  Simplification rules
% 1.62/1.17  ----------------------
% 1.62/1.17  #Subsume      : 1
% 1.62/1.17  #Demod        : 7
% 1.62/1.17  #Tautology    : 13
% 1.62/1.17  #SimpNegUnit  : 3
% 1.62/1.17  #BackRed      : 1
% 1.62/1.17  
% 1.62/1.17  #Partial instantiations: 0
% 1.62/1.17  #Strategies tried      : 1
% 1.62/1.17  
% 1.62/1.17  Timing (in seconds)
% 1.62/1.17  ----------------------
% 1.62/1.17  Preprocessing        : 0.27
% 1.62/1.17  Parsing              : 0.15
% 1.62/1.17  CNF conversion       : 0.02
% 1.62/1.17  Main loop            : 0.11
% 1.79/1.17  Inferencing          : 0.04
% 1.79/1.17  Reduction            : 0.04
% 1.79/1.17  Demodulation         : 0.03
% 1.79/1.17  BG Simplification    : 0.01
% 1.79/1.17  Subsumption          : 0.02
% 1.79/1.17  Abstraction          : 0.00
% 1.79/1.17  MUC search           : 0.00
% 1.79/1.17  Cooper               : 0.00
% 1.79/1.17  Total                : 0.40
% 1.79/1.17  Index Insertion      : 0.00
% 1.79/1.17  Index Deletion       : 0.00
% 1.79/1.17  Index Matching       : 0.00
% 1.79/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
