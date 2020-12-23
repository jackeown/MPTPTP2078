%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:27 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  68 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_58,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_20])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    ! [A_5,B_6] : k4_xboole_0(k3_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(A_38,B_37)
      | ~ v1_zfmisc_1(B_37)
      | v1_xboole_0(B_37)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_101,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ v1_zfmisc_1(B_39)
      | v1_xboole_0(B_39)
      | v1_xboole_0(A_40)
      | k4_xboole_0(A_40,B_39) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_92])).

tff(c_103,plain,(
    ! [A_40] :
      ( A_40 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_40)
      | k4_xboole_0(A_40,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_101])).

tff(c_107,plain,(
    ! [A_41] :
      ( A_41 = '#skF_1'
      | v1_xboole_0(A_41)
      | k4_xboole_0(A_41,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_103])).

tff(c_22,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_110,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_107,c_22])).

tff(c_116,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_110])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_6])).

tff(c_132,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_123])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:39:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.11  
% 1.77/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.11  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.77/1.11  
% 1.77/1.11  %Foreground sorts:
% 1.77/1.11  
% 1.77/1.11  
% 1.77/1.11  %Background operators:
% 1.77/1.11  
% 1.77/1.11  
% 1.77/1.11  %Foreground operators:
% 1.77/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.77/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.77/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.11  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.77/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.77/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.77/1.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.77/1.11  
% 1.77/1.12  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.77/1.12  tff(f_66, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 1.77/1.12  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.77/1.12  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.77/1.12  tff(f_54, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 1.77/1.12  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.77/1.12  tff(c_58, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.12  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.77/1.12  tff(c_66, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_20])).
% 1.77/1.12  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.12  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.12  tff(c_53, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.12  tff(c_57, plain, (![A_5, B_6]: (k4_xboole_0(k3_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_53])).
% 1.77/1.12  tff(c_26, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.77/1.12  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.77/1.12  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.12  tff(c_92, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(A_38, B_37) | ~v1_zfmisc_1(B_37) | v1_xboole_0(B_37) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.77/1.12  tff(c_101, plain, (![B_39, A_40]: (B_39=A_40 | ~v1_zfmisc_1(B_39) | v1_xboole_0(B_39) | v1_xboole_0(A_40) | k4_xboole_0(A_40, B_39)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_92])).
% 1.77/1.12  tff(c_103, plain, (![A_40]: (A_40='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_40) | k4_xboole_0(A_40, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_101])).
% 1.77/1.12  tff(c_107, plain, (![A_41]: (A_41='#skF_1' | v1_xboole_0(A_41) | k4_xboole_0(A_41, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_26, c_103])).
% 1.77/1.12  tff(c_22, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.77/1.12  tff(c_110, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_107, c_22])).
% 1.77/1.12  tff(c_116, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_110])).
% 1.77/1.12  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.12  tff(c_123, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_116, c_6])).
% 1.77/1.12  tff(c_132, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_123])).
% 1.77/1.12  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_132])).
% 1.77/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.12  
% 1.77/1.12  Inference rules
% 1.77/1.12  ----------------------
% 1.77/1.12  #Ref     : 0
% 1.77/1.12  #Sup     : 25
% 1.77/1.12  #Fact    : 0
% 1.77/1.12  #Define  : 0
% 1.77/1.12  #Split   : 0
% 1.77/1.12  #Chain   : 0
% 1.77/1.12  #Close   : 0
% 1.77/1.12  
% 1.77/1.12  Ordering : KBO
% 1.77/1.12  
% 1.77/1.12  Simplification rules
% 1.77/1.12  ----------------------
% 1.77/1.12  #Subsume      : 1
% 1.77/1.12  #Demod        : 3
% 1.77/1.12  #Tautology    : 15
% 1.77/1.12  #SimpNegUnit  : 2
% 1.77/1.12  #BackRed      : 1
% 1.77/1.12  
% 1.77/1.12  #Partial instantiations: 0
% 1.77/1.12  #Strategies tried      : 1
% 1.77/1.12  
% 1.77/1.12  Timing (in seconds)
% 1.77/1.12  ----------------------
% 1.77/1.12  Preprocessing        : 0.27
% 1.77/1.12  Parsing              : 0.14
% 1.77/1.12  CNF conversion       : 0.02
% 1.77/1.12  Main loop            : 0.12
% 1.77/1.12  Inferencing          : 0.05
% 1.77/1.12  Reduction            : 0.03
% 1.77/1.12  Demodulation         : 0.02
% 1.77/1.12  BG Simplification    : 0.01
% 1.77/1.12  Subsumption          : 0.01
% 1.77/1.12  Abstraction          : 0.01
% 1.77/1.12  MUC search           : 0.00
% 1.77/1.12  Cooper               : 0.00
% 1.77/1.12  Total                : 0.41
% 1.77/1.12  Index Insertion      : 0.00
% 1.77/1.12  Index Deletion       : 0.00
% 1.77/1.12  Index Matching       : 0.00
% 1.77/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
