%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:26 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   45 (  53 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  76 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_61,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | k4_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_65,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_22])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [A_23,B_24] : r1_tarski(k3_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_66,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41,c_66])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_5,B_6] : k4_xboole_0(k3_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_66])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_299,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(A_50,B_49)
      | ~ v1_zfmisc_1(B_49)
      | v1_xboole_0(B_49)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_652,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ v1_zfmisc_1(B_63)
      | v1_xboole_0(B_63)
      | v1_xboole_0(A_64)
      | k4_xboole_0(A_64,B_63) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_299])).

tff(c_654,plain,(
    ! [A_64] :
      ( A_64 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_64)
      | k4_xboole_0(A_64,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_652])).

tff(c_658,plain,(
    ! [A_65] :
      ( A_65 = '#skF_1'
      | v1_xboole_0(A_65)
      | k4_xboole_0(A_65,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_654])).

tff(c_24,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_661,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_658,c_24])).

tff(c_667,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_661])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_682,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_10])).

tff(c_693,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_682])).

tff(c_695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:03:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.47/1.35  
% 2.47/1.35  %Foreground sorts:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Background operators:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Foreground operators:
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.35  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.47/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.35  
% 2.47/1.36  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.47/1.36  tff(f_68, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 2.47/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.47/1.36  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.47/1.36  tff(f_56, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.47/1.36  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.47/1.36  tff(c_61, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | k4_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.36  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.47/1.36  tff(c_65, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_61, c_22])).
% 2.47/1.36  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.36  tff(c_38, plain, (![A_23, B_24]: (r1_tarski(k3_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.36  tff(c_41, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_38])).
% 2.47/1.36  tff(c_66, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.36  tff(c_77, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_41, c_66])).
% 2.47/1.36  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.36  tff(c_78, plain, (![A_5, B_6]: (k4_xboole_0(k3_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_66])).
% 2.47/1.36  tff(c_28, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.47/1.36  tff(c_26, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.47/1.36  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.36  tff(c_299, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(A_50, B_49) | ~v1_zfmisc_1(B_49) | v1_xboole_0(B_49) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.47/1.36  tff(c_652, plain, (![B_63, A_64]: (B_63=A_64 | ~v1_zfmisc_1(B_63) | v1_xboole_0(B_63) | v1_xboole_0(A_64) | k4_xboole_0(A_64, B_63)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_299])).
% 2.47/1.36  tff(c_654, plain, (![A_64]: (A_64='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_64) | k4_xboole_0(A_64, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_652])).
% 2.47/1.36  tff(c_658, plain, (![A_65]: (A_65='#skF_1' | v1_xboole_0(A_65) | k4_xboole_0(A_65, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_28, c_654])).
% 2.47/1.36  tff(c_24, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.47/1.36  tff(c_661, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_658, c_24])).
% 2.47/1.36  tff(c_667, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_661])).
% 2.47/1.36  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.36  tff(c_682, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_667, c_10])).
% 2.47/1.36  tff(c_693, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_77, c_682])).
% 2.47/1.36  tff(c_695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_693])).
% 2.47/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  Inference rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Ref     : 0
% 2.47/1.36  #Sup     : 157
% 2.47/1.36  #Fact    : 0
% 2.47/1.36  #Define  : 0
% 2.47/1.36  #Split   : 0
% 2.47/1.36  #Chain   : 0
% 2.47/1.36  #Close   : 0
% 2.47/1.36  
% 2.47/1.36  Ordering : KBO
% 2.47/1.36  
% 2.47/1.36  Simplification rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Subsume      : 1
% 2.47/1.36  #Demod        : 131
% 2.47/1.36  #Tautology    : 131
% 2.47/1.36  #SimpNegUnit  : 2
% 2.47/1.36  #BackRed      : 1
% 2.47/1.36  
% 2.47/1.36  #Partial instantiations: 0
% 2.47/1.36  #Strategies tried      : 1
% 2.47/1.36  
% 2.47/1.36  Timing (in seconds)
% 2.47/1.36  ----------------------
% 2.55/1.37  Preprocessing        : 0.30
% 2.55/1.37  Parsing              : 0.17
% 2.55/1.37  CNF conversion       : 0.02
% 2.55/1.37  Main loop            : 0.24
% 2.55/1.37  Inferencing          : 0.10
% 2.55/1.37  Reduction            : 0.08
% 2.55/1.37  Demodulation         : 0.06
% 2.55/1.37  BG Simplification    : 0.01
% 2.55/1.37  Subsumption          : 0.03
% 2.55/1.37  Abstraction          : 0.02
% 2.55/1.37  MUC search           : 0.00
% 2.55/1.37  Cooper               : 0.00
% 2.55/1.37  Total                : 0.57
% 2.55/1.37  Index Insertion      : 0.00
% 2.55/1.37  Index Deletion       : 0.00
% 2.55/1.37  Index Matching       : 0.00
% 2.55/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
