%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:23 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   37 (  45 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  66 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_257,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(A_65,B_64)
      | ~ v1_zfmisc_1(B_64)
      | v1_xboole_0(B_64)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_459,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = A_89
      | ~ v1_zfmisc_1(A_89)
      | v1_xboole_0(A_89)
      | v1_xboole_0(k3_xboole_0(A_89,B_90)) ) ),
    inference(resolution,[status(thm)],[c_14,c_257])).

tff(c_30,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_462,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | ~ v1_zfmisc_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_459,c_30])).

tff(c_465,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_462])).

tff(c_466,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_465])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [B_6] : k2_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_46])).

tff(c_158,plain,(
    ! [A_51,B_52,C_53] : r1_tarski(k2_xboole_0(k3_xboole_0(A_51,B_52),k3_xboole_0(A_51,C_53)),k2_xboole_0(B_52,C_53)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_173,plain,(
    ! [A_51,B_52] : r1_tarski(k3_xboole_0(A_51,B_52),k2_xboole_0(B_52,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_158])).

tff(c_179,plain,(
    ! [A_51,B_52] : r1_tarski(k3_xboole_0(A_51,B_52),B_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_173])).

tff(c_501,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_179])).

tff(c_534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_501])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.41  
% 2.33/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.41  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_2 > #skF_3
% 2.33/1.41  
% 2.33/1.41  %Foreground sorts:
% 2.33/1.41  
% 2.33/1.41  
% 2.33/1.41  %Background operators:
% 2.33/1.41  
% 2.33/1.41  
% 2.33/1.41  %Foreground operators:
% 2.33/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.33/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.33/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.41  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.33/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.41  
% 2.33/1.42  tff(f_81, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 2.33/1.42  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.33/1.42  tff(f_69, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.33/1.42  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.33/1.42  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.33/1.42  tff(f_49, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.33/1.42  tff(c_28, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.33/1.42  tff(c_34, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.33/1.42  tff(c_32, plain, (v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.33/1.42  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.33/1.42  tff(c_257, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(A_65, B_64) | ~v1_zfmisc_1(B_64) | v1_xboole_0(B_64) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.33/1.42  tff(c_459, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=A_89 | ~v1_zfmisc_1(A_89) | v1_xboole_0(A_89) | v1_xboole_0(k3_xboole_0(A_89, B_90)))), inference(resolution, [status(thm)], [c_14, c_257])).
% 2.33/1.42  tff(c_30, plain, (~v1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.33/1.42  tff(c_462, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2' | ~v1_zfmisc_1('#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_459, c_30])).
% 2.33/1.42  tff(c_465, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2' | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_462])).
% 2.33/1.42  tff(c_466, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_465])).
% 2.33/1.42  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.42  tff(c_46, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.42  tff(c_58, plain, (![B_6]: (k2_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_46])).
% 2.33/1.42  tff(c_158, plain, (![A_51, B_52, C_53]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_51, B_52), k3_xboole_0(A_51, C_53)), k2_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.33/1.42  tff(c_173, plain, (![A_51, B_52]: (r1_tarski(k3_xboole_0(A_51, B_52), k2_xboole_0(B_52, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_158])).
% 2.33/1.42  tff(c_179, plain, (![A_51, B_52]: (r1_tarski(k3_xboole_0(A_51, B_52), B_52))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_173])).
% 2.33/1.42  tff(c_501, plain, (r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_466, c_179])).
% 2.33/1.42  tff(c_534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_501])).
% 2.33/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.42  
% 2.33/1.42  Inference rules
% 2.33/1.42  ----------------------
% 2.33/1.42  #Ref     : 0
% 2.33/1.42  #Sup     : 111
% 2.33/1.42  #Fact    : 0
% 2.33/1.42  #Define  : 0
% 2.33/1.42  #Split   : 0
% 2.33/1.42  #Chain   : 0
% 2.33/1.42  #Close   : 0
% 2.33/1.42  
% 2.33/1.42  Ordering : KBO
% 2.33/1.42  
% 2.33/1.42  Simplification rules
% 2.33/1.42  ----------------------
% 2.33/1.42  #Subsume      : 4
% 2.33/1.42  #Demod        : 23
% 2.33/1.42  #Tautology    : 43
% 2.33/1.42  #SimpNegUnit  : 5
% 2.33/1.42  #BackRed      : 1
% 2.33/1.42  
% 2.33/1.42  #Partial instantiations: 0
% 2.33/1.42  #Strategies tried      : 1
% 2.33/1.42  
% 2.33/1.42  Timing (in seconds)
% 2.33/1.42  ----------------------
% 2.33/1.42  Preprocessing        : 0.32
% 2.33/1.42  Parsing              : 0.17
% 2.33/1.42  CNF conversion       : 0.02
% 2.33/1.42  Main loop            : 0.26
% 2.33/1.42  Inferencing          : 0.11
% 2.33/1.42  Reduction            : 0.07
% 2.33/1.42  Demodulation         : 0.05
% 2.33/1.43  BG Simplification    : 0.02
% 2.33/1.43  Subsumption          : 0.05
% 2.33/1.43  Abstraction          : 0.01
% 2.33/1.43  MUC search           : 0.00
% 2.33/1.43  Cooper               : 0.00
% 2.33/1.43  Total                : 0.61
% 2.33/1.43  Index Insertion      : 0.00
% 2.33/1.43  Index Deletion       : 0.00
% 2.33/1.43  Index Matching       : 0.00
% 2.33/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
