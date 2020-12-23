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
% DateTime   : Thu Dec  3 09:59:28 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   33 (  43 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  51 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_26,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_27,plain,(
    ! [A_23] :
      ( v1_relat_1(A_23)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_31,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_27])).

tff(c_92,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(k4_tarski('#skF_2'(A_39,B_40),'#skF_1'(A_39,B_40)),A_39)
      | r2_hidden(k4_tarski('#skF_3'(A_39,B_40),'#skF_4'(A_39,B_40)),B_40)
      | k4_relat_1(A_39) = B_40
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [A_26,B_27] : ~ r2_hidden(A_26,k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_54])).

tff(c_106,plain,(
    ! [A_39] :
      ( r2_hidden(k4_tarski('#skF_2'(A_39,k1_xboole_0),'#skF_1'(A_39,k1_xboole_0)),A_39)
      | k4_relat_1(A_39) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_92,c_57])).

tff(c_112,plain,(
    ! [A_41] :
      ( r2_hidden(k4_tarski('#skF_2'(A_41,k1_xboole_0),'#skF_1'(A_41,k1_xboole_0)),A_41)
      | k4_relat_1(A_41) = k1_xboole_0
      | ~ v1_relat_1(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_106])).

tff(c_120,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_112,c_57])).

tff(c_124,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_120])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.21  
% 1.83/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.21  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 1.83/1.21  
% 1.83/1.21  %Foreground sorts:
% 1.83/1.21  
% 1.83/1.21  
% 1.83/1.21  %Background operators:
% 1.83/1.21  
% 1.83/1.21  
% 1.83/1.21  %Foreground operators:
% 1.83/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.83/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.83/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.83/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.83/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.21  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.83/1.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.83/1.21  
% 1.83/1.22  tff(f_53, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_relat_1)).
% 1.83/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.83/1.22  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.83/1.22  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 1.83/1.22  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.83/1.22  tff(f_35, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.83/1.22  tff(c_26, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.83/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.83/1.22  tff(c_27, plain, (![A_23]: (v1_relat_1(A_23) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.83/1.22  tff(c_31, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_27])).
% 1.83/1.22  tff(c_92, plain, (![A_39, B_40]: (r2_hidden(k4_tarski('#skF_2'(A_39, B_40), '#skF_1'(A_39, B_40)), A_39) | r2_hidden(k4_tarski('#skF_3'(A_39, B_40), '#skF_4'(A_39, B_40)), B_40) | k4_relat_1(A_39)=B_40 | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.83/1.22  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.22  tff(c_54, plain, (![A_26, B_27]: (~r2_hidden(A_26, k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.22  tff(c_57, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_54])).
% 1.83/1.22  tff(c_106, plain, (![A_39]: (r2_hidden(k4_tarski('#skF_2'(A_39, k1_xboole_0), '#skF_1'(A_39, k1_xboole_0)), A_39) | k4_relat_1(A_39)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_92, c_57])).
% 1.83/1.22  tff(c_112, plain, (![A_41]: (r2_hidden(k4_tarski('#skF_2'(A_41, k1_xboole_0), '#skF_1'(A_41, k1_xboole_0)), A_41) | k4_relat_1(A_41)=k1_xboole_0 | ~v1_relat_1(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_106])).
% 1.83/1.22  tff(c_120, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_112, c_57])).
% 1.83/1.22  tff(c_124, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_31, c_120])).
% 1.83/1.22  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_124])).
% 1.83/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.22  
% 1.83/1.22  Inference rules
% 1.83/1.22  ----------------------
% 1.83/1.22  #Ref     : 0
% 1.83/1.22  #Sup     : 19
% 1.83/1.22  #Fact    : 0
% 1.83/1.22  #Define  : 0
% 1.83/1.22  #Split   : 0
% 1.83/1.22  #Chain   : 0
% 1.83/1.22  #Close   : 0
% 1.83/1.22  
% 1.83/1.22  Ordering : KBO
% 1.83/1.22  
% 1.83/1.22  Simplification rules
% 1.83/1.22  ----------------------
% 1.83/1.22  #Subsume      : 2
% 1.83/1.22  #Demod        : 3
% 1.83/1.22  #Tautology    : 9
% 1.83/1.22  #SimpNegUnit  : 1
% 1.83/1.22  #BackRed      : 0
% 1.83/1.22  
% 1.83/1.22  #Partial instantiations: 0
% 1.83/1.22  #Strategies tried      : 1
% 1.83/1.22  
% 1.83/1.22  Timing (in seconds)
% 1.83/1.22  ----------------------
% 1.83/1.22  Preprocessing        : 0.26
% 1.83/1.22  Parsing              : 0.13
% 1.83/1.22  CNF conversion       : 0.02
% 1.83/1.22  Main loop            : 0.13
% 1.83/1.22  Inferencing          : 0.06
% 1.83/1.22  Reduction            : 0.03
% 1.83/1.22  Demodulation         : 0.02
% 1.83/1.22  BG Simplification    : 0.01
% 1.83/1.22  Subsumption          : 0.03
% 1.83/1.22  Abstraction          : 0.01
% 1.83/1.22  MUC search           : 0.00
% 1.83/1.22  Cooper               : 0.00
% 1.83/1.22  Total                : 0.42
% 1.83/1.22  Index Insertion      : 0.00
% 1.83/1.22  Index Deletion       : 0.00
% 1.83/1.22  Index Matching       : 0.00
% 1.83/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
