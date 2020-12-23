%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:28 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   38 (  56 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  67 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(f_57,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_28,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_56,plain,(
    ! [A_27] :
      ( k1_xboole_0 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_60,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_56])).

tff(c_29,plain,(
    ! [A_24] :
      ( v1_relat_1(A_24)
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_33,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_29])).

tff(c_61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_33])).

tff(c_115,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(k4_tarski('#skF_2'(A_41,B_42),'#skF_1'(A_41,B_42)),A_41)
      | r2_hidden(k4_tarski('#skF_3'(A_41,B_42),'#skF_4'(A_41,B_42)),B_42)
      | k4_relat_1(A_41) = B_42
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67,plain,(
    ! [A_28,B_29] : ~ r2_hidden(A_28,k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [A_2] : ~ r2_hidden(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_129,plain,(
    ! [A_41] :
      ( r2_hidden(k4_tarski('#skF_2'(A_41,k1_xboole_0),'#skF_1'(A_41,k1_xboole_0)),A_41)
      | k4_relat_1(A_41) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_115,c_73])).

tff(c_135,plain,(
    ! [A_43] :
      ( r2_hidden(k4_tarski('#skF_2'(A_43,k1_xboole_0),'#skF_1'(A_43,k1_xboole_0)),A_43)
      | k4_relat_1(A_43) = k1_xboole_0
      | ~ v1_relat_1(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_129])).

tff(c_143,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_135,c_73])).

tff(c_147,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_143])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.23  
% 1.91/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.23  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 1.91/1.23  
% 1.91/1.23  %Foreground sorts:
% 1.91/1.23  
% 1.91/1.23  
% 1.91/1.23  %Background operators:
% 1.91/1.23  
% 1.91/1.23  
% 1.91/1.23  %Foreground operators:
% 1.91/1.23  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.91/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.23  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.91/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.91/1.23  
% 1.93/1.24  tff(f_57, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 1.93/1.24  tff(f_26, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 1.93/1.24  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.93/1.24  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.93/1.24  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_1)).
% 1.93/1.24  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.93/1.24  tff(f_39, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.93/1.24  tff(c_28, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.24  tff(c_2, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.93/1.24  tff(c_56, plain, (![A_27]: (k1_xboole_0=A_27 | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.93/1.24  tff(c_60, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_56])).
% 1.93/1.24  tff(c_29, plain, (![A_24]: (v1_relat_1(A_24) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.93/1.24  tff(c_33, plain, (v1_relat_1(o_0_0_xboole_0)), inference(resolution, [status(thm)], [c_2, c_29])).
% 1.93/1.24  tff(c_61, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_33])).
% 1.93/1.24  tff(c_115, plain, (![A_41, B_42]: (r2_hidden(k4_tarski('#skF_2'(A_41, B_42), '#skF_1'(A_41, B_42)), A_41) | r2_hidden(k4_tarski('#skF_3'(A_41, B_42), '#skF_4'(A_41, B_42)), B_42) | k4_relat_1(A_41)=B_42 | ~v1_relat_1(B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.24  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.24  tff(c_67, plain, (![A_28, B_29]: (~r2_hidden(A_28, k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.24  tff(c_73, plain, (![A_2]: (~r2_hidden(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_67])).
% 1.93/1.24  tff(c_129, plain, (![A_41]: (r2_hidden(k4_tarski('#skF_2'(A_41, k1_xboole_0), '#skF_1'(A_41, k1_xboole_0)), A_41) | k4_relat_1(A_41)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_115, c_73])).
% 1.93/1.24  tff(c_135, plain, (![A_43]: (r2_hidden(k4_tarski('#skF_2'(A_43, k1_xboole_0), '#skF_1'(A_43, k1_xboole_0)), A_43) | k4_relat_1(A_43)=k1_xboole_0 | ~v1_relat_1(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_129])).
% 1.93/1.24  tff(c_143, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_135, c_73])).
% 1.93/1.24  tff(c_147, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_61, c_143])).
% 1.93/1.24  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_147])).
% 1.93/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  Inference rules
% 1.93/1.24  ----------------------
% 1.93/1.24  #Ref     : 0
% 1.93/1.24  #Sup     : 24
% 1.93/1.24  #Fact    : 0
% 1.93/1.24  #Define  : 0
% 1.93/1.24  #Split   : 0
% 1.93/1.24  #Chain   : 0
% 1.93/1.24  #Close   : 0
% 1.93/1.24  
% 1.93/1.24  Ordering : KBO
% 1.93/1.24  
% 1.93/1.24  Simplification rules
% 1.93/1.24  ----------------------
% 1.93/1.24  #Subsume      : 2
% 1.93/1.24  #Demod        : 6
% 1.93/1.24  #Tautology    : 13
% 1.93/1.24  #SimpNegUnit  : 1
% 1.93/1.24  #BackRed      : 2
% 1.93/1.24  
% 1.93/1.24  #Partial instantiations: 0
% 1.93/1.24  #Strategies tried      : 1
% 1.93/1.24  
% 1.93/1.24  Timing (in seconds)
% 1.93/1.24  ----------------------
% 1.93/1.24  Preprocessing        : 0.29
% 1.93/1.24  Parsing              : 0.16
% 1.93/1.24  CNF conversion       : 0.02
% 1.93/1.24  Main loop            : 0.14
% 1.93/1.24  Inferencing          : 0.06
% 1.93/1.24  Reduction            : 0.04
% 1.93/1.24  Demodulation         : 0.03
% 1.93/1.24  BG Simplification    : 0.01
% 1.93/1.24  Subsumption          : 0.03
% 1.93/1.24  Abstraction          : 0.01
% 1.93/1.24  MUC search           : 0.00
% 1.93/1.24  Cooper               : 0.00
% 1.93/1.24  Total                : 0.46
% 1.93/1.24  Index Insertion      : 0.00
% 1.93/1.24  Index Deletion       : 0.00
% 1.93/1.24  Index Matching       : 0.00
% 1.93/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
