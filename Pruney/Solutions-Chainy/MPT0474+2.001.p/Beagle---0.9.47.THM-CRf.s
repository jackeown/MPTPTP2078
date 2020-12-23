%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:27 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   32 (  43 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_22,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_23,plain,(
    ! [A_23] :
      ( v1_relat_1(A_23)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_27,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_23])).

tff(c_69,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(k4_tarski('#skF_3'(A_43,B_44),'#skF_2'(A_43,B_44)),A_43)
      | r2_hidden(k4_tarski('#skF_4'(A_43,B_44),'#skF_5'(A_43,B_44)),B_44)
      | k4_relat_1(A_43) = B_44
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_45,B_46] :
      ( ~ v1_xboole_0(A_45)
      | r2_hidden(k4_tarski('#skF_4'(A_45,B_46),'#skF_5'(A_45,B_46)),B_46)
      | k4_relat_1(A_45) = B_46
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_110,plain,(
    ! [B_47,A_48] :
      ( ~ v1_xboole_0(B_47)
      | ~ v1_xboole_0(A_48)
      | k4_relat_1(A_48) = B_47
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_112,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(A_48)
      | k4_relat_1(A_48) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_122,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(A_51)
      | k4_relat_1(A_51) = k1_xboole_0
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_112])).

tff(c_125,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_128,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_125])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 1.81/1.19  
% 1.81/1.19  %Foreground sorts:
% 1.81/1.19  
% 1.81/1.19  
% 1.81/1.19  %Background operators:
% 1.81/1.19  
% 1.81/1.19  
% 1.81/1.19  %Foreground operators:
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.81/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.81/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.81/1.19  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.81/1.19  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.81/1.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.81/1.19  
% 1.81/1.20  tff(f_50, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 1.81/1.20  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.81/1.20  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.81/1.20  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_1)).
% 1.81/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.81/1.20  tff(c_22, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.20  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.20  tff(c_23, plain, (![A_23]: (v1_relat_1(A_23) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.81/1.20  tff(c_27, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_23])).
% 1.81/1.20  tff(c_69, plain, (![A_43, B_44]: (r2_hidden(k4_tarski('#skF_3'(A_43, B_44), '#skF_2'(A_43, B_44)), A_43) | r2_hidden(k4_tarski('#skF_4'(A_43, B_44), '#skF_5'(A_43, B_44)), B_44) | k4_relat_1(A_43)=B_44 | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.20  tff(c_96, plain, (![A_45, B_46]: (~v1_xboole_0(A_45) | r2_hidden(k4_tarski('#skF_4'(A_45, B_46), '#skF_5'(A_45, B_46)), B_46) | k4_relat_1(A_45)=B_46 | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_69, c_2])).
% 1.81/1.20  tff(c_110, plain, (![B_47, A_48]: (~v1_xboole_0(B_47) | ~v1_xboole_0(A_48) | k4_relat_1(A_48)=B_47 | ~v1_relat_1(B_47) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_96, c_2])).
% 1.81/1.20  tff(c_112, plain, (![A_48]: (~v1_xboole_0(A_48) | k4_relat_1(A_48)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_6, c_110])).
% 1.81/1.20  tff(c_122, plain, (![A_51]: (~v1_xboole_0(A_51) | k4_relat_1(A_51)=k1_xboole_0 | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_112])).
% 1.81/1.20  tff(c_125, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_122])).
% 1.81/1.20  tff(c_128, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_27, c_125])).
% 1.81/1.20  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_128])).
% 1.81/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  Inference rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Ref     : 0
% 1.81/1.20  #Sup     : 21
% 1.81/1.20  #Fact    : 0
% 1.81/1.20  #Define  : 0
% 1.81/1.20  #Split   : 0
% 1.81/1.20  #Chain   : 0
% 1.81/1.20  #Close   : 0
% 1.81/1.20  
% 1.81/1.20  Ordering : KBO
% 1.81/1.20  
% 1.81/1.20  Simplification rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Subsume      : 2
% 1.81/1.20  #Demod        : 2
% 1.81/1.20  #Tautology    : 2
% 1.81/1.20  #SimpNegUnit  : 1
% 1.81/1.20  #BackRed      : 0
% 1.81/1.20  
% 1.81/1.20  #Partial instantiations: 0
% 1.81/1.20  #Strategies tried      : 1
% 1.81/1.20  
% 1.81/1.20  Timing (in seconds)
% 1.81/1.20  ----------------------
% 1.81/1.20  Preprocessing        : 0.26
% 1.81/1.20  Parsing              : 0.14
% 1.81/1.20  CNF conversion       : 0.02
% 1.81/1.20  Main loop            : 0.17
% 1.81/1.20  Inferencing          : 0.07
% 1.81/1.20  Reduction            : 0.04
% 1.81/1.20  Demodulation         : 0.03
% 1.81/1.20  BG Simplification    : 0.01
% 1.81/1.20  Subsumption          : 0.04
% 1.81/1.20  Abstraction          : 0.01
% 1.81/1.20  MUC search           : 0.00
% 1.81/1.20  Cooper               : 0.00
% 1.81/1.20  Total                : 0.46
% 1.81/1.20  Index Insertion      : 0.00
% 1.81/1.20  Index Deletion       : 0.00
% 1.81/1.20  Index Matching       : 0.00
% 1.81/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
