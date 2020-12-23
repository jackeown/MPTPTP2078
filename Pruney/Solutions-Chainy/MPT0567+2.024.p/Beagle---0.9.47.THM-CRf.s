%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:17 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  38 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_26,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [A_37,B_38,C_39] :
      ( r2_hidden('#skF_2'(A_37,B_38,C_39),B_38)
      | ~ r2_hidden(A_37,k10_relat_1(C_39,B_38))
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ! [A_20,B_21] : ~ r2_hidden(A_20,k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_52])).

tff(c_140,plain,(
    ! [A_42,C_43] :
      ( ~ r2_hidden(A_42,k10_relat_1(C_43,k1_xboole_0))
      | ~ v1_relat_1(C_43) ) ),
    inference(resolution,[status(thm)],[c_120,c_55])).

tff(c_156,plain,(
    ! [C_44,B_45] :
      ( ~ v1_relat_1(C_44)
      | r1_tarski(k10_relat_1(C_44,k1_xboole_0),B_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_170,plain,(
    ! [C_49] :
      ( k10_relat_1(C_49,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_49) ) ),
    inference(resolution,[status(thm)],[c_156,c_8])).

tff(c_173,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_170])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.63/1.15  
% 1.63/1.15  %Foreground sorts:
% 1.63/1.15  
% 1.63/1.15  
% 1.63/1.15  %Background operators:
% 1.63/1.15  
% 1.63/1.15  
% 1.63/1.15  %Foreground operators:
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.63/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.63/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.63/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.63/1.15  
% 1.84/1.16  tff(f_61, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.84/1.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.84/1.16  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.84/1.16  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.84/1.16  tff(f_45, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.84/1.16  tff(f_36, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.84/1.16  tff(c_26, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.84/1.16  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.84/1.16  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.84/1.16  tff(c_120, plain, (![A_37, B_38, C_39]: (r2_hidden('#skF_2'(A_37, B_38, C_39), B_38) | ~r2_hidden(A_37, k10_relat_1(C_39, B_38)) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.16  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.84/1.16  tff(c_52, plain, (![A_20, B_21]: (~r2_hidden(A_20, k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.84/1.16  tff(c_55, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_52])).
% 1.84/1.16  tff(c_140, plain, (![A_42, C_43]: (~r2_hidden(A_42, k10_relat_1(C_43, k1_xboole_0)) | ~v1_relat_1(C_43))), inference(resolution, [status(thm)], [c_120, c_55])).
% 1.84/1.16  tff(c_156, plain, (![C_44, B_45]: (~v1_relat_1(C_44) | r1_tarski(k10_relat_1(C_44, k1_xboole_0), B_45))), inference(resolution, [status(thm)], [c_6, c_140])).
% 1.84/1.16  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.84/1.16  tff(c_170, plain, (![C_49]: (k10_relat_1(C_49, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_49))), inference(resolution, [status(thm)], [c_156, c_8])).
% 1.84/1.16  tff(c_173, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_170])).
% 1.84/1.16  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_173])).
% 1.84/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.16  
% 1.84/1.16  Inference rules
% 1.84/1.16  ----------------------
% 1.84/1.16  #Ref     : 0
% 1.84/1.16  #Sup     : 30
% 1.84/1.16  #Fact    : 0
% 1.84/1.16  #Define  : 0
% 1.84/1.16  #Split   : 0
% 1.84/1.16  #Chain   : 0
% 1.84/1.16  #Close   : 0
% 1.84/1.16  
% 1.84/1.16  Ordering : KBO
% 1.84/1.16  
% 1.84/1.16  Simplification rules
% 1.84/1.16  ----------------------
% 1.84/1.16  #Subsume      : 2
% 1.84/1.16  #Demod        : 2
% 1.84/1.16  #Tautology    : 13
% 1.84/1.16  #SimpNegUnit  : 1
% 1.84/1.16  #BackRed      : 0
% 1.84/1.16  
% 1.84/1.16  #Partial instantiations: 0
% 1.84/1.16  #Strategies tried      : 1
% 1.84/1.16  
% 1.84/1.16  Timing (in seconds)
% 1.84/1.16  ----------------------
% 1.84/1.17  Preprocessing        : 0.28
% 1.84/1.17  Parsing              : 0.15
% 1.84/1.17  CNF conversion       : 0.02
% 1.84/1.17  Main loop            : 0.14
% 1.84/1.17  Inferencing          : 0.06
% 1.84/1.17  Reduction            : 0.04
% 1.84/1.17  Demodulation         : 0.03
% 1.84/1.17  BG Simplification    : 0.01
% 1.84/1.17  Subsumption          : 0.03
% 1.84/1.17  Abstraction          : 0.01
% 1.84/1.17  MUC search           : 0.00
% 1.84/1.17  Cooper               : 0.00
% 1.84/1.17  Total                : 0.44
% 1.84/1.17  Index Insertion      : 0.00
% 1.84/1.17  Index Deletion       : 0.00
% 1.84/1.17  Index Matching       : 0.00
% 1.84/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
