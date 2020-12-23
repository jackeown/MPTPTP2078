%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:34 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   47 (  88 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 ( 162 expanded)
%              Number of equality atoms :   13 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_42,plain,(
    k1_wellord1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [D_53,B_54,A_55] :
      ( r2_hidden(k4_tarski(D_53,B_54),A_55)
      | ~ r2_hidden(D_53,k1_wellord1(A_55,B_54))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [B_25,C_26,A_24] :
      ( r2_hidden(B_25,k3_relat_1(C_26))
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_102,plain,(
    ! [B_64,A_65,D_66] :
      ( r2_hidden(B_64,k3_relat_1(A_65))
      | ~ r2_hidden(D_66,k1_wellord1(A_65,B_64))
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_57,c_20])).

tff(c_112,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,k3_relat_1(A_70))
      | ~ v1_relat_1(A_70)
      | v1_xboole_0(k1_wellord1(A_70,B_69)) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_44,plain,(
    ~ r2_hidden('#skF_8',k3_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_134,plain,
    ( ~ v1_relat_1('#skF_9')
    | v1_xboole_0(k1_wellord1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_112,c_44])).

tff(c_142,plain,(
    v1_xboole_0(k1_wellord1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_134])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_407,plain,(
    ! [A_109,B_110] :
      ( r2_hidden(k4_tarski('#skF_2'(A_109,B_110),'#skF_3'(A_109,B_110)),A_109)
      | r2_hidden('#skF_4'(A_109,B_110),B_110)
      | k1_relat_1(A_109) = B_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_477,plain,(
    ! [A_111,B_112] :
      ( ~ v1_xboole_0(A_111)
      | r2_hidden('#skF_4'(A_111,B_112),B_112)
      | k1_relat_1(A_111) = B_112 ) ),
    inference(resolution,[status(thm)],[c_407,c_2])).

tff(c_531,plain,(
    ! [B_113,A_114] :
      ( ~ v1_xboole_0(B_113)
      | ~ v1_xboole_0(A_114)
      | k1_relat_1(A_114) = B_113 ) ),
    inference(resolution,[status(thm)],[c_477,c_2])).

tff(c_562,plain,(
    ! [A_115] :
      ( ~ v1_xboole_0(A_115)
      | k1_relat_1(A_115) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_531])).

tff(c_600,plain,(
    k1_relat_1(k1_wellord1('#skF_9','#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_562])).

tff(c_900,plain,(
    ! [A_121] :
      ( ~ v1_xboole_0(A_121)
      | k1_wellord1('#skF_9','#skF_8') = k1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_142,c_531])).

tff(c_924,plain,(
    k1_relat_1(k1_wellord1('#skF_9','#skF_8')) = k1_wellord1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_142,c_900])).

tff(c_939,plain,(
    k1_wellord1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_924])).

tff(c_941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.42  
% 2.48/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.42  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_4
% 2.48/1.42  
% 2.48/1.42  %Foreground sorts:
% 2.48/1.42  
% 2.48/1.42  
% 2.48/1.42  %Background operators:
% 2.48/1.42  
% 2.48/1.42  
% 2.48/1.42  %Foreground operators:
% 2.48/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.42  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.48/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.48/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.48/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.42  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.48/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.48/1.42  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.48/1.42  tff('#skF_9', type, '#skF_9': $i).
% 2.48/1.42  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.48/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.48/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.42  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.48/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.48/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.48/1.42  
% 2.83/1.43  tff(f_68, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k3_relat_1(B)) | (k1_wellord1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord1)).
% 2.83/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.83/1.43  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 2.83/1.43  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 2.83/1.43  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.83/1.43  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.83/1.43  tff(c_42, plain, (k1_wellord1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.43  tff(c_46, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.43  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.43  tff(c_57, plain, (![D_53, B_54, A_55]: (r2_hidden(k4_tarski(D_53, B_54), A_55) | ~r2_hidden(D_53, k1_wellord1(A_55, B_54)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.83/1.43  tff(c_20, plain, (![B_25, C_26, A_24]: (r2_hidden(B_25, k3_relat_1(C_26)) | ~r2_hidden(k4_tarski(A_24, B_25), C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.83/1.43  tff(c_102, plain, (![B_64, A_65, D_66]: (r2_hidden(B_64, k3_relat_1(A_65)) | ~r2_hidden(D_66, k1_wellord1(A_65, B_64)) | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_57, c_20])).
% 2.83/1.43  tff(c_112, plain, (![B_69, A_70]: (r2_hidden(B_69, k3_relat_1(A_70)) | ~v1_relat_1(A_70) | v1_xboole_0(k1_wellord1(A_70, B_69)))), inference(resolution, [status(thm)], [c_4, c_102])).
% 2.83/1.43  tff(c_44, plain, (~r2_hidden('#skF_8', k3_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.43  tff(c_134, plain, (~v1_relat_1('#skF_9') | v1_xboole_0(k1_wellord1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_112, c_44])).
% 2.83/1.43  tff(c_142, plain, (v1_xboole_0(k1_wellord1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_134])).
% 2.83/1.43  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.43  tff(c_407, plain, (![A_109, B_110]: (r2_hidden(k4_tarski('#skF_2'(A_109, B_110), '#skF_3'(A_109, B_110)), A_109) | r2_hidden('#skF_4'(A_109, B_110), B_110) | k1_relat_1(A_109)=B_110)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.83/1.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.43  tff(c_477, plain, (![A_111, B_112]: (~v1_xboole_0(A_111) | r2_hidden('#skF_4'(A_111, B_112), B_112) | k1_relat_1(A_111)=B_112)), inference(resolution, [status(thm)], [c_407, c_2])).
% 2.83/1.43  tff(c_531, plain, (![B_113, A_114]: (~v1_xboole_0(B_113) | ~v1_xboole_0(A_114) | k1_relat_1(A_114)=B_113)), inference(resolution, [status(thm)], [c_477, c_2])).
% 2.83/1.43  tff(c_562, plain, (![A_115]: (~v1_xboole_0(A_115) | k1_relat_1(A_115)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_531])).
% 2.83/1.43  tff(c_600, plain, (k1_relat_1(k1_wellord1('#skF_9', '#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_562])).
% 2.83/1.43  tff(c_900, plain, (![A_121]: (~v1_xboole_0(A_121) | k1_wellord1('#skF_9', '#skF_8')=k1_relat_1(A_121))), inference(resolution, [status(thm)], [c_142, c_531])).
% 2.83/1.43  tff(c_924, plain, (k1_relat_1(k1_wellord1('#skF_9', '#skF_8'))=k1_wellord1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_142, c_900])).
% 2.83/1.43  tff(c_939, plain, (k1_wellord1('#skF_9', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_600, c_924])).
% 2.83/1.43  tff(c_941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_939])).
% 2.83/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  Inference rules
% 2.83/1.43  ----------------------
% 2.83/1.43  #Ref     : 0
% 2.83/1.43  #Sup     : 195
% 2.83/1.43  #Fact    : 0
% 2.83/1.43  #Define  : 0
% 2.83/1.43  #Split   : 0
% 2.83/1.43  #Chain   : 0
% 2.83/1.43  #Close   : 0
% 2.83/1.43  
% 2.83/1.43  Ordering : KBO
% 2.83/1.43  
% 2.83/1.43  Simplification rules
% 2.83/1.43  ----------------------
% 2.83/1.43  #Subsume      : 27
% 2.83/1.43  #Demod        : 105
% 2.83/1.43  #Tautology    : 37
% 2.83/1.43  #SimpNegUnit  : 1
% 2.83/1.43  #BackRed      : 0
% 2.83/1.43  
% 2.83/1.43  #Partial instantiations: 0
% 2.83/1.43  #Strategies tried      : 1
% 2.83/1.43  
% 2.83/1.43  Timing (in seconds)
% 2.83/1.43  ----------------------
% 2.83/1.43  Preprocessing        : 0.29
% 2.83/1.43  Parsing              : 0.15
% 2.83/1.43  CNF conversion       : 0.03
% 2.83/1.43  Main loop            : 0.35
% 2.83/1.43  Inferencing          : 0.14
% 2.83/1.43  Reduction            : 0.08
% 2.83/1.43  Demodulation         : 0.06
% 2.83/1.43  BG Simplification    : 0.02
% 2.83/1.43  Subsumption          : 0.08
% 2.83/1.43  Abstraction          : 0.02
% 2.83/1.43  MUC search           : 0.00
% 2.83/1.44  Cooper               : 0.00
% 2.83/1.44  Total                : 0.66
% 2.83/1.44  Index Insertion      : 0.00
% 2.83/1.44  Index Deletion       : 0.00
% 2.83/1.44  Index Matching       : 0.00
% 2.83/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
