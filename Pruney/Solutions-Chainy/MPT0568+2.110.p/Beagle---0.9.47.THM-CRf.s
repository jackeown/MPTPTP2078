%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:34 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  55 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_63,axiom,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_110,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),B_27)
      | r2_hidden('#skF_2'(A_26,B_27),A_26)
      | B_27 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_18,B_19] : ~ r2_hidden(A_18,k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_79])).

tff(c_117,plain,(
    ! [B_27] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_27),B_27)
      | k1_xboole_0 = B_27 ) ),
    inference(resolution,[status(thm)],[c_110,c_82])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_73,plain,(
    ! [A_17] :
      ( v1_relat_1(k4_relat_1(A_17))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_76,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_73])).

tff(c_78,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_76])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_245,plain,(
    ! [A_43,B_44,C_45] :
      ( r2_hidden('#skF_3'(A_43,B_44,C_45),k2_relat_1(C_45))
      | ~ r2_hidden(A_43,k10_relat_1(C_45,B_44))
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_248,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_3'(A_43,B_44,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_43,k10_relat_1(k1_xboole_0,B_44))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_245])).

tff(c_250,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_3'(A_43,B_44,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_43,k10_relat_1(k1_xboole_0,B_44)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_248])).

tff(c_252,plain,(
    ! [A_46,B_47] : ~ r2_hidden(A_46,k10_relat_1(k1_xboole_0,B_47)) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_250])).

tff(c_276,plain,(
    ! [B_47] : k10_relat_1(k1_xboole_0,B_47) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_252])).

tff(c_38,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.59  
% 2.40/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.60  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.40/1.60  
% 2.40/1.60  %Foreground sorts:
% 2.40/1.60  
% 2.40/1.60  
% 2.40/1.60  %Background operators:
% 2.40/1.60  
% 2.40/1.60  
% 2.40/1.60  %Foreground operators:
% 2.40/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.40/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.40/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.60  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.40/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.40/1.60  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.40/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.40/1.60  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.40/1.60  
% 2.40/1.61  tff(f_33, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.40/1.61  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.40/1.61  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.40/1.61  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.40/1.61  tff(f_63, axiom, (k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 2.40/1.61  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 2.40/1.61  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.40/1.61  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.40/1.61  tff(f_66, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.40/1.61  tff(c_110, plain, (![A_26, B_27]: (r2_hidden('#skF_1'(A_26, B_27), B_27) | r2_hidden('#skF_2'(A_26, B_27), A_26) | B_27=A_26)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.61  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.61  tff(c_79, plain, (![A_18, B_19]: (~r2_hidden(A_18, k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.40/1.61  tff(c_82, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_79])).
% 2.40/1.61  tff(c_117, plain, (![B_27]: (r2_hidden('#skF_1'(k1_xboole_0, B_27), B_27) | k1_xboole_0=B_27)), inference(resolution, [status(thm)], [c_110, c_82])).
% 2.40/1.61  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.40/1.61  tff(c_36, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.40/1.61  tff(c_73, plain, (![A_17]: (v1_relat_1(k4_relat_1(A_17)) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.40/1.61  tff(c_76, plain, (v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_73])).
% 2.40/1.61  tff(c_78, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_76])).
% 2.40/1.61  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.40/1.61  tff(c_245, plain, (![A_43, B_44, C_45]: (r2_hidden('#skF_3'(A_43, B_44, C_45), k2_relat_1(C_45)) | ~r2_hidden(A_43, k10_relat_1(C_45, B_44)) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.61  tff(c_248, plain, (![A_43, B_44]: (r2_hidden('#skF_3'(A_43, B_44, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_43, k10_relat_1(k1_xboole_0, B_44)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_245])).
% 2.40/1.61  tff(c_250, plain, (![A_43, B_44]: (r2_hidden('#skF_3'(A_43, B_44, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_43, k10_relat_1(k1_xboole_0, B_44)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_248])).
% 2.40/1.61  tff(c_252, plain, (![A_46, B_47]: (~r2_hidden(A_46, k10_relat_1(k1_xboole_0, B_47)))), inference(negUnitSimplification, [status(thm)], [c_82, c_250])).
% 2.40/1.61  tff(c_276, plain, (![B_47]: (k10_relat_1(k1_xboole_0, B_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_252])).
% 2.40/1.61  tff(c_38, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.40/1.61  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_276, c_38])).
% 2.40/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.61  
% 2.40/1.61  Inference rules
% 2.40/1.61  ----------------------
% 2.40/1.61  #Ref     : 0
% 2.40/1.61  #Sup     : 53
% 2.40/1.61  #Fact    : 0
% 2.40/1.61  #Define  : 0
% 2.40/1.61  #Split   : 0
% 2.40/1.61  #Chain   : 0
% 2.40/1.61  #Close   : 0
% 2.40/1.61  
% 2.40/1.61  Ordering : KBO
% 2.40/1.61  
% 2.40/1.61  Simplification rules
% 2.40/1.61  ----------------------
% 2.40/1.61  #Subsume      : 12
% 2.40/1.61  #Demod        : 11
% 2.40/1.61  #Tautology    : 24
% 2.40/1.61  #SimpNegUnit  : 1
% 2.40/1.61  #BackRed      : 2
% 2.40/1.61  
% 2.40/1.61  #Partial instantiations: 0
% 2.40/1.61  #Strategies tried      : 1
% 2.40/1.61  
% 2.40/1.61  Timing (in seconds)
% 2.40/1.61  ----------------------
% 2.40/1.62  Preprocessing        : 0.44
% 2.40/1.62  Parsing              : 0.23
% 2.40/1.62  CNF conversion       : 0.03
% 2.40/1.62  Main loop            : 0.30
% 2.40/1.62  Inferencing          : 0.13
% 2.40/1.62  Reduction            : 0.08
% 2.40/1.62  Demodulation         : 0.05
% 2.40/1.62  BG Simplification    : 0.02
% 2.40/1.62  Subsumption          : 0.05
% 2.40/1.62  Abstraction          : 0.01
% 2.40/1.62  MUC search           : 0.00
% 2.40/1.62  Cooper               : 0.00
% 2.40/1.62  Total                : 0.78
% 2.40/1.62  Index Insertion      : 0.00
% 2.40/1.62  Index Deletion       : 0.00
% 2.40/1.62  Index Matching       : 0.00
% 2.40/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
