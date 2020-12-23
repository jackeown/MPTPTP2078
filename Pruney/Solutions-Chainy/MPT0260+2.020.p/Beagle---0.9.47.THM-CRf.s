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
% DateTime   : Thu Dec  3 09:52:11 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  38 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_30,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_39,B_40] : r1_tarski(k1_tarski(A_39),k2_tarski(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_47,plain,(
    ! [B_45,A_46] :
      ( r1_xboole_0(B_45,A_46)
      | ~ r1_xboole_0(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    r1_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_47])).

tff(c_73,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_73])).

tff(c_191,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,k3_xboole_0(B_72,C_73))
      | ~ r1_tarski(A_71,C_73)
      | r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_202,plain,(
    ! [A_71] :
      ( ~ r1_xboole_0(A_71,k1_xboole_0)
      | ~ r1_tarski(A_71,k2_tarski('#skF_1','#skF_2'))
      | r1_xboole_0(A_71,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_191])).

tff(c_297,plain,(
    ! [A_91] :
      ( ~ r1_tarski(A_91,k2_tarski('#skF_1','#skF_2'))
      | r1_xboole_0(A_91,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_202])).

tff(c_302,plain,(
    r1_xboole_0(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_297])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden(A_37,B_38)
      | ~ r1_xboole_0(k1_tarski(A_37),B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_314,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_302,c_26])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.27  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.27  
% 2.11/1.27  %Foreground sorts:
% 2.11/1.27  
% 2.11/1.27  
% 2.11/1.27  %Background operators:
% 2.11/1.27  
% 2.11/1.27  
% 2.11/1.27  %Foreground operators:
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.27  
% 2.11/1.28  tff(f_70, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.11/1.28  tff(f_64, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.11/1.28  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.11/1.28  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.11/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.11/1.28  tff(f_43, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.11/1.28  tff(f_62, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.11/1.28  tff(c_30, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.11/1.28  tff(c_28, plain, (![A_39, B_40]: (r1_tarski(k1_tarski(A_39), k2_tarski(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.28  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.28  tff(c_32, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.11/1.28  tff(c_47, plain, (![B_45, A_46]: (r1_xboole_0(B_45, A_46) | ~r1_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.28  tff(c_52, plain, (r1_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_47])).
% 2.11/1.28  tff(c_73, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.28  tff(c_86, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_73])).
% 2.11/1.28  tff(c_191, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, k3_xboole_0(B_72, C_73)) | ~r1_tarski(A_71, C_73) | r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.28  tff(c_202, plain, (![A_71]: (~r1_xboole_0(A_71, k1_xboole_0) | ~r1_tarski(A_71, k2_tarski('#skF_1', '#skF_2')) | r1_xboole_0(A_71, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_191])).
% 2.11/1.28  tff(c_297, plain, (![A_91]: (~r1_tarski(A_91, k2_tarski('#skF_1', '#skF_2')) | r1_xboole_0(A_91, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_202])).
% 2.11/1.28  tff(c_302, plain, (r1_xboole_0(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_28, c_297])).
% 2.11/1.28  tff(c_26, plain, (![A_37, B_38]: (~r2_hidden(A_37, B_38) | ~r1_xboole_0(k1_tarski(A_37), B_38))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.11/1.28  tff(c_314, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_302, c_26])).
% 2.11/1.28  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_314])).
% 2.11/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.28  
% 2.11/1.28  Inference rules
% 2.11/1.28  ----------------------
% 2.11/1.28  #Ref     : 0
% 2.11/1.28  #Sup     : 66
% 2.11/1.28  #Fact    : 0
% 2.11/1.28  #Define  : 0
% 2.11/1.28  #Split   : 0
% 2.11/1.28  #Chain   : 0
% 2.11/1.28  #Close   : 0
% 2.11/1.28  
% 2.11/1.28  Ordering : KBO
% 2.11/1.28  
% 2.11/1.28  Simplification rules
% 2.11/1.28  ----------------------
% 2.11/1.28  #Subsume      : 5
% 2.11/1.28  #Demod        : 13
% 2.11/1.28  #Tautology    : 29
% 2.11/1.28  #SimpNegUnit  : 0
% 2.11/1.28  #BackRed      : 0
% 2.11/1.28  
% 2.11/1.28  #Partial instantiations: 0
% 2.11/1.28  #Strategies tried      : 1
% 2.11/1.28  
% 2.11/1.28  Timing (in seconds)
% 2.11/1.28  ----------------------
% 2.11/1.28  Preprocessing        : 0.31
% 2.11/1.29  Parsing              : 0.17
% 2.11/1.29  CNF conversion       : 0.02
% 2.11/1.29  Main loop            : 0.20
% 2.11/1.29  Inferencing          : 0.08
% 2.11/1.29  Reduction            : 0.06
% 2.11/1.29  Demodulation         : 0.05
% 2.11/1.29  BG Simplification    : 0.02
% 2.11/1.29  Subsumption          : 0.04
% 2.11/1.29  Abstraction          : 0.01
% 2.11/1.29  MUC search           : 0.00
% 2.11/1.29  Cooper               : 0.00
% 2.11/1.29  Total                : 0.53
% 2.11/1.29  Index Insertion      : 0.00
% 2.11/1.29  Index Deletion       : 0.00
% 2.11/1.29  Index Matching       : 0.00
% 2.11/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
