%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:27 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   44 (  61 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  70 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    ! [A_60] : k2_zfmisc_1(A_60,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_54,B_55] : v1_relat_1(k2_zfmisc_1(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_36])).

tff(c_1272,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden(k4_tarski('#skF_2'(A_150,B_151,C_152),'#skF_3'(A_150,B_151,C_152)),A_150)
      | r2_hidden('#skF_4'(A_150,B_151,C_152),C_152)
      | k10_relat_1(A_150,B_151) = C_152
      | ~ v1_relat_1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,(
    ! [B_67] : k3_xboole_0(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [B_67,C_5] :
      ( ~ r1_xboole_0(k1_xboole_0,B_67)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_4])).

tff(c_115,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_1314,plain,(
    ! [B_151,C_152] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_151,C_152),C_152)
      | k10_relat_1(k1_xboole_0,B_151) = C_152
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1272,c_115])).

tff(c_1333,plain,(
    ! [B_153,C_154] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_153,C_154),C_154)
      | k10_relat_1(k1_xboole_0,B_153) = C_154 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1314])).

tff(c_1390,plain,(
    ! [B_153] : k10_relat_1(k1_xboole_0,B_153) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1333,c_115])).

tff(c_38,plain,(
    k10_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_38])).

tff(c_1409,plain,(
    ! [B_155] : ~ r1_xboole_0(k1_xboole_0,B_155) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_1414,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_1409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.53  
% 3.11/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.53  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 3.11/1.53  
% 3.11/1.53  %Foreground sorts:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Background operators:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Foreground operators:
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.11/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.11/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.11/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.11/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.11/1.53  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.11/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.11/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.11/1.53  
% 3.11/1.54  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.11/1.54  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.11/1.54  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.11/1.54  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 3.11/1.54  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.11/1.54  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.11/1.54  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.11/1.54  tff(f_69, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 3.11/1.54  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.11/1.54  tff(c_48, plain, (![A_60]: (k2_zfmisc_1(A_60, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.11/1.54  tff(c_36, plain, (![A_54, B_55]: (v1_relat_1(k2_zfmisc_1(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.11/1.54  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_36])).
% 3.11/1.54  tff(c_1272, plain, (![A_150, B_151, C_152]: (r2_hidden(k4_tarski('#skF_2'(A_150, B_151, C_152), '#skF_3'(A_150, B_151, C_152)), A_150) | r2_hidden('#skF_4'(A_150, B_151, C_152), C_152) | k10_relat_1(A_150, B_151)=C_152 | ~v1_relat_1(A_150))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.11/1.54  tff(c_76, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.11/1.54  tff(c_8, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.11/1.54  tff(c_103, plain, (![B_67]: (k3_xboole_0(k1_xboole_0, B_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_76, c_8])).
% 3.11/1.54  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.11/1.54  tff(c_108, plain, (![B_67, C_5]: (~r1_xboole_0(k1_xboole_0, B_67) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_103, c_4])).
% 3.11/1.54  tff(c_115, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_108])).
% 3.11/1.54  tff(c_1314, plain, (![B_151, C_152]: (r2_hidden('#skF_4'(k1_xboole_0, B_151, C_152), C_152) | k10_relat_1(k1_xboole_0, B_151)=C_152 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1272, c_115])).
% 3.11/1.54  tff(c_1333, plain, (![B_153, C_154]: (r2_hidden('#skF_4'(k1_xboole_0, B_153, C_154), C_154) | k10_relat_1(k1_xboole_0, B_153)=C_154)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1314])).
% 3.11/1.54  tff(c_1390, plain, (![B_153]: (k10_relat_1(k1_xboole_0, B_153)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1333, c_115])).
% 3.11/1.54  tff(c_38, plain, (k10_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.11/1.54  tff(c_1407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1390, c_38])).
% 3.11/1.54  tff(c_1409, plain, (![B_155]: (~r1_xboole_0(k1_xboole_0, B_155))), inference(splitRight, [status(thm)], [c_108])).
% 3.11/1.54  tff(c_1414, plain, $false, inference(resolution, [status(thm)], [c_10, c_1409])).
% 3.11/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.54  
% 3.11/1.54  Inference rules
% 3.11/1.54  ----------------------
% 3.11/1.54  #Ref     : 0
% 3.11/1.54  #Sup     : 285
% 3.11/1.54  #Fact    : 0
% 3.11/1.54  #Define  : 0
% 3.11/1.54  #Split   : 1
% 3.11/1.54  #Chain   : 0
% 3.11/1.54  #Close   : 0
% 3.11/1.54  
% 3.11/1.54  Ordering : KBO
% 3.11/1.54  
% 3.11/1.54  Simplification rules
% 3.11/1.54  ----------------------
% 3.11/1.54  #Subsume      : 121
% 3.11/1.54  #Demod        : 141
% 3.11/1.54  #Tautology    : 66
% 3.11/1.54  #SimpNegUnit  : 5
% 3.11/1.54  #BackRed      : 9
% 3.11/1.54  
% 3.11/1.54  #Partial instantiations: 0
% 3.11/1.54  #Strategies tried      : 1
% 3.11/1.54  
% 3.11/1.54  Timing (in seconds)
% 3.11/1.54  ----------------------
% 3.11/1.55  Preprocessing        : 0.31
% 3.11/1.55  Parsing              : 0.17
% 3.11/1.55  CNF conversion       : 0.03
% 3.11/1.55  Main loop            : 0.42
% 3.11/1.55  Inferencing          : 0.16
% 3.11/1.55  Reduction            : 0.12
% 3.11/1.55  Demodulation         : 0.09
% 3.11/1.55  BG Simplification    : 0.02
% 3.11/1.55  Subsumption          : 0.08
% 3.11/1.55  Abstraction          : 0.02
% 3.11/1.55  MUC search           : 0.00
% 3.11/1.55  Cooper               : 0.00
% 3.11/1.55  Total                : 0.75
% 3.11/1.55  Index Insertion      : 0.00
% 3.11/1.55  Index Deletion       : 0.00
% 3.11/1.55  Index Matching       : 0.00
% 3.11/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
