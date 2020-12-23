%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:21 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  51 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_65,axiom,(
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

tff(f_44,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    ! [A_56] :
      ( v1_relat_1(A_56)
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_1317,plain,(
    ! [A_148,B_149,C_150] :
      ( r2_hidden(k4_tarski('#skF_2'(A_148,B_149,C_150),'#skF_3'(A_148,B_149,C_150)),A_148)
      | r2_hidden('#skF_4'(A_148,B_149,C_150),C_150)
      | k10_relat_1(A_148,B_149) = C_150
      | ~ v1_relat_1(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_64,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_71,plain,(
    ! [A_6,C_64] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_73,plain,(
    ! [C_64] : ~ r2_hidden(C_64,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_1367,plain,(
    ! [B_149,C_150] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_149,C_150),C_150)
      | k10_relat_1(k1_xboole_0,B_149) = C_150
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1317,c_73])).

tff(c_1388,plain,(
    ! [B_151,C_152] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_151,C_152),C_152)
      | k10_relat_1(k1_xboole_0,B_151) = C_152 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1367])).

tff(c_1455,plain,(
    ! [B_151] : k10_relat_1(k1_xboole_0,B_151) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1388,c_73])).

tff(c_36,plain,(
    k10_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1455,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:06:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.51  
% 2.85/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.51  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 2.85/1.51  
% 2.85/1.51  %Foreground sorts:
% 2.85/1.51  
% 2.85/1.51  
% 2.85/1.51  %Background operators:
% 2.85/1.51  
% 2.85/1.51  
% 2.85/1.51  %Foreground operators:
% 2.85/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.85/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.85/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.51  tff('#skF_6', type, '#skF_6': $i).
% 2.85/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.85/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.85/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.85/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.85/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.85/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.85/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.85/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.85/1.51  
% 2.85/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.85/1.52  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.85/1.52  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 2.85/1.52  tff(f_44, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.85/1.52  tff(f_42, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.85/1.52  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.85/1.52  tff(f_68, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.85/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.85/1.52  tff(c_38, plain, (![A_56]: (v1_relat_1(A_56) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.85/1.52  tff(c_42, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_38])).
% 2.85/1.52  tff(c_1317, plain, (![A_148, B_149, C_150]: (r2_hidden(k4_tarski('#skF_2'(A_148, B_149, C_150), '#skF_3'(A_148, B_149, C_150)), A_148) | r2_hidden('#skF_4'(A_148, B_149, C_150), C_150) | k10_relat_1(A_148, B_149)=C_150 | ~v1_relat_1(A_148))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.85/1.52  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.85/1.52  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.85/1.52  tff(c_68, plain, (![A_62, B_63, C_64]: (~r1_xboole_0(A_62, B_63) | ~r2_hidden(C_64, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.85/1.52  tff(c_71, plain, (![A_6, C_64]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 2.85/1.52  tff(c_73, plain, (![C_64]: (~r2_hidden(C_64, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_71])).
% 2.85/1.52  tff(c_1367, plain, (![B_149, C_150]: (r2_hidden('#skF_4'(k1_xboole_0, B_149, C_150), C_150) | k10_relat_1(k1_xboole_0, B_149)=C_150 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1317, c_73])).
% 2.85/1.52  tff(c_1388, plain, (![B_151, C_152]: (r2_hidden('#skF_4'(k1_xboole_0, B_151, C_152), C_152) | k10_relat_1(k1_xboole_0, B_151)=C_152)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1367])).
% 2.85/1.52  tff(c_1455, plain, (![B_151]: (k10_relat_1(k1_xboole_0, B_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1388, c_73])).
% 2.85/1.52  tff(c_36, plain, (k10_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.85/1.52  tff(c_1472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1455, c_36])).
% 2.85/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.52  
% 2.85/1.52  Inference rules
% 2.85/1.52  ----------------------
% 2.85/1.52  #Ref     : 0
% 2.85/1.52  #Sup     : 287
% 2.85/1.52  #Fact    : 0
% 2.85/1.52  #Define  : 0
% 2.85/1.52  #Split   : 0
% 2.85/1.52  #Chain   : 0
% 2.85/1.52  #Close   : 0
% 2.85/1.52  
% 2.85/1.52  Ordering : KBO
% 2.85/1.52  
% 2.85/1.52  Simplification rules
% 2.85/1.52  ----------------------
% 2.85/1.52  #Subsume      : 150
% 2.85/1.52  #Demod        : 113
% 2.85/1.52  #Tautology    : 37
% 2.85/1.52  #SimpNegUnit  : 3
% 2.85/1.52  #BackRed      : 9
% 2.85/1.52  
% 2.85/1.52  #Partial instantiations: 0
% 2.85/1.52  #Strategies tried      : 1
% 2.85/1.52  
% 2.85/1.52  Timing (in seconds)
% 2.85/1.52  ----------------------
% 3.20/1.53  Preprocessing        : 0.29
% 3.20/1.53  Parsing              : 0.15
% 3.20/1.53  CNF conversion       : 0.02
% 3.20/1.53  Main loop            : 0.47
% 3.20/1.53  Inferencing          : 0.19
% 3.20/1.53  Reduction            : 0.11
% 3.20/1.53  Demodulation         : 0.08
% 3.20/1.53  BG Simplification    : 0.02
% 3.20/1.53  Subsumption          : 0.10
% 3.20/1.53  Abstraction          : 0.03
% 3.20/1.53  MUC search           : 0.00
% 3.20/1.53  Cooper               : 0.00
% 3.20/1.53  Total                : 0.78
% 3.20/1.53  Index Insertion      : 0.00
% 3.20/1.53  Index Deletion       : 0.00
% 3.20/1.53  Index Matching       : 0.00
% 3.20/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
