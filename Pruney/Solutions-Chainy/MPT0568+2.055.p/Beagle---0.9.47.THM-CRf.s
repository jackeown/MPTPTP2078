%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:27 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  51 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

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

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_62,axiom,(
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

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_46,plain,(
    ! [A_58] : k2_zfmisc_1(A_58,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_52,B_53] : v1_relat_1(k2_zfmisc_1(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_34])).

tff(c_593,plain,(
    ! [A_110,B_111,C_112] :
      ( r2_hidden(k4_tarski('#skF_2'(A_110,B_111,C_112),'#skF_3'(A_110,B_111,C_112)),A_110)
      | r2_hidden('#skF_4'(A_110,B_111,C_112),C_112)
      | k10_relat_1(A_110,B_111) = C_112
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,k3_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    ! [A_6,C_62] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_62,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_73])).

tff(c_78,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_623,plain,(
    ! [B_111,C_112] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_111,C_112),C_112)
      | k10_relat_1(k1_xboole_0,B_111) = C_112
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_593,c_78])).

tff(c_639,plain,(
    ! [B_113,C_114] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_113,C_114),C_114)
      | k10_relat_1(k1_xboole_0,B_113) = C_114 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_623])).

tff(c_681,plain,(
    ! [B_113] : k10_relat_1(k1_xboole_0,B_113) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_639,c_78])).

tff(c_36,plain,(
    k10_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.40  
% 2.37/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.40  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 2.37/1.40  
% 2.37/1.40  %Foreground sorts:
% 2.37/1.40  
% 2.37/1.40  
% 2.37/1.40  %Background operators:
% 2.37/1.40  
% 2.37/1.40  
% 2.37/1.40  %Foreground operators:
% 2.37/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.37/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.37/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.37/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.37/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.37/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.37/1.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.37/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.37/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.40  
% 2.37/1.41  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.37/1.41  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.37/1.41  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 2.37/1.41  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.37/1.41  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.37/1.41  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.37/1.41  tff(f_67, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.37/1.41  tff(c_46, plain, (![A_58]: (k2_zfmisc_1(A_58, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.37/1.41  tff(c_34, plain, (![A_52, B_53]: (v1_relat_1(k2_zfmisc_1(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.37/1.41  tff(c_50, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_34])).
% 2.37/1.41  tff(c_593, plain, (![A_110, B_111, C_112]: (r2_hidden(k4_tarski('#skF_2'(A_110, B_111, C_112), '#skF_3'(A_110, B_111, C_112)), A_110) | r2_hidden('#skF_4'(A_110, B_111, C_112), C_112) | k10_relat_1(A_110, B_111)=C_112 | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.37/1.41  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.37/1.41  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.37/1.41  tff(c_73, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.37/1.41  tff(c_76, plain, (![A_6, C_62]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_73])).
% 2.37/1.41  tff(c_78, plain, (![C_62]: (~r2_hidden(C_62, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_76])).
% 2.37/1.41  tff(c_623, plain, (![B_111, C_112]: (r2_hidden('#skF_4'(k1_xboole_0, B_111, C_112), C_112) | k10_relat_1(k1_xboole_0, B_111)=C_112 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_593, c_78])).
% 2.37/1.41  tff(c_639, plain, (![B_113, C_114]: (r2_hidden('#skF_4'(k1_xboole_0, B_113, C_114), C_114) | k10_relat_1(k1_xboole_0, B_113)=C_114)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_623])).
% 2.37/1.41  tff(c_681, plain, (![B_113]: (k10_relat_1(k1_xboole_0, B_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_639, c_78])).
% 2.37/1.41  tff(c_36, plain, (k10_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.37/1.41  tff(c_693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_681, c_36])).
% 2.37/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.41  
% 2.37/1.41  Inference rules
% 2.37/1.41  ----------------------
% 2.37/1.41  #Ref     : 0
% 2.37/1.41  #Sup     : 135
% 2.37/1.41  #Fact    : 0
% 2.37/1.41  #Define  : 0
% 2.37/1.41  #Split   : 0
% 2.37/1.41  #Chain   : 0
% 2.37/1.41  #Close   : 0
% 2.37/1.41  
% 2.37/1.41  Ordering : KBO
% 2.37/1.41  
% 2.37/1.41  Simplification rules
% 2.37/1.41  ----------------------
% 2.37/1.41  #Subsume      : 44
% 2.37/1.41  #Demod        : 47
% 2.37/1.41  #Tautology    : 26
% 2.37/1.41  #SimpNegUnit  : 5
% 2.37/1.41  #BackRed      : 6
% 2.37/1.41  
% 2.37/1.41  #Partial instantiations: 0
% 2.37/1.41  #Strategies tried      : 1
% 2.37/1.41  
% 2.37/1.41  Timing (in seconds)
% 2.37/1.41  ----------------------
% 2.37/1.42  Preprocessing        : 0.30
% 2.37/1.42  Parsing              : 0.16
% 2.37/1.42  CNF conversion       : 0.03
% 2.37/1.42  Main loop            : 0.28
% 2.37/1.42  Inferencing          : 0.11
% 2.37/1.42  Reduction            : 0.08
% 2.37/1.42  Demodulation         : 0.06
% 2.37/1.42  BG Simplification    : 0.02
% 2.37/1.42  Subsumption          : 0.05
% 2.37/1.42  Abstraction          : 0.02
% 2.37/1.42  MUC search           : 0.00
% 2.37/1.42  Cooper               : 0.00
% 2.37/1.42  Total                : 0.61
% 2.37/1.42  Index Insertion      : 0.00
% 2.37/1.42  Index Deletion       : 0.00
% 2.37/1.42  Index Matching       : 0.00
% 2.37/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
