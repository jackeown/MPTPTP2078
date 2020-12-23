%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:39 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_75,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    ! [A_60] : k2_zfmisc_1(A_60,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    ! [A_54,B_55] : v1_relat_1(k2_zfmisc_1(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_36])).

tff(c_177,plain,(
    ! [A_83,B_84,D_85] :
      ( r2_hidden(k4_tarski('#skF_6'(A_83,B_84,k9_relat_1(A_83,B_84),D_85),D_85),A_83)
      | ~ r2_hidden(D_85,k9_relat_1(A_83,B_84))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(C_65,k3_xboole_0(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_83,plain,(
    ! [A_8,C_65] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_65,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_86,plain,(
    ! [C_65] : ~ r2_hidden(C_65,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_83])).

tff(c_187,plain,(
    ! [D_85,B_84] :
      ( ~ r2_hidden(D_85,k9_relat_1(k1_xboole_0,B_84))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_177,c_86])).

tff(c_204,plain,(
    ! [D_86,B_87] : ~ r2_hidden(D_86,k9_relat_1(k1_xboole_0,B_87)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_187])).

tff(c_221,plain,(
    ! [B_87] : k9_relat_1(k1_xboole_0,B_87) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_204])).

tff(c_38,plain,(
    k9_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:04:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.20  
% 1.97/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.20  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 1.97/1.20  
% 1.97/1.20  %Foreground sorts:
% 1.97/1.20  
% 1.97/1.20  
% 1.97/1.20  %Background operators:
% 1.97/1.20  
% 1.97/1.20  
% 1.97/1.20  %Foreground operators:
% 1.97/1.20  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.97/1.20  tff('#skF_7', type, '#skF_7': $i).
% 1.97/1.20  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.97/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.97/1.20  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.20  
% 1.97/1.21  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.97/1.21  tff(f_57, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.97/1.21  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.97/1.21  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 1.97/1.21  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.97/1.21  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.97/1.21  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.97/1.21  tff(f_75, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.97/1.21  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.21  tff(c_48, plain, (![A_60]: (k2_zfmisc_1(A_60, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.97/1.21  tff(c_36, plain, (![A_54, B_55]: (v1_relat_1(k2_zfmisc_1(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.97/1.21  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_36])).
% 1.97/1.21  tff(c_177, plain, (![A_83, B_84, D_85]: (r2_hidden(k4_tarski('#skF_6'(A_83, B_84, k9_relat_1(A_83, B_84), D_85), D_85), A_83) | ~r2_hidden(D_85, k9_relat_1(A_83, B_84)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.97/1.21  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.21  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.97/1.21  tff(c_76, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(C_65, k3_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.21  tff(c_83, plain, (![A_8, C_65]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_76])).
% 1.97/1.21  tff(c_86, plain, (![C_65]: (~r2_hidden(C_65, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_83])).
% 1.97/1.21  tff(c_187, plain, (![D_85, B_84]: (~r2_hidden(D_85, k9_relat_1(k1_xboole_0, B_84)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_177, c_86])).
% 1.97/1.21  tff(c_204, plain, (![D_86, B_87]: (~r2_hidden(D_86, k9_relat_1(k1_xboole_0, B_87)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_187])).
% 1.97/1.21  tff(c_221, plain, (![B_87]: (k9_relat_1(k1_xboole_0, B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_204])).
% 1.97/1.21  tff(c_38, plain, (k9_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.97/1.21  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_38])).
% 1.97/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  Inference rules
% 1.97/1.21  ----------------------
% 1.97/1.21  #Ref     : 0
% 1.97/1.21  #Sup     : 40
% 1.97/1.21  #Fact    : 0
% 1.97/1.21  #Define  : 0
% 1.97/1.21  #Split   : 0
% 1.97/1.21  #Chain   : 0
% 1.97/1.21  #Close   : 0
% 1.97/1.21  
% 1.97/1.21  Ordering : KBO
% 1.97/1.21  
% 1.97/1.21  Simplification rules
% 1.97/1.21  ----------------------
% 1.97/1.21  #Subsume      : 5
% 1.97/1.21  #Demod        : 13
% 1.97/1.21  #Tautology    : 18
% 1.97/1.21  #SimpNegUnit  : 3
% 1.97/1.21  #BackRed      : 2
% 1.97/1.21  
% 1.97/1.21  #Partial instantiations: 0
% 1.97/1.21  #Strategies tried      : 1
% 1.97/1.21  
% 1.97/1.21  Timing (in seconds)
% 1.97/1.21  ----------------------
% 1.97/1.21  Preprocessing        : 0.31
% 1.97/1.21  Parsing              : 0.16
% 1.97/1.21  CNF conversion       : 0.03
% 1.97/1.21  Main loop            : 0.17
% 1.97/1.22  Inferencing          : 0.07
% 1.97/1.22  Reduction            : 0.05
% 1.97/1.22  Demodulation         : 0.04
% 1.97/1.22  BG Simplification    : 0.01
% 1.97/1.22  Subsumption          : 0.03
% 1.97/1.22  Abstraction          : 0.01
% 1.97/1.22  MUC search           : 0.00
% 1.97/1.22  Cooper               : 0.00
% 1.97/1.22  Total                : 0.50
% 1.97/1.22  Index Insertion      : 0.00
% 1.97/1.22  Index Deletion       : 0.00
% 1.97/1.22  Index Matching       : 0.00
% 1.97/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
