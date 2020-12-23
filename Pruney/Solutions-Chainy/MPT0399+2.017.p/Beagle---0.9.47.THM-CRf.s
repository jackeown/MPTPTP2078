%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:34 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   42 (  97 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 ( 148 expanded)
%              Number of equality atoms :   14 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    r1_setfam_1('#skF_7',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_5'(A_24,B_25),A_24)
      | r1_setfam_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_171,plain,(
    ! [A_69,B_70,C_71] :
      ( r2_hidden('#skF_6'(A_69,B_70,C_71),B_70)
      | ~ r2_hidden(C_71,A_69)
      | ~ r1_setfam_1(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_20] : k2_zfmisc_1(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_61,plain,(
    ! [A_38,B_39] : ~ r2_hidden(A_38,k2_zfmisc_1(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_64,plain,(
    ! [A_20] : ~ r2_hidden(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_61])).

tff(c_205,plain,(
    ! [C_72,A_73] :
      ( ~ r2_hidden(C_72,A_73)
      | ~ r1_setfam_1(A_73,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_171,c_64])).

tff(c_222,plain,(
    ! [A_74,B_75] :
      ( ~ r1_setfam_1(A_74,k1_xboole_0)
      | r1_setfam_1(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_34,c_205])).

tff(c_255,plain,(
    ! [B_75] : r1_setfam_1('#skF_7',B_75) ),
    inference(resolution,[status(thm)],[c_38,c_222])).

tff(c_263,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_2'(A_77,B_78),A_77)
      | r2_hidden('#skF_3'(A_77,B_78),B_78)
      | k3_tarski(A_77) = B_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_425,plain,(
    ! [A_87] :
      ( r2_hidden('#skF_2'(A_87,k1_xboole_0),A_87)
      | k3_tarski(A_87) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_263,c_64])).

tff(c_470,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_425,c_64])).

tff(c_92,plain,(
    ! [A_52,C_53] :
      ( r2_hidden('#skF_4'(A_52,k3_tarski(A_52),C_53),A_52)
      | ~ r2_hidden(C_53,k3_tarski(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [C_53] : ~ r2_hidden(C_53,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_92,c_64])).

tff(c_325,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_3'(k3_tarski(k1_xboole_0),B_78),B_78)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_78 ) ),
    inference(resolution,[status(thm)],[c_263,c_100])).

tff(c_2403,plain,(
    ! [B_146] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_146),B_146)
      | k1_xboole_0 = B_146 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_470,c_470,c_325])).

tff(c_204,plain,(
    ! [C_71,A_69] :
      ( ~ r2_hidden(C_71,A_69)
      | ~ r1_setfam_1(A_69,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_171,c_64])).

tff(c_2464,plain,(
    ! [B_147] :
      ( ~ r1_setfam_1(B_147,k1_xboole_0)
      | k1_xboole_0 = B_147 ) ),
    inference(resolution,[status(thm)],[c_2403,c_204])).

tff(c_2492,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_255,c_2464])).

tff(c_2506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:27:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.62  
% 3.20/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.63  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_zfmisc_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5
% 3.20/1.63  
% 3.20/1.63  %Foreground sorts:
% 3.20/1.63  
% 3.20/1.63  
% 3.20/1.63  %Background operators:
% 3.20/1.63  
% 3.20/1.63  
% 3.20/1.63  %Foreground operators:
% 3.20/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.63  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 3.20/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.63  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.20/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.20/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.20/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.20/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.63  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.20/1.63  
% 3.56/1.64  tff(f_61, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 3.56/1.64  tff(f_56, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 3.56/1.64  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.56/1.64  tff(f_44, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.56/1.64  tff(f_35, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 3.56/1.64  tff(c_36, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.56/1.64  tff(c_38, plain, (r1_setfam_1('#skF_7', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.56/1.64  tff(c_34, plain, (![A_24, B_25]: (r2_hidden('#skF_5'(A_24, B_25), A_24) | r1_setfam_1(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.56/1.64  tff(c_171, plain, (![A_69, B_70, C_71]: (r2_hidden('#skF_6'(A_69, B_70, C_71), B_70) | ~r2_hidden(C_71, A_69) | ~r1_setfam_1(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.56/1.64  tff(c_22, plain, (![A_20]: (k2_zfmisc_1(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.64  tff(c_61, plain, (![A_38, B_39]: (~r2_hidden(A_38, k2_zfmisc_1(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.56/1.64  tff(c_64, plain, (![A_20]: (~r2_hidden(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_61])).
% 3.56/1.64  tff(c_205, plain, (![C_72, A_73]: (~r2_hidden(C_72, A_73) | ~r1_setfam_1(A_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_171, c_64])).
% 3.56/1.64  tff(c_222, plain, (![A_74, B_75]: (~r1_setfam_1(A_74, k1_xboole_0) | r1_setfam_1(A_74, B_75))), inference(resolution, [status(thm)], [c_34, c_205])).
% 3.56/1.64  tff(c_255, plain, (![B_75]: (r1_setfam_1('#skF_7', B_75))), inference(resolution, [status(thm)], [c_38, c_222])).
% 3.56/1.64  tff(c_263, plain, (![A_77, B_78]: (r2_hidden('#skF_2'(A_77, B_78), A_77) | r2_hidden('#skF_3'(A_77, B_78), B_78) | k3_tarski(A_77)=B_78)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.64  tff(c_425, plain, (![A_87]: (r2_hidden('#skF_2'(A_87, k1_xboole_0), A_87) | k3_tarski(A_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_263, c_64])).
% 3.56/1.64  tff(c_470, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_425, c_64])).
% 3.56/1.64  tff(c_92, plain, (![A_52, C_53]: (r2_hidden('#skF_4'(A_52, k3_tarski(A_52), C_53), A_52) | ~r2_hidden(C_53, k3_tarski(A_52)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.64  tff(c_100, plain, (![C_53]: (~r2_hidden(C_53, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_92, c_64])).
% 3.56/1.64  tff(c_325, plain, (![B_78]: (r2_hidden('#skF_3'(k3_tarski(k1_xboole_0), B_78), B_78) | k3_tarski(k3_tarski(k1_xboole_0))=B_78)), inference(resolution, [status(thm)], [c_263, c_100])).
% 3.56/1.64  tff(c_2403, plain, (![B_146]: (r2_hidden('#skF_3'(k1_xboole_0, B_146), B_146) | k1_xboole_0=B_146)), inference(demodulation, [status(thm), theory('equality')], [c_470, c_470, c_470, c_325])).
% 3.56/1.64  tff(c_204, plain, (![C_71, A_69]: (~r2_hidden(C_71, A_69) | ~r1_setfam_1(A_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_171, c_64])).
% 3.56/1.64  tff(c_2464, plain, (![B_147]: (~r1_setfam_1(B_147, k1_xboole_0) | k1_xboole_0=B_147)), inference(resolution, [status(thm)], [c_2403, c_204])).
% 3.56/1.64  tff(c_2492, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_255, c_2464])).
% 3.56/1.64  tff(c_2506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_2492])).
% 3.56/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.64  
% 3.56/1.64  Inference rules
% 3.56/1.64  ----------------------
% 3.56/1.64  #Ref     : 0
% 3.56/1.64  #Sup     : 570
% 3.56/1.64  #Fact    : 0
% 3.56/1.64  #Define  : 0
% 3.56/1.64  #Split   : 0
% 3.56/1.64  #Chain   : 0
% 3.56/1.64  #Close   : 0
% 3.56/1.64  
% 3.56/1.64  Ordering : KBO
% 3.56/1.64  
% 3.56/1.64  Simplification rules
% 3.56/1.64  ----------------------
% 3.56/1.64  #Subsume      : 173
% 3.56/1.64  #Demod        : 506
% 3.56/1.64  #Tautology    : 265
% 3.56/1.64  #SimpNegUnit  : 3
% 3.56/1.64  #BackRed      : 12
% 3.56/1.64  
% 3.56/1.64  #Partial instantiations: 0
% 3.56/1.64  #Strategies tried      : 1
% 3.56/1.64  
% 3.56/1.64  Timing (in seconds)
% 3.56/1.64  ----------------------
% 3.56/1.64  Preprocessing        : 0.30
% 3.56/1.64  Parsing              : 0.16
% 3.56/1.64  CNF conversion       : 0.03
% 3.56/1.64  Main loop            : 0.50
% 3.56/1.64  Inferencing          : 0.17
% 3.56/1.64  Reduction            : 0.15
% 3.56/1.64  Demodulation         : 0.11
% 3.56/1.64  BG Simplification    : 0.03
% 3.56/1.64  Subsumption          : 0.13
% 3.56/1.64  Abstraction          : 0.03
% 3.56/1.64  MUC search           : 0.00
% 3.56/1.64  Cooper               : 0.00
% 3.56/1.64  Total                : 0.83
% 3.56/1.64  Index Insertion      : 0.00
% 3.56/1.64  Index Deletion       : 0.00
% 3.56/1.64  Index Matching       : 0.00
% 3.56/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
