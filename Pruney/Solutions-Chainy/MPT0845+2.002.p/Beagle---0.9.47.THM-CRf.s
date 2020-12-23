%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:44 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   54 (  64 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 104 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_65,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1100,plain,(
    ! [A_216,B_217,C_218] :
      ( r2_hidden('#skF_1'(A_216,B_217,C_218),A_216)
      | r2_hidden('#skF_2'(A_216,B_217,C_218),C_218)
      | k4_xboole_0(A_216,B_217) = C_218 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1353,plain,(
    ! [A_236,C_237] :
      ( r2_hidden('#skF_2'(A_236,A_236,C_237),C_237)
      | k4_xboole_0(A_236,A_236) = C_237 ) ),
    inference(resolution,[status(thm)],[c_1100,c_18])).

tff(c_34,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_204,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_4'(A_84,B_85),B_85)
      | ~ r2_hidden(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    ! [B_58,A_57] :
      ( ~ r1_tarski(B_58,A_57)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_414,plain,(
    ! [B_114,A_115] :
      ( ~ r1_tarski(B_114,'#skF_4'(A_115,B_114))
      | ~ r2_hidden(A_115,B_114) ) ),
    inference(resolution,[status(thm)],[c_204,c_56])).

tff(c_419,plain,(
    ! [A_115] : ~ r2_hidden(A_115,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_414])).

tff(c_1391,plain,(
    ! [A_236] : k4_xboole_0(A_236,A_236) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1353,c_419])).

tff(c_1171,plain,(
    ! [A_216,C_218] :
      ( r2_hidden('#skF_2'(A_216,A_216,C_218),C_218)
      | k4_xboole_0(A_216,A_216) = C_218 ) ),
    inference(resolution,[status(thm)],[c_1100,c_18])).

tff(c_1395,plain,(
    ! [A_216,C_218] :
      ( r2_hidden('#skF_2'(A_216,A_216,C_218),C_218)
      | k1_xboole_0 = C_218 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_1171])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_449,plain,(
    ! [D_121,A_122,B_123] :
      ( ~ r2_hidden(D_121,'#skF_4'(A_122,B_123))
      | ~ r2_hidden(D_121,B_123)
      | ~ r2_hidden(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2682,plain,(
    ! [A_339,A_340,B_341] :
      ( ~ r2_hidden('#skF_3'(A_339,'#skF_4'(A_340,B_341)),B_341)
      | ~ r2_hidden(A_340,B_341)
      | r1_xboole_0(A_339,'#skF_4'(A_340,B_341)) ) ),
    inference(resolution,[status(thm)],[c_26,c_449])).

tff(c_2698,plain,(
    ! [A_342,A_343] :
      ( ~ r2_hidden(A_342,A_343)
      | r1_xboole_0(A_343,'#skF_4'(A_342,A_343)) ) ),
    inference(resolution,[status(thm)],[c_28,c_2682])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2705,plain,(
    ! [A_344,A_345] :
      ( r1_xboole_0('#skF_4'(A_344,A_345),A_345)
      | ~ r2_hidden(A_344,A_345) ) ),
    inference(resolution,[status(thm)],[c_2698,c_22])).

tff(c_58,plain,(
    ! [B_60] :
      ( ~ r1_xboole_0(B_60,'#skF_5')
      | ~ r2_hidden(B_60,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_223,plain,(
    ! [A_84] :
      ( ~ r1_xboole_0('#skF_4'(A_84,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_84,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_204,c_58])).

tff(c_2717,plain,(
    ! [A_346] : ~ r2_hidden(A_346,'#skF_5') ),
    inference(resolution,[status(thm)],[c_2705,c_223])).

tff(c_2739,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1395,c_2717])).

tff(c_2785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:53:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.73  
% 3.97/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.73  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.97/1.73  
% 3.97/1.73  %Foreground sorts:
% 3.97/1.73  
% 3.97/1.73  
% 3.97/1.73  %Background operators:
% 3.97/1.73  
% 3.97/1.73  
% 3.97/1.73  %Foreground operators:
% 3.97/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.97/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.97/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.97/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.97/1.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.97/1.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.97/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.97/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.97/1.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.97/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.97/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.97/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.97/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.97/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.97/1.73  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.97/1.73  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.97/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.97/1.73  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.97/1.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.97/1.73  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.97/1.73  
% 3.97/1.74  tff(f_110, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.97/1.74  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.97/1.74  tff(f_65, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.97/1.74  tff(f_92, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 3.97/1.74  tff(f_99, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.97/1.74  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.97/1.74  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.97/1.74  tff(c_60, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.97/1.74  tff(c_1100, plain, (![A_216, B_217, C_218]: (r2_hidden('#skF_1'(A_216, B_217, C_218), A_216) | r2_hidden('#skF_2'(A_216, B_217, C_218), C_218) | k4_xboole_0(A_216, B_217)=C_218)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.97/1.74  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.97/1.74  tff(c_1353, plain, (![A_236, C_237]: (r2_hidden('#skF_2'(A_236, A_236, C_237), C_237) | k4_xboole_0(A_236, A_236)=C_237)), inference(resolution, [status(thm)], [c_1100, c_18])).
% 3.97/1.74  tff(c_34, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.97/1.74  tff(c_204, plain, (![A_84, B_85]: (r2_hidden('#skF_4'(A_84, B_85), B_85) | ~r2_hidden(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.97/1.74  tff(c_56, plain, (![B_58, A_57]: (~r1_tarski(B_58, A_57) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.97/1.74  tff(c_414, plain, (![B_114, A_115]: (~r1_tarski(B_114, '#skF_4'(A_115, B_114)) | ~r2_hidden(A_115, B_114))), inference(resolution, [status(thm)], [c_204, c_56])).
% 3.97/1.74  tff(c_419, plain, (![A_115]: (~r2_hidden(A_115, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_414])).
% 3.97/1.74  tff(c_1391, plain, (![A_236]: (k4_xboole_0(A_236, A_236)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1353, c_419])).
% 3.97/1.74  tff(c_1171, plain, (![A_216, C_218]: (r2_hidden('#skF_2'(A_216, A_216, C_218), C_218) | k4_xboole_0(A_216, A_216)=C_218)), inference(resolution, [status(thm)], [c_1100, c_18])).
% 3.97/1.74  tff(c_1395, plain, (![A_216, C_218]: (r2_hidden('#skF_2'(A_216, A_216, C_218), C_218) | k1_xboole_0=C_218)), inference(demodulation, [status(thm), theory('equality')], [c_1391, c_1171])).
% 3.97/1.74  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.97/1.74  tff(c_26, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.97/1.74  tff(c_449, plain, (![D_121, A_122, B_123]: (~r2_hidden(D_121, '#skF_4'(A_122, B_123)) | ~r2_hidden(D_121, B_123) | ~r2_hidden(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.97/1.74  tff(c_2682, plain, (![A_339, A_340, B_341]: (~r2_hidden('#skF_3'(A_339, '#skF_4'(A_340, B_341)), B_341) | ~r2_hidden(A_340, B_341) | r1_xboole_0(A_339, '#skF_4'(A_340, B_341)))), inference(resolution, [status(thm)], [c_26, c_449])).
% 3.97/1.74  tff(c_2698, plain, (![A_342, A_343]: (~r2_hidden(A_342, A_343) | r1_xboole_0(A_343, '#skF_4'(A_342, A_343)))), inference(resolution, [status(thm)], [c_28, c_2682])).
% 3.97/1.74  tff(c_22, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.97/1.74  tff(c_2705, plain, (![A_344, A_345]: (r1_xboole_0('#skF_4'(A_344, A_345), A_345) | ~r2_hidden(A_344, A_345))), inference(resolution, [status(thm)], [c_2698, c_22])).
% 3.97/1.74  tff(c_58, plain, (![B_60]: (~r1_xboole_0(B_60, '#skF_5') | ~r2_hidden(B_60, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.97/1.74  tff(c_223, plain, (![A_84]: (~r1_xboole_0('#skF_4'(A_84, '#skF_5'), '#skF_5') | ~r2_hidden(A_84, '#skF_5'))), inference(resolution, [status(thm)], [c_204, c_58])).
% 3.97/1.74  tff(c_2717, plain, (![A_346]: (~r2_hidden(A_346, '#skF_5'))), inference(resolution, [status(thm)], [c_2705, c_223])).
% 3.97/1.74  tff(c_2739, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1395, c_2717])).
% 3.97/1.74  tff(c_2785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2739])).
% 3.97/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.74  
% 3.97/1.74  Inference rules
% 3.97/1.74  ----------------------
% 3.97/1.74  #Ref     : 0
% 3.97/1.74  #Sup     : 594
% 3.97/1.74  #Fact    : 0
% 3.97/1.74  #Define  : 0
% 3.97/1.74  #Split   : 1
% 3.97/1.74  #Chain   : 0
% 3.97/1.74  #Close   : 0
% 3.97/1.74  
% 3.97/1.74  Ordering : KBO
% 3.97/1.74  
% 3.97/1.74  Simplification rules
% 3.97/1.74  ----------------------
% 3.97/1.74  #Subsume      : 144
% 3.97/1.74  #Demod        : 298
% 3.97/1.74  #Tautology    : 217
% 3.97/1.74  #SimpNegUnit  : 18
% 3.97/1.74  #BackRed      : 5
% 3.97/1.74  
% 3.97/1.74  #Partial instantiations: 0
% 3.97/1.74  #Strategies tried      : 1
% 3.97/1.74  
% 3.97/1.74  Timing (in seconds)
% 3.97/1.74  ----------------------
% 3.97/1.74  Preprocessing        : 0.33
% 3.97/1.74  Parsing              : 0.17
% 3.97/1.74  CNF conversion       : 0.02
% 3.97/1.74  Main loop            : 0.61
% 3.97/1.74  Inferencing          : 0.22
% 3.97/1.74  Reduction            : 0.19
% 3.97/1.74  Demodulation         : 0.13
% 3.97/1.74  BG Simplification    : 0.03
% 3.97/1.75  Subsumption          : 0.13
% 3.97/1.75  Abstraction          : 0.03
% 3.97/1.75  MUC search           : 0.00
% 3.97/1.75  Cooper               : 0.00
% 3.97/1.75  Total                : 0.96
% 3.97/1.75  Index Insertion      : 0.00
% 3.97/1.75  Index Deletion       : 0.00
% 3.97/1.75  Index Matching       : 0.00
% 3.97/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
