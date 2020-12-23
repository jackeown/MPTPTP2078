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
% DateTime   : Thu Dec  3 09:57:34 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   44 (  81 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 167 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9),A_8)
      | r1_setfam_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    ! [D_24,B_25,A_26] :
      ( ~ r2_hidden(D_24,B_25)
      | ~ r2_hidden(D_24,k4_xboole_0(A_26,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [D_29,A_30] :
      ( ~ r2_hidden(D_29,A_30)
      | ~ r2_hidden(D_29,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_44])).

tff(c_63,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden('#skF_3'(A_31,B_32),k1_xboole_0)
      | r1_setfam_1(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_28,c_59])).

tff(c_68,plain,(
    ! [B_9] : r1_setfam_1(k1_xboole_0,B_9) ),
    inference(resolution,[status(thm)],[c_28,c_63])).

tff(c_247,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden('#skF_1'(A_77,B_78,C_79),A_77)
      | r2_hidden('#skF_2'(A_77,B_78,C_79),C_79)
      | k4_xboole_0(A_77,B_78) = C_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_888,plain,(
    ! [A_134,C_135] :
      ( r2_hidden('#skF_2'(A_134,A_134,C_135),C_135)
      | k4_xboole_0(A_134,A_134) = C_135 ) ),
    inference(resolution,[status(thm)],[c_247,c_16])).

tff(c_24,plain,(
    ! [A_8,B_9,C_18] :
      ( r2_hidden('#skF_4'(A_8,B_9,C_18),B_9)
      | ~ r2_hidden(C_18,A_8)
      | ~ r1_setfam_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_98,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden('#skF_4'(A_46,B_47,C_48),B_47)
      | ~ r2_hidden(C_48,A_46)
      | ~ r1_setfam_1(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_47,plain,(
    ! [D_24,A_7] :
      ( ~ r2_hidden(D_24,A_7)
      | ~ r2_hidden(D_24,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_44])).

tff(c_171,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r2_hidden('#skF_4'(A_60,B_61,C_62),k1_xboole_0)
      | ~ r2_hidden(C_62,A_60)
      | ~ r1_setfam_1(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_98,c_47])).

tff(c_176,plain,(
    ! [C_18,A_8] :
      ( ~ r2_hidden(C_18,A_8)
      | ~ r1_setfam_1(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_171])).

tff(c_931,plain,(
    ! [C_136,A_137] :
      ( ~ r1_setfam_1(C_136,k1_xboole_0)
      | k4_xboole_0(A_137,A_137) = C_136 ) ),
    inference(resolution,[status(thm)],[c_888,c_176])).

tff(c_963,plain,(
    ! [A_138] : k4_xboole_0(A_138,A_138) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_931])).

tff(c_32,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_182,plain,(
    ! [C_66,A_67] :
      ( ~ r2_hidden(C_66,A_67)
      | ~ r1_setfam_1(A_67,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_171])).

tff(c_199,plain,(
    ! [A_68,B_69] :
      ( ~ r1_setfam_1(A_68,k1_xboole_0)
      | r1_setfam_1(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_28,c_182])).

tff(c_212,plain,(
    ! [B_69] : r1_setfam_1('#skF_5',B_69) ),
    inference(resolution,[status(thm)],[c_32,c_199])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_426,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_2'(A_96,B_97,A_96),A_96)
      | k4_xboole_0(A_96,B_97) = A_96 ) ),
    inference(resolution,[status(thm)],[c_247,c_14])).

tff(c_456,plain,(
    ! [A_98,B_99] :
      ( ~ r1_setfam_1(A_98,k1_xboole_0)
      | k4_xboole_0(A_98,B_99) = A_98 ) ),
    inference(resolution,[status(thm)],[c_426,c_176])).

tff(c_474,plain,(
    ! [B_99] : k4_xboole_0('#skF_5',B_99) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_212,c_456])).

tff(c_970,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_963,c_474])).

tff(c_1007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_970])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.36  
% 2.60/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.36  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2
% 2.60/1.36  
% 2.60/1.36  %Foreground sorts:
% 2.60/1.36  
% 2.60/1.36  
% 2.60/1.36  %Background operators:
% 2.60/1.36  
% 2.60/1.36  
% 2.60/1.36  %Foreground operators:
% 2.60/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.36  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.60/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.60/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.60/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.36  
% 2.60/1.37  tff(f_54, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.60/1.37  tff(f_49, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.60/1.37  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.60/1.37  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.60/1.37  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.60/1.37  tff(c_28, plain, (![A_8, B_9]: (r2_hidden('#skF_3'(A_8, B_9), A_8) | r1_setfam_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.37  tff(c_20, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.60/1.37  tff(c_44, plain, (![D_24, B_25, A_26]: (~r2_hidden(D_24, B_25) | ~r2_hidden(D_24, k4_xboole_0(A_26, B_25)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.37  tff(c_59, plain, (![D_29, A_30]: (~r2_hidden(D_29, A_30) | ~r2_hidden(D_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_44])).
% 2.60/1.37  tff(c_63, plain, (![A_31, B_32]: (~r2_hidden('#skF_3'(A_31, B_32), k1_xboole_0) | r1_setfam_1(A_31, B_32))), inference(resolution, [status(thm)], [c_28, c_59])).
% 2.60/1.37  tff(c_68, plain, (![B_9]: (r1_setfam_1(k1_xboole_0, B_9))), inference(resolution, [status(thm)], [c_28, c_63])).
% 2.60/1.37  tff(c_247, plain, (![A_77, B_78, C_79]: (r2_hidden('#skF_1'(A_77, B_78, C_79), A_77) | r2_hidden('#skF_2'(A_77, B_78, C_79), C_79) | k4_xboole_0(A_77, B_78)=C_79)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.37  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.37  tff(c_888, plain, (![A_134, C_135]: (r2_hidden('#skF_2'(A_134, A_134, C_135), C_135) | k4_xboole_0(A_134, A_134)=C_135)), inference(resolution, [status(thm)], [c_247, c_16])).
% 2.60/1.37  tff(c_24, plain, (![A_8, B_9, C_18]: (r2_hidden('#skF_4'(A_8, B_9, C_18), B_9) | ~r2_hidden(C_18, A_8) | ~r1_setfam_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.37  tff(c_98, plain, (![A_46, B_47, C_48]: (r2_hidden('#skF_4'(A_46, B_47, C_48), B_47) | ~r2_hidden(C_48, A_46) | ~r1_setfam_1(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.37  tff(c_47, plain, (![D_24, A_7]: (~r2_hidden(D_24, A_7) | ~r2_hidden(D_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_44])).
% 2.60/1.37  tff(c_171, plain, (![A_60, B_61, C_62]: (~r2_hidden('#skF_4'(A_60, B_61, C_62), k1_xboole_0) | ~r2_hidden(C_62, A_60) | ~r1_setfam_1(A_60, B_61))), inference(resolution, [status(thm)], [c_98, c_47])).
% 2.60/1.37  tff(c_176, plain, (![C_18, A_8]: (~r2_hidden(C_18, A_8) | ~r1_setfam_1(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_171])).
% 2.60/1.37  tff(c_931, plain, (![C_136, A_137]: (~r1_setfam_1(C_136, k1_xboole_0) | k4_xboole_0(A_137, A_137)=C_136)), inference(resolution, [status(thm)], [c_888, c_176])).
% 2.60/1.37  tff(c_963, plain, (![A_138]: (k4_xboole_0(A_138, A_138)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_931])).
% 2.60/1.37  tff(c_32, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.60/1.37  tff(c_182, plain, (![C_66, A_67]: (~r2_hidden(C_66, A_67) | ~r1_setfam_1(A_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_171])).
% 2.60/1.37  tff(c_199, plain, (![A_68, B_69]: (~r1_setfam_1(A_68, k1_xboole_0) | r1_setfam_1(A_68, B_69))), inference(resolution, [status(thm)], [c_28, c_182])).
% 2.60/1.37  tff(c_212, plain, (![B_69]: (r1_setfam_1('#skF_5', B_69))), inference(resolution, [status(thm)], [c_32, c_199])).
% 2.60/1.37  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.37  tff(c_426, plain, (![A_96, B_97]: (r2_hidden('#skF_2'(A_96, B_97, A_96), A_96) | k4_xboole_0(A_96, B_97)=A_96)), inference(resolution, [status(thm)], [c_247, c_14])).
% 2.60/1.37  tff(c_456, plain, (![A_98, B_99]: (~r1_setfam_1(A_98, k1_xboole_0) | k4_xboole_0(A_98, B_99)=A_98)), inference(resolution, [status(thm)], [c_426, c_176])).
% 2.60/1.37  tff(c_474, plain, (![B_99]: (k4_xboole_0('#skF_5', B_99)='#skF_5')), inference(resolution, [status(thm)], [c_212, c_456])).
% 2.60/1.37  tff(c_970, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_963, c_474])).
% 2.60/1.37  tff(c_1007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_970])).
% 2.60/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.37  
% 2.60/1.37  Inference rules
% 2.60/1.37  ----------------------
% 2.60/1.37  #Ref     : 0
% 2.60/1.37  #Sup     : 229
% 2.60/1.37  #Fact    : 0
% 2.60/1.37  #Define  : 0
% 2.60/1.37  #Split   : 0
% 2.60/1.37  #Chain   : 0
% 2.60/1.37  #Close   : 0
% 2.60/1.37  
% 2.60/1.37  Ordering : KBO
% 2.60/1.37  
% 2.60/1.37  Simplification rules
% 2.60/1.37  ----------------------
% 2.60/1.37  #Subsume      : 35
% 2.60/1.37  #Demod        : 101
% 2.60/1.37  #Tautology    : 73
% 2.60/1.37  #SimpNegUnit  : 1
% 2.60/1.37  #BackRed      : 9
% 2.60/1.37  
% 2.60/1.37  #Partial instantiations: 0
% 2.60/1.37  #Strategies tried      : 1
% 2.60/1.37  
% 2.60/1.37  Timing (in seconds)
% 2.60/1.37  ----------------------
% 2.60/1.38  Preprocessing        : 0.27
% 2.60/1.38  Parsing              : 0.14
% 2.60/1.38  CNF conversion       : 0.02
% 2.60/1.38  Main loop            : 0.34
% 2.60/1.38  Inferencing          : 0.13
% 2.60/1.38  Reduction            : 0.09
% 2.60/1.38  Demodulation         : 0.06
% 2.60/1.38  BG Simplification    : 0.02
% 2.60/1.38  Subsumption          : 0.08
% 2.60/1.38  Abstraction          : 0.02
% 2.60/1.38  MUC search           : 0.00
% 2.60/1.38  Cooper               : 0.00
% 2.60/1.38  Total                : 0.64
% 2.60/1.38  Index Insertion      : 0.00
% 2.60/1.38  Index Deletion       : 0.00
% 2.60/1.38  Index Matching       : 0.00
% 2.60/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
