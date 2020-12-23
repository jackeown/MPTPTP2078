%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:40 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  96 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_45,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_32,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_326,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),B_55)
      | r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_978,plain,(
    ! [A_86,B_87,A_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | r1_xboole_0(A_88,k3_xboole_0(A_86,B_87)) ) ),
    inference(resolution,[status(thm)],[c_326,c_12])).

tff(c_28,plain,(
    ! [A_23] :
      ( ~ r1_xboole_0(A_23,A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_992,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = k1_xboole_0
      | ~ r1_xboole_0(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_978,c_28])).

tff(c_1013,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_992])).

tff(c_24,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1052,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1013,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_701,plain,(
    ! [A_74,B_75] : k4_xboole_0(k2_xboole_0(A_74,B_75),B_75) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_749,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_701])).

tff(c_38,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_39,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_38])).

tff(c_802,plain,(
    ! [A_78,B_79] : k4_xboole_0(k2_xboole_0(A_78,B_79),A_78) = k4_xboole_0(B_79,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_701])).

tff(c_852,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_802])).

tff(c_869,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_852])).

tff(c_34,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1012,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_992])).

tff(c_1026,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_24])).

tff(c_1036,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_1026])).

tff(c_1160,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_1036])).

tff(c_1162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.47  
% 2.73/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.73/1.47  
% 2.73/1.47  %Foreground sorts:
% 2.73/1.47  
% 2.73/1.47  
% 2.73/1.47  %Background operators:
% 2.73/1.47  
% 2.73/1.47  
% 2.73/1.47  %Foreground operators:
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.47  
% 2.87/1.48  tff(f_94, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 2.87/1.48  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.87/1.48  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.87/1.48  tff(f_83, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.87/1.48  tff(f_71, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.87/1.48  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.87/1.48  tff(f_67, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.87/1.48  tff(c_32, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.87/1.48  tff(c_36, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.87/1.48  tff(c_326, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), B_55) | r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.87/1.48  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.87/1.48  tff(c_978, plain, (![A_86, B_87, A_88]: (~r1_xboole_0(A_86, B_87) | r1_xboole_0(A_88, k3_xboole_0(A_86, B_87)))), inference(resolution, [status(thm)], [c_326, c_12])).
% 2.87/1.48  tff(c_28, plain, (![A_23]: (~r1_xboole_0(A_23, A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.87/1.48  tff(c_992, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=k1_xboole_0 | ~r1_xboole_0(A_89, B_90))), inference(resolution, [status(thm)], [c_978, c_28])).
% 2.87/1.48  tff(c_1013, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_992])).
% 2.87/1.48  tff(c_24, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.48  tff(c_1052, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1013, c_24])).
% 2.87/1.48  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.87/1.48  tff(c_701, plain, (![A_74, B_75]: (k4_xboole_0(k2_xboole_0(A_74, B_75), B_75)=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.48  tff(c_749, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_701])).
% 2.87/1.48  tff(c_38, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.87/1.48  tff(c_39, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_38])).
% 2.87/1.48  tff(c_802, plain, (![A_78, B_79]: (k4_xboole_0(k2_xboole_0(A_78, B_79), A_78)=k4_xboole_0(B_79, A_78))), inference(superposition, [status(thm), theory('equality')], [c_2, c_701])).
% 2.87/1.48  tff(c_852, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_39, c_802])).
% 2.87/1.48  tff(c_869, plain, (k4_xboole_0('#skF_5', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_852])).
% 2.87/1.48  tff(c_34, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.87/1.48  tff(c_1012, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_992])).
% 2.87/1.48  tff(c_1026, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1012, c_24])).
% 2.87/1.48  tff(c_1036, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_869, c_1026])).
% 2.87/1.48  tff(c_1160, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_1036])).
% 2.87/1.48  tff(c_1162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1160])).
% 2.87/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.48  
% 2.87/1.48  Inference rules
% 2.87/1.48  ----------------------
% 2.87/1.48  #Ref     : 0
% 2.87/1.48  #Sup     : 291
% 2.87/1.48  #Fact    : 0
% 2.87/1.48  #Define  : 0
% 2.87/1.48  #Split   : 1
% 2.87/1.48  #Chain   : 0
% 2.87/1.48  #Close   : 0
% 2.87/1.48  
% 2.87/1.48  Ordering : KBO
% 2.87/1.48  
% 2.87/1.48  Simplification rules
% 2.87/1.48  ----------------------
% 2.87/1.48  #Subsume      : 6
% 2.87/1.48  #Demod        : 157
% 2.87/1.49  #Tautology    : 174
% 2.87/1.49  #SimpNegUnit  : 5
% 2.87/1.49  #BackRed      : 2
% 2.87/1.49  
% 2.87/1.49  #Partial instantiations: 0
% 2.87/1.49  #Strategies tried      : 1
% 2.87/1.49  
% 2.87/1.49  Timing (in seconds)
% 2.87/1.49  ----------------------
% 2.87/1.49  Preprocessing        : 0.30
% 2.87/1.49  Parsing              : 0.16
% 2.87/1.49  CNF conversion       : 0.02
% 2.87/1.49  Main loop            : 0.38
% 2.87/1.49  Inferencing          : 0.12
% 2.87/1.49  Reduction            : 0.15
% 2.87/1.49  Demodulation         : 0.12
% 2.87/1.49  BG Simplification    : 0.02
% 2.87/1.49  Subsumption          : 0.06
% 2.87/1.49  Abstraction          : 0.02
% 2.87/1.49  MUC search           : 0.00
% 2.87/1.49  Cooper               : 0.00
% 2.87/1.49  Total                : 0.71
% 2.87/1.49  Index Insertion      : 0.00
% 2.87/1.49  Index Deletion       : 0.00
% 2.87/1.49  Index Matching       : 0.00
% 2.87/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
