%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:39 EST 2020

% Result     : Theorem 4.86s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :   51 (  89 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 ( 100 expanded)
%              Number of equality atoms :   32 (  71 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_32,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1344,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r1_xboole_0(A_82,B_83)
      | ~ r2_hidden(C_84,k3_xboole_0(A_82,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2000,plain,(
    ! [A_103,B_104] :
      ( ~ r1_xboole_0(A_103,B_104)
      | k3_xboole_0(A_103,B_104) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_1344])).

tff(c_2018,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_2000])).

tff(c_28,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2113,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2018,c_28])).

tff(c_14,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_175,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_222,plain,(
    ! [A_14] : k2_xboole_0(k1_xboole_0,A_14) = A_14 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_175])).

tff(c_2383,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2113,c_222])).

tff(c_161,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(A_39,B_40)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_171,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_161])).

tff(c_1753,plain,(
    ! [A_98,C_99,B_100] : k2_xboole_0(k4_xboole_0(A_98,C_99),k4_xboole_0(B_100,C_99)) = k4_xboole_0(k2_xboole_0(A_98,B_100),C_99) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1844,plain,(
    ! [A_14,B_100] : k4_xboole_0(k2_xboole_0(A_14,B_100),A_14) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_100,A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_1753])).

tff(c_1884,plain,(
    ! [A_14,B_100] : k4_xboole_0(k2_xboole_0(A_14,B_100),A_14) = k4_xboole_0(B_100,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_1844])).

tff(c_34,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2017,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_2000])).

tff(c_2052,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2017,c_28])).

tff(c_2679,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2052,c_222])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_39,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_38])).

tff(c_6101,plain,(
    ! [A_164,B_165] : k4_xboole_0(k2_xboole_0(A_164,B_165),A_164) = k4_xboole_0(B_165,A_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_1844])).

tff(c_6247,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_6101])).

tff(c_6293,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2383,c_1884,c_2679,c_6247])).

tff(c_6295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:57:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.86/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.86/1.98  
% 4.86/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.86/1.98  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 4.86/1.98  
% 4.86/1.98  %Foreground sorts:
% 4.86/1.98  
% 4.86/1.98  
% 4.86/1.98  %Background operators:
% 4.86/1.98  
% 4.86/1.98  
% 4.86/1.98  %Foreground operators:
% 4.86/1.98  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.86/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.86/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.86/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.86/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.86/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.86/1.98  tff('#skF_5', type, '#skF_5': $i).
% 4.86/1.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.86/1.98  tff('#skF_3', type, '#skF_3': $i).
% 4.86/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.86/1.98  tff('#skF_4', type, '#skF_4': $i).
% 4.86/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.86/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.86/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.86/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.86/1.98  
% 4.86/1.99  tff(f_82, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 4.86/1.99  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.86/1.99  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.86/1.99  tff(f_71, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.86/1.99  tff(f_57, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.86/1.99  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.86/1.99  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.86/1.99  tff(f_65, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 4.86/1.99  tff(c_32, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.86/1.99  tff(c_36, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.86/1.99  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.86/1.99  tff(c_1344, plain, (![A_82, B_83, C_84]: (~r1_xboole_0(A_82, B_83) | ~r2_hidden(C_84, k3_xboole_0(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.86/1.99  tff(c_2000, plain, (![A_103, B_104]: (~r1_xboole_0(A_103, B_104) | k3_xboole_0(A_103, B_104)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1344])).
% 4.86/1.99  tff(c_2018, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_2000])).
% 4.86/1.99  tff(c_28, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.86/1.99  tff(c_2113, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2018, c_28])).
% 4.86/1.99  tff(c_14, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.86/1.99  tff(c_175, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.86/1.99  tff(c_222, plain, (![A_14]: (k2_xboole_0(k1_xboole_0, A_14)=A_14)), inference(superposition, [status(thm), theory('equality')], [c_14, c_175])).
% 4.86/1.99  tff(c_2383, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2113, c_222])).
% 4.86/1.99  tff(c_161, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(A_39, B_40))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.86/1.99  tff(c_171, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_161])).
% 4.86/1.99  tff(c_1753, plain, (![A_98, C_99, B_100]: (k2_xboole_0(k4_xboole_0(A_98, C_99), k4_xboole_0(B_100, C_99))=k4_xboole_0(k2_xboole_0(A_98, B_100), C_99))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.86/1.99  tff(c_1844, plain, (![A_14, B_100]: (k4_xboole_0(k2_xboole_0(A_14, B_100), A_14)=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_100, A_14)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_1753])).
% 4.86/1.99  tff(c_1884, plain, (![A_14, B_100]: (k4_xboole_0(k2_xboole_0(A_14, B_100), A_14)=k4_xboole_0(B_100, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_1844])).
% 4.86/1.99  tff(c_34, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.86/1.99  tff(c_2017, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_2000])).
% 4.86/1.99  tff(c_2052, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2017, c_28])).
% 4.86/1.99  tff(c_2679, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2052, c_222])).
% 4.86/1.99  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.86/1.99  tff(c_38, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.86/1.99  tff(c_39, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_38])).
% 4.86/1.99  tff(c_6101, plain, (![A_164, B_165]: (k4_xboole_0(k2_xboole_0(A_164, B_165), A_164)=k4_xboole_0(B_165, A_164))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_1844])).
% 4.86/1.99  tff(c_6247, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_39, c_6101])).
% 4.86/1.99  tff(c_6293, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2383, c_1884, c_2679, c_6247])).
% 4.86/1.99  tff(c_6295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_6293])).
% 4.86/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.86/1.99  
% 4.86/1.99  Inference rules
% 4.86/1.99  ----------------------
% 4.86/1.99  #Ref     : 0
% 4.86/1.99  #Sup     : 1584
% 4.86/1.99  #Fact    : 0
% 4.86/1.99  #Define  : 0
% 4.86/1.99  #Split   : 3
% 4.86/1.99  #Chain   : 0
% 4.86/1.99  #Close   : 0
% 4.86/1.99  
% 4.86/1.99  Ordering : KBO
% 4.86/1.99  
% 4.86/1.99  Simplification rules
% 4.86/1.99  ----------------------
% 4.86/1.99  #Subsume      : 60
% 4.86/1.99  #Demod        : 1620
% 4.86/1.99  #Tautology    : 1178
% 4.86/1.99  #SimpNegUnit  : 15
% 4.86/1.99  #BackRed      : 6
% 4.86/1.99  
% 4.86/1.99  #Partial instantiations: 0
% 4.86/1.99  #Strategies tried      : 1
% 4.86/1.99  
% 4.86/1.99  Timing (in seconds)
% 4.86/1.99  ----------------------
% 4.86/2.00  Preprocessing        : 0.30
% 4.86/2.00  Parsing              : 0.17
% 4.86/2.00  CNF conversion       : 0.02
% 4.86/2.00  Main loop            : 0.89
% 4.86/2.00  Inferencing          : 0.27
% 4.86/2.00  Reduction            : 0.42
% 4.86/2.00  Demodulation         : 0.35
% 4.86/2.00  BG Simplification    : 0.03
% 4.86/2.00  Subsumption          : 0.12
% 4.86/2.00  Abstraction          : 0.04
% 4.86/2.00  MUC search           : 0.00
% 4.86/2.00  Cooper               : 0.00
% 4.86/2.00  Total                : 1.22
% 4.86/2.00  Index Insertion      : 0.00
% 4.86/2.00  Index Deletion       : 0.00
% 4.86/2.00  Index Matching       : 0.00
% 4.86/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
