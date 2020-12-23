%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:29 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   55 (  90 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 ( 113 expanded)
%              Number of equality atoms :   34 (  66 expanded)
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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_71,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

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

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_80,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_80])).

tff(c_145,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_163,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_145])).

tff(c_172,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_163])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_169,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_145])).

tff(c_174,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_169])).

tff(c_683,plain,(
    ! [A_64,B_65,C_66] : k2_xboole_0(k4_xboole_0(A_64,B_65),k3_xboole_0(A_64,C_66)) = k4_xboole_0(A_64,k4_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_816,plain,(
    ! [C_70] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_70)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_683])).

tff(c_852,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_816])).

tff(c_868,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_20,c_852])).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_91,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_80])).

tff(c_166,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_145])).

tff(c_173,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_166])).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_107,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_136,plain,(
    ! [A_40,B_41] :
      ( ~ r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_107])).

tff(c_144,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_136])).

tff(c_261,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_282,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_261])).

tff(c_297,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_282])).

tff(c_844,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3','#skF_5')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_816])).

tff(c_866,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_92,c_844])).

tff(c_875,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_866])).

tff(c_876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_875])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:26:00 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.42  
% 2.59/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.59/1.42  
% 2.59/1.42  %Foreground sorts:
% 2.59/1.42  
% 2.59/1.42  
% 2.59/1.42  %Background operators:
% 2.59/1.42  
% 2.59/1.42  
% 2.59/1.42  %Foreground operators:
% 2.59/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.59/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.59/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.42  
% 2.59/1.43  tff(f_80, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.59/1.43  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.59/1.43  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.59/1.43  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.59/1.43  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.59/1.43  tff(f_71, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.59/1.43  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.59/1.43  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.59/1.43  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.59/1.43  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.43  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.59/1.43  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.43  tff(c_80, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.59/1.43  tff(c_92, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_80])).
% 2.59/1.43  tff(c_145, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.59/1.43  tff(c_163, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_92, c_145])).
% 2.59/1.43  tff(c_172, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_163])).
% 2.59/1.43  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.59/1.43  tff(c_169, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_145])).
% 2.59/1.43  tff(c_174, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_169])).
% 2.59/1.43  tff(c_683, plain, (![A_64, B_65, C_66]: (k2_xboole_0(k4_xboole_0(A_64, B_65), k3_xboole_0(A_64, C_66))=k4_xboole_0(A_64, k4_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.59/1.43  tff(c_816, plain, (![C_70]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_70))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_70)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_683])).
% 2.59/1.43  tff(c_852, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_174, c_816])).
% 2.59/1.43  tff(c_868, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_20, c_852])).
% 2.59/1.43  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.43  tff(c_91, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_80])).
% 2.59/1.43  tff(c_166, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_145])).
% 2.59/1.43  tff(c_173, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_166])).
% 2.59/1.43  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.43  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.43  tff(c_107, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.43  tff(c_136, plain, (![A_40, B_41]: (~r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_107])).
% 2.59/1.43  tff(c_144, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_136])).
% 2.59/1.43  tff(c_261, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.59/1.43  tff(c_282, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_144, c_261])).
% 2.59/1.43  tff(c_297, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_282])).
% 2.59/1.43  tff(c_844, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', '#skF_5'))=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_297, c_816])).
% 2.59/1.43  tff(c_866, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_173, c_92, c_844])).
% 2.59/1.43  tff(c_875, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_868, c_866])).
% 2.59/1.43  tff(c_876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_875])).
% 2.59/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.43  
% 2.59/1.43  Inference rules
% 2.59/1.43  ----------------------
% 2.59/1.43  #Ref     : 0
% 2.59/1.43  #Sup     : 208
% 2.59/1.43  #Fact    : 0
% 2.59/1.43  #Define  : 0
% 2.59/1.43  #Split   : 5
% 2.59/1.43  #Chain   : 0
% 2.59/1.43  #Close   : 0
% 2.59/1.43  
% 2.59/1.43  Ordering : KBO
% 2.59/1.43  
% 2.59/1.43  Simplification rules
% 2.59/1.43  ----------------------
% 2.59/1.43  #Subsume      : 13
% 2.59/1.43  #Demod        : 129
% 2.59/1.43  #Tautology    : 125
% 2.59/1.43  #SimpNegUnit  : 14
% 2.59/1.43  #BackRed      : 1
% 2.59/1.43  
% 2.59/1.43  #Partial instantiations: 0
% 2.59/1.43  #Strategies tried      : 1
% 2.59/1.43  
% 2.59/1.43  Timing (in seconds)
% 2.59/1.43  ----------------------
% 2.59/1.43  Preprocessing        : 0.32
% 2.59/1.43  Parsing              : 0.17
% 2.59/1.43  CNF conversion       : 0.02
% 2.59/1.43  Main loop            : 0.31
% 2.59/1.43  Inferencing          : 0.12
% 2.59/1.43  Reduction            : 0.11
% 2.59/1.43  Demodulation         : 0.08
% 2.59/1.43  BG Simplification    : 0.02
% 2.59/1.43  Subsumption          : 0.04
% 2.59/1.43  Abstraction          : 0.02
% 2.59/1.43  MUC search           : 0.00
% 2.59/1.43  Cooper               : 0.00
% 2.59/1.43  Total                : 0.66
% 2.59/1.43  Index Insertion      : 0.00
% 2.59/1.43  Index Deletion       : 0.00
% 2.59/1.43  Index Matching       : 0.00
% 2.59/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
