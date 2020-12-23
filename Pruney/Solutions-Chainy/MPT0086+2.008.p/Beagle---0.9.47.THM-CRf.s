%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:14 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   58 (  98 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 122 expanded)
%              Number of equality atoms :   21 (  49 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_30,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_174,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_156])).

tff(c_185,plain,(
    ! [A_42] : k4_xboole_0(A_42,A_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_174])).

tff(c_32,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_193,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_xboole_0) = k3_xboole_0(A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_32])).

tff(c_208,plain,(
    ! [A_42] : k3_xboole_0(A_42,A_42) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_193])).

tff(c_245,plain,(
    ! [A_46,B_47,C_48] : k4_xboole_0(k3_xboole_0(A_46,B_47),C_48) = k3_xboole_0(A_46,k4_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_275,plain,(
    ! [A_42,C_48] : k3_xboole_0(A_42,k4_xboole_0(A_42,C_48)) = k4_xboole_0(A_42,C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_245])).

tff(c_159,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,k4_xboole_0(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_32])).

tff(c_1558,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k4_xboole_0(A_37,B_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_159])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_140,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_152,plain,(
    ! [A_16,C_35] :
      ( ~ r1_xboole_0(A_16,k1_xboole_0)
      | ~ r2_hidden(C_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_140])).

tff(c_154,plain,(
    ! [C_35] : ~ r2_hidden(C_35,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_177,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_174])).

tff(c_462,plain,(
    ! [A_63,B_64] : k3_xboole_0(A_63,k4_xboole_0(B_64,k3_xboole_0(A_63,B_64))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_177])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),k3_xboole_0(A_11,B_12))
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_470,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_3'(A_63,k4_xboole_0(B_64,k3_xboole_0(A_63,B_64))),k1_xboole_0)
      | r1_xboole_0(A_63,k4_xboole_0(B_64,k3_xboole_0(A_63,B_64))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_24])).

tff(c_528,plain,(
    ! [A_65,B_66] : r1_xboole_0(A_65,k4_xboole_0(B_66,k3_xboole_0(A_65,B_66))) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_470])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_562,plain,(
    ! [B_67,A_68] : r1_xboole_0(k4_xboole_0(B_67,k3_xboole_0(A_68,B_67)),A_68) ),
    inference(resolution,[status(thm)],[c_528,c_22])).

tff(c_583,plain,(
    ! [B_2,A_1] : r1_xboole_0(k4_xboole_0(B_2,k3_xboole_0(B_2,A_1)),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_562])).

tff(c_1560,plain,(
    ! [B_2,A_1] : r1_xboole_0(k4_xboole_0(B_2,A_1),A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_583])).

tff(c_36,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_36])).

tff(c_1693,plain,(
    ! [A_16] : ~ r1_xboole_0(A_16,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_1865,plain,(
    ! [A_155,B_156] :
      ( r2_hidden('#skF_3'(A_155,B_156),k3_xboole_0(A_155,B_156))
      | r1_xboole_0(A_155,B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1883,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_3'(A_16,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_16,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1865])).

tff(c_1887,plain,(
    ! [A_157] : r2_hidden('#skF_3'(A_157,k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1693,c_1883])).

tff(c_1854,plain,(
    ! [D_150,B_151,A_152] :
      ( ~ r2_hidden(D_150,B_151)
      | ~ r2_hidden(D_150,k4_xboole_0(A_152,B_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1863,plain,(
    ! [D_150,A_17] :
      ( ~ r2_hidden(D_150,k1_xboole_0)
      | ~ r2_hidden(D_150,A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1854])).

tff(c_1892,plain,(
    ! [A_157,A_17] : ~ r2_hidden('#skF_3'(A_157,k1_xboole_0),A_17) ),
    inference(resolution,[status(thm)],[c_1887,c_1863])).

tff(c_1886,plain,(
    ! [A_16] : r2_hidden('#skF_3'(A_16,k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1693,c_1883])).

tff(c_1902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1892,c_1886])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:29:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.62  
% 3.38/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.62  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.38/1.62  
% 3.38/1.62  %Foreground sorts:
% 3.38/1.62  
% 3.38/1.62  
% 3.38/1.62  %Background operators:
% 3.38/1.62  
% 3.38/1.62  
% 3.38/1.62  %Foreground operators:
% 3.38/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.38/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.38/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.38/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.38/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.62  
% 3.38/1.63  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.38/1.63  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.38/1.63  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.38/1.63  tff(f_63, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.38/1.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.38/1.63  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.38/1.63  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.38/1.63  tff(f_66, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.38/1.63  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.38/1.63  tff(c_30, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.38/1.63  tff(c_28, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.38/1.63  tff(c_156, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.38/1.63  tff(c_174, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_156])).
% 3.38/1.63  tff(c_185, plain, (![A_42]: (k4_xboole_0(A_42, A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_174])).
% 3.38/1.63  tff(c_32, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.38/1.63  tff(c_193, plain, (![A_42]: (k4_xboole_0(A_42, k1_xboole_0)=k3_xboole_0(A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_185, c_32])).
% 3.38/1.63  tff(c_208, plain, (![A_42]: (k3_xboole_0(A_42, A_42)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_193])).
% 3.38/1.63  tff(c_245, plain, (![A_46, B_47, C_48]: (k4_xboole_0(k3_xboole_0(A_46, B_47), C_48)=k3_xboole_0(A_46, k4_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.38/1.63  tff(c_275, plain, (![A_42, C_48]: (k3_xboole_0(A_42, k4_xboole_0(A_42, C_48))=k4_xboole_0(A_42, C_48))), inference(superposition, [status(thm), theory('equality')], [c_208, c_245])).
% 3.38/1.63  tff(c_159, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k3_xboole_0(A_37, k4_xboole_0(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_32])).
% 3.38/1.63  tff(c_1558, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k4_xboole_0(A_37, B_38))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_159])).
% 3.38/1.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.38/1.63  tff(c_140, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.38/1.63  tff(c_152, plain, (![A_16, C_35]: (~r1_xboole_0(A_16, k1_xboole_0) | ~r2_hidden(C_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_140])).
% 3.38/1.63  tff(c_154, plain, (![C_35]: (~r2_hidden(C_35, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_152])).
% 3.38/1.63  tff(c_177, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_174])).
% 3.38/1.63  tff(c_462, plain, (![A_63, B_64]: (k3_xboole_0(A_63, k4_xboole_0(B_64, k3_xboole_0(A_63, B_64)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_245, c_177])).
% 3.38/1.63  tff(c_24, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), k3_xboole_0(A_11, B_12)) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.38/1.63  tff(c_470, plain, (![A_63, B_64]: (r2_hidden('#skF_3'(A_63, k4_xboole_0(B_64, k3_xboole_0(A_63, B_64))), k1_xboole_0) | r1_xboole_0(A_63, k4_xboole_0(B_64, k3_xboole_0(A_63, B_64))))), inference(superposition, [status(thm), theory('equality')], [c_462, c_24])).
% 3.38/1.63  tff(c_528, plain, (![A_65, B_66]: (r1_xboole_0(A_65, k4_xboole_0(B_66, k3_xboole_0(A_65, B_66))))), inference(negUnitSimplification, [status(thm)], [c_154, c_470])).
% 3.38/1.63  tff(c_22, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.63  tff(c_562, plain, (![B_67, A_68]: (r1_xboole_0(k4_xboole_0(B_67, k3_xboole_0(A_68, B_67)), A_68))), inference(resolution, [status(thm)], [c_528, c_22])).
% 3.38/1.63  tff(c_583, plain, (![B_2, A_1]: (r1_xboole_0(k4_xboole_0(B_2, k3_xboole_0(B_2, A_1)), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_562])).
% 3.38/1.63  tff(c_1560, plain, (![B_2, A_1]: (r1_xboole_0(k4_xboole_0(B_2, A_1), A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_583])).
% 3.38/1.63  tff(c_36, plain, (~r1_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.38/1.63  tff(c_1692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1560, c_36])).
% 3.38/1.63  tff(c_1693, plain, (![A_16]: (~r1_xboole_0(A_16, k1_xboole_0))), inference(splitRight, [status(thm)], [c_152])).
% 3.38/1.63  tff(c_1865, plain, (![A_155, B_156]: (r2_hidden('#skF_3'(A_155, B_156), k3_xboole_0(A_155, B_156)) | r1_xboole_0(A_155, B_156))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.38/1.63  tff(c_1883, plain, (![A_16]: (r2_hidden('#skF_3'(A_16, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1865])).
% 3.38/1.63  tff(c_1887, plain, (![A_157]: (r2_hidden('#skF_3'(A_157, k1_xboole_0), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1693, c_1883])).
% 3.38/1.63  tff(c_1854, plain, (![D_150, B_151, A_152]: (~r2_hidden(D_150, B_151) | ~r2_hidden(D_150, k4_xboole_0(A_152, B_151)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.38/1.63  tff(c_1863, plain, (![D_150, A_17]: (~r2_hidden(D_150, k1_xboole_0) | ~r2_hidden(D_150, A_17))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1854])).
% 3.38/1.63  tff(c_1892, plain, (![A_157, A_17]: (~r2_hidden('#skF_3'(A_157, k1_xboole_0), A_17))), inference(resolution, [status(thm)], [c_1887, c_1863])).
% 3.38/1.63  tff(c_1886, plain, (![A_16]: (r2_hidden('#skF_3'(A_16, k1_xboole_0), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1693, c_1883])).
% 3.38/1.63  tff(c_1902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1892, c_1886])).
% 3.38/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.63  
% 3.38/1.63  Inference rules
% 3.38/1.63  ----------------------
% 3.38/1.63  #Ref     : 0
% 3.38/1.63  #Sup     : 443
% 3.38/1.63  #Fact    : 0
% 3.38/1.63  #Define  : 0
% 3.38/1.63  #Split   : 2
% 3.38/1.63  #Chain   : 0
% 3.38/1.63  #Close   : 0
% 3.38/1.63  
% 3.38/1.63  Ordering : KBO
% 3.38/1.63  
% 3.38/1.63  Simplification rules
% 3.38/1.63  ----------------------
% 3.38/1.63  #Subsume      : 60
% 3.38/1.63  #Demod        : 254
% 3.38/1.63  #Tautology    : 213
% 3.38/1.63  #SimpNegUnit  : 16
% 3.38/1.63  #BackRed      : 5
% 3.38/1.63  
% 3.38/1.63  #Partial instantiations: 0
% 3.38/1.63  #Strategies tried      : 1
% 3.38/1.63  
% 3.38/1.63  Timing (in seconds)
% 3.38/1.63  ----------------------
% 3.38/1.63  Preprocessing        : 0.32
% 3.38/1.63  Parsing              : 0.16
% 3.38/1.63  CNF conversion       : 0.02
% 3.38/1.64  Main loop            : 0.50
% 3.38/1.64  Inferencing          : 0.17
% 3.38/1.64  Reduction            : 0.18
% 3.38/1.64  Demodulation         : 0.14
% 3.38/1.64  BG Simplification    : 0.02
% 3.38/1.64  Subsumption          : 0.08
% 3.38/1.64  Abstraction          : 0.03
% 3.38/1.64  MUC search           : 0.00
% 3.38/1.64  Cooper               : 0.00
% 3.38/1.64  Total                : 0.84
% 3.38/1.64  Index Insertion      : 0.00
% 3.38/1.64  Index Deletion       : 0.00
% 3.38/1.64  Index Matching       : 0.00
% 3.38/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
