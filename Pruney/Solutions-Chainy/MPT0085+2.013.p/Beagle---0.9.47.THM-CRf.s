%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:12 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   52 (  85 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 124 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_53,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,k3_xboole_0(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    ! [A_18,C_29] :
      ( ~ r1_xboole_0(A_18,k1_xboole_0)
      | ~ r2_hidden(C_29,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_53])).

tff(c_63,plain,(
    ! [C_30] : ~ r2_hidden(C_30,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_69,plain,(
    ! [B_31] : r1_tarski(k1_xboole_0,B_31) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_73,plain,(
    ! [B_31] : k2_xboole_0(k1_xboole_0,B_31) = B_31 ),
    inference(resolution,[status(thm)],[c_69,c_12])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_168,plain,(
    ! [A_41,B_42,B_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | r1_tarski(k3_xboole_0(A_41,B_42),B_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_199,plain,(
    ! [A_48,B_49,B_50] :
      ( k2_xboole_0(k3_xboole_0(A_48,B_49),B_50) = B_50
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_168,c_12])).

tff(c_30,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_39,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_30])).

tff(c_244,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_39])).

tff(c_258,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_244])).

tff(c_287,plain,(
    ! [A_53,B_54,C_55] : k2_xboole_0(k3_xboole_0(A_53,B_54),k3_xboole_0(A_53,C_55)) = k3_xboole_0(A_53,k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_303,plain,(
    ! [C_55] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_55)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_287])).

tff(c_330,plain,(
    ! [C_55] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_55)) = k3_xboole_0('#skF_3',C_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_303])).

tff(c_20,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_20])).

tff(c_388,plain,(
    ! [A_18] : ~ r1_xboole_0(A_18,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_420,plain,(
    ! [A_62,B_63,B_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | r1_tarski(k3_xboole_0(A_62,B_63),B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_432,plain,(
    ! [A_68,B_69,B_70] :
      ( k2_xboole_0(k3_xboole_0(A_68,B_69),B_70) = B_70
      | ~ r1_xboole_0(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_420,c_12])).

tff(c_470,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = k1_xboole_0
      | ~ r1_xboole_0(A_71,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_39])).

tff(c_474,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_470])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_484,plain,(
    ! [C_10] :
      ( ~ r1_xboole_0('#skF_3','#skF_4')
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_10])).

tff(c_495,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_484])).

tff(c_579,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_2'(A_77,B_78),k3_xboole_0(A_77,B_78))
      | r1_xboole_0(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_593,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_2'(A_18,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_18,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_579])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_495,c_593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:37:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.32  
% 2.08/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.08/1.32  
% 2.08/1.32  %Foreground sorts:
% 2.08/1.32  
% 2.08/1.32  
% 2.08/1.32  %Background operators:
% 2.08/1.32  
% 2.08/1.32  
% 2.08/1.32  %Foreground operators:
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.32  
% 2.08/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.08/1.33  tff(f_56, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.08/1.33  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.08/1.33  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.08/1.33  tff(f_61, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.08/1.33  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.08/1.33  tff(f_54, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.08/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.33  tff(c_18, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.33  tff(c_53, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, k3_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.33  tff(c_60, plain, (![A_18, C_29]: (~r1_xboole_0(A_18, k1_xboole_0) | ~r2_hidden(C_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_53])).
% 2.08/1.33  tff(c_63, plain, (![C_30]: (~r2_hidden(C_30, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_60])).
% 2.08/1.33  tff(c_69, plain, (![B_31]: (r1_tarski(k1_xboole_0, B_31))), inference(resolution, [status(thm)], [c_6, c_63])).
% 2.08/1.33  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.33  tff(c_73, plain, (![B_31]: (k2_xboole_0(k1_xboole_0, B_31)=B_31)), inference(resolution, [status(thm)], [c_69, c_12])).
% 2.08/1.33  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.33  tff(c_168, plain, (![A_41, B_42, B_43]: (~r1_xboole_0(A_41, B_42) | r1_tarski(k3_xboole_0(A_41, B_42), B_43))), inference(resolution, [status(thm)], [c_6, c_53])).
% 2.08/1.33  tff(c_199, plain, (![A_48, B_49, B_50]: (k2_xboole_0(k3_xboole_0(A_48, B_49), B_50)=B_50 | ~r1_xboole_0(A_48, B_49))), inference(resolution, [status(thm)], [c_168, c_12])).
% 2.08/1.33  tff(c_30, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k3_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.33  tff(c_39, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_18, c_30])).
% 2.08/1.33  tff(c_244, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_xboole_0(A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_199, c_39])).
% 2.08/1.33  tff(c_258, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_244])).
% 2.08/1.33  tff(c_287, plain, (![A_53, B_54, C_55]: (k2_xboole_0(k3_xboole_0(A_53, B_54), k3_xboole_0(A_53, C_55))=k3_xboole_0(A_53, k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.33  tff(c_303, plain, (![C_55]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_55))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_55)))), inference(superposition, [status(thm), theory('equality')], [c_258, c_287])).
% 2.08/1.33  tff(c_330, plain, (![C_55]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_55))=k3_xboole_0('#skF_3', C_55))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_303])).
% 2.08/1.33  tff(c_20, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.33  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_330, c_20])).
% 2.08/1.33  tff(c_388, plain, (![A_18]: (~r1_xboole_0(A_18, k1_xboole_0))), inference(splitRight, [status(thm)], [c_60])).
% 2.08/1.33  tff(c_420, plain, (![A_62, B_63, B_64]: (~r1_xboole_0(A_62, B_63) | r1_tarski(k3_xboole_0(A_62, B_63), B_64))), inference(resolution, [status(thm)], [c_6, c_53])).
% 2.08/1.33  tff(c_432, plain, (![A_68, B_69, B_70]: (k2_xboole_0(k3_xboole_0(A_68, B_69), B_70)=B_70 | ~r1_xboole_0(A_68, B_69))), inference(resolution, [status(thm)], [c_420, c_12])).
% 2.08/1.33  tff(c_470, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=k1_xboole_0 | ~r1_xboole_0(A_71, B_72))), inference(superposition, [status(thm), theory('equality')], [c_432, c_39])).
% 2.08/1.33  tff(c_474, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_470])).
% 2.08/1.33  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.33  tff(c_484, plain, (![C_10]: (~r1_xboole_0('#skF_3', '#skF_4') | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_474, c_10])).
% 2.08/1.33  tff(c_495, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_484])).
% 2.08/1.33  tff(c_579, plain, (![A_77, B_78]: (r2_hidden('#skF_2'(A_77, B_78), k3_xboole_0(A_77, B_78)) | r1_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.33  tff(c_593, plain, (![A_18]: (r2_hidden('#skF_2'(A_18, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_579])).
% 2.08/1.33  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_388, c_495, c_593])).
% 2.08/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.33  
% 2.08/1.33  Inference rules
% 2.08/1.33  ----------------------
% 2.08/1.33  #Ref     : 0
% 2.08/1.33  #Sup     : 131
% 2.08/1.33  #Fact    : 0
% 2.08/1.33  #Define  : 0
% 2.08/1.33  #Split   : 1
% 2.08/1.33  #Chain   : 0
% 2.08/1.33  #Close   : 0
% 2.08/1.33  
% 2.08/1.33  Ordering : KBO
% 2.08/1.33  
% 2.08/1.33  Simplification rules
% 2.08/1.33  ----------------------
% 2.08/1.33  #Subsume      : 6
% 2.08/1.33  #Demod        : 50
% 2.08/1.33  #Tautology    : 81
% 2.08/1.33  #SimpNegUnit  : 6
% 2.08/1.33  #BackRed      : 1
% 2.08/1.33  
% 2.08/1.33  #Partial instantiations: 0
% 2.08/1.33  #Strategies tried      : 1
% 2.08/1.33  
% 2.08/1.33  Timing (in seconds)
% 2.08/1.33  ----------------------
% 2.35/1.34  Preprocessing        : 0.29
% 2.35/1.34  Parsing              : 0.16
% 2.35/1.34  CNF conversion       : 0.02
% 2.35/1.34  Main loop            : 0.25
% 2.35/1.34  Inferencing          : 0.11
% 2.35/1.34  Reduction            : 0.07
% 2.35/1.34  Demodulation         : 0.05
% 2.35/1.34  BG Simplification    : 0.01
% 2.35/1.34  Subsumption          : 0.03
% 2.35/1.34  Abstraction          : 0.01
% 2.35/1.34  MUC search           : 0.00
% 2.35/1.34  Cooper               : 0.00
% 2.35/1.34  Total                : 0.57
% 2.35/1.34  Index Insertion      : 0.00
% 2.35/1.34  Index Deletion       : 0.00
% 2.35/1.34  Index Matching       : 0.00
% 2.35/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
