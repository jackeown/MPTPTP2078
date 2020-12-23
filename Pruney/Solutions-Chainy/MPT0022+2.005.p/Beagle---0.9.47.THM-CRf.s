%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:33 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 400 expanded)
%              Number of leaves         :   13 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :   96 (1084 expanded)
%              Number of equality atoms :   38 ( 357 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_41,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(A,B) = k1_xboole_0
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_36,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(c_197,plain,(
    ! [A_38,B_39,C_40] :
      ( r2_hidden('#skF_1'(A_38,B_39,C_40),B_39)
      | r2_hidden('#skF_1'(A_38,B_39,C_40),A_38)
      | r2_hidden('#skF_2'(A_38,B_39,C_40),C_40)
      | k2_xboole_0(A_38,B_39) = C_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_459,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54,A_53),B_54)
      | r2_hidden('#skF_2'(A_53,B_54,A_53),A_53)
      | k2_xboole_0(A_53,B_54) = A_53 ) ),
    inference(resolution,[status(thm)],[c_197,c_16])).

tff(c_505,plain,(
    ! [B_55] :
      ( r2_hidden('#skF_2'(B_55,B_55,B_55),B_55)
      | k2_xboole_0(B_55,B_55) = B_55 ) ),
    inference(resolution,[status(thm)],[c_459,c_16])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_267,plain,(
    ! [B_41,C_42] :
      ( ~ r2_hidden('#skF_2'(B_41,B_41,C_42),B_41)
      | k2_xboole_0(B_41,B_41) = C_42
      | r2_hidden('#skF_1'(B_41,B_41,C_42),B_41) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_10])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_291,plain,(
    ! [B_41] :
      ( ~ r2_hidden('#skF_2'(B_41,B_41,B_41),B_41)
      | k2_xboole_0(B_41,B_41) = B_41 ) ),
    inference(resolution,[status(thm)],[c_267,c_12])).

tff(c_534,plain,(
    ! [B_55] : k2_xboole_0(B_55,B_55) = B_55 ),
    inference(resolution,[status(thm)],[c_505,c_291])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_196,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k2_xboole_0(A_1,A_1) = C_3
      | r2_hidden('#skF_1'(A_1,A_1,C_3),A_1) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_18])).

tff(c_804,plain,(
    ! [A_70,C_71] :
      ( r2_hidden('#skF_2'(A_70,A_70,C_71),C_71)
      | C_71 = A_70
      | r2_hidden('#skF_1'(A_70,A_70,C_71),A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_196])).

tff(c_24,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [D_13,B_14,A_15] :
      ( ~ r2_hidden(D_13,B_14)
      | r2_hidden(D_13,k2_xboole_0(A_15,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_57,plain,(
    ! [D_18] :
      ( ~ r2_hidden(D_18,'#skF_4')
      | r2_hidden(D_18,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_46])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_49,plain,(
    ! [D_13,A_7] :
      ( ~ r2_hidden(D_13,k1_xboole_0)
      | r2_hidden(D_13,A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_46])).

tff(c_60,plain,(
    ! [D_18,A_7] :
      ( r2_hidden(D_18,A_7)
      | ~ r2_hidden(D_18,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_57,c_49])).

tff(c_856,plain,(
    ! [C_72,A_73] :
      ( r2_hidden('#skF_1'('#skF_4','#skF_4',C_72),A_73)
      | r2_hidden('#skF_2'('#skF_4','#skF_4',C_72),C_72)
      | C_72 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_804,c_60])).

tff(c_863,plain,(
    ! [A_73] :
      ( k2_xboole_0('#skF_4','#skF_4') = A_73
      | r2_hidden('#skF_2'('#skF_4','#skF_4',A_73),A_73)
      | A_73 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_856,c_16])).

tff(c_901,plain,(
    ! [A_74] :
      ( A_74 = '#skF_4'
      | r2_hidden('#skF_2'('#skF_4','#skF_4',A_74),A_74)
      | A_74 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_863])).

tff(c_38,plain,(
    ! [D_9,A_10,B_11] :
      ( ~ r2_hidden(D_9,A_10)
      | r2_hidden(D_9,k2_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    ! [D_9] :
      ( ~ r2_hidden(D_9,'#skF_3')
      | r2_hidden(D_9,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_38])).

tff(c_53,plain,(
    ! [D_16,A_17] :
      ( ~ r2_hidden(D_16,k1_xboole_0)
      | r2_hidden(D_16,A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_46])).

tff(c_56,plain,(
    ! [D_9,A_17] :
      ( r2_hidden(D_9,A_17)
      | ~ r2_hidden(D_9,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_53])).

tff(c_930,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_4','#skF_3'),A_17)
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_901,c_56])).

tff(c_932,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_930])).

tff(c_984,plain,(
    k2_xboole_0('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_24])).

tff(c_987,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_984])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_985,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_22])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_985])).

tff(c_1003,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_930])).

tff(c_1004,plain,(
    ! [A_77] : r2_hidden('#skF_2'('#skF_4','#skF_4','#skF_3'),A_77) ),
    inference(splitRight,[status(thm)],[c_930])).

tff(c_119,plain,(
    ! [B_2,C_3] :
      ( ~ r2_hidden('#skF_2'(B_2,B_2,C_3),B_2)
      | k2_xboole_0(B_2,B_2) = C_3
      | r2_hidden('#skF_1'(B_2,B_2,C_3),B_2) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_10])).

tff(c_580,plain,(
    ! [B_58,C_59] :
      ( ~ r2_hidden('#skF_2'(B_58,B_58,C_59),B_58)
      | C_59 = B_58
      | r2_hidden('#skF_1'(B_58,B_58,C_59),B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_119])).

tff(c_617,plain,(
    ! [C_60,A_61] :
      ( r2_hidden('#skF_1'('#skF_4','#skF_4',C_60),A_61)
      | ~ r2_hidden('#skF_2'('#skF_4','#skF_4',C_60),'#skF_4')
      | C_60 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_580,c_60])).

tff(c_620,plain,(
    ! [A_61] :
      ( k2_xboole_0('#skF_4','#skF_4') = A_61
      | ~ r2_hidden('#skF_2'('#skF_4','#skF_4',A_61),'#skF_4')
      | A_61 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_617,c_12])).

tff(c_642,plain,(
    ! [A_61] :
      ( A_61 = '#skF_4'
      | ~ r2_hidden('#skF_2'('#skF_4','#skF_4',A_61),'#skF_4')
      | A_61 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_620])).

tff(c_1008,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1004,c_642])).

tff(c_1025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1003,c_1003,c_1008])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 09:45:11 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.47  
% 2.74/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.48  %$ r2_hidden > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.74/1.48  
% 2.74/1.48  %Foreground sorts:
% 2.74/1.48  
% 2.74/1.48  
% 2.74/1.48  %Background operators:
% 2.74/1.48  
% 2.74/1.48  
% 2.74/1.48  %Foreground operators:
% 2.74/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.74/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.74/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.74/1.48  
% 3.02/1.49  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.02/1.49  tff(f_41, negated_conjecture, ~(![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 3.02/1.49  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.02/1.49  tff(c_197, plain, (![A_38, B_39, C_40]: (r2_hidden('#skF_1'(A_38, B_39, C_40), B_39) | r2_hidden('#skF_1'(A_38, B_39, C_40), A_38) | r2_hidden('#skF_2'(A_38, B_39, C_40), C_40) | k2_xboole_0(A_38, B_39)=C_40)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.02/1.49  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.02/1.49  tff(c_459, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54, A_53), B_54) | r2_hidden('#skF_2'(A_53, B_54, A_53), A_53) | k2_xboole_0(A_53, B_54)=A_53)), inference(resolution, [status(thm)], [c_197, c_16])).
% 3.02/1.49  tff(c_505, plain, (![B_55]: (r2_hidden('#skF_2'(B_55, B_55, B_55), B_55) | k2_xboole_0(B_55, B_55)=B_55)), inference(resolution, [status(thm)], [c_459, c_16])).
% 3.02/1.49  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.02/1.49  tff(c_267, plain, (![B_41, C_42]: (~r2_hidden('#skF_2'(B_41, B_41, C_42), B_41) | k2_xboole_0(B_41, B_41)=C_42 | r2_hidden('#skF_1'(B_41, B_41, C_42), B_41))), inference(factorization, [status(thm), theory('equality')], [c_10])).
% 3.02/1.49  tff(c_12, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.02/1.49  tff(c_291, plain, (![B_41]: (~r2_hidden('#skF_2'(B_41, B_41, B_41), B_41) | k2_xboole_0(B_41, B_41)=B_41)), inference(resolution, [status(thm)], [c_267, c_12])).
% 3.02/1.49  tff(c_534, plain, (![B_55]: (k2_xboole_0(B_55, B_55)=B_55)), inference(resolution, [status(thm)], [c_505, c_291])).
% 3.02/1.49  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.02/1.49  tff(c_196, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k2_xboole_0(A_1, A_1)=C_3 | r2_hidden('#skF_1'(A_1, A_1, C_3), A_1))), inference(factorization, [status(thm), theory('equality')], [c_18])).
% 3.02/1.49  tff(c_804, plain, (![A_70, C_71]: (r2_hidden('#skF_2'(A_70, A_70, C_71), C_71) | C_71=A_70 | r2_hidden('#skF_1'(A_70, A_70, C_71), A_70))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_196])).
% 3.02/1.49  tff(c_24, plain, (k2_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.02/1.49  tff(c_46, plain, (![D_13, B_14, A_15]: (~r2_hidden(D_13, B_14) | r2_hidden(D_13, k2_xboole_0(A_15, B_14)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.02/1.49  tff(c_57, plain, (![D_18]: (~r2_hidden(D_18, '#skF_4') | r2_hidden(D_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_46])).
% 3.02/1.49  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.02/1.49  tff(c_49, plain, (![D_13, A_7]: (~r2_hidden(D_13, k1_xboole_0) | r2_hidden(D_13, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_46])).
% 3.02/1.49  tff(c_60, plain, (![D_18, A_7]: (r2_hidden(D_18, A_7) | ~r2_hidden(D_18, '#skF_4'))), inference(resolution, [status(thm)], [c_57, c_49])).
% 3.02/1.49  tff(c_856, plain, (![C_72, A_73]: (r2_hidden('#skF_1'('#skF_4', '#skF_4', C_72), A_73) | r2_hidden('#skF_2'('#skF_4', '#skF_4', C_72), C_72) | C_72='#skF_4')), inference(resolution, [status(thm)], [c_804, c_60])).
% 3.02/1.49  tff(c_863, plain, (![A_73]: (k2_xboole_0('#skF_4', '#skF_4')=A_73 | r2_hidden('#skF_2'('#skF_4', '#skF_4', A_73), A_73) | A_73='#skF_4')), inference(resolution, [status(thm)], [c_856, c_16])).
% 3.02/1.49  tff(c_901, plain, (![A_74]: (A_74='#skF_4' | r2_hidden('#skF_2'('#skF_4', '#skF_4', A_74), A_74) | A_74='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_534, c_863])).
% 3.02/1.49  tff(c_38, plain, (![D_9, A_10, B_11]: (~r2_hidden(D_9, A_10) | r2_hidden(D_9, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.02/1.49  tff(c_44, plain, (![D_9]: (~r2_hidden(D_9, '#skF_3') | r2_hidden(D_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_38])).
% 3.02/1.49  tff(c_53, plain, (![D_16, A_17]: (~r2_hidden(D_16, k1_xboole_0) | r2_hidden(D_16, A_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_46])).
% 3.02/1.49  tff(c_56, plain, (![D_9, A_17]: (r2_hidden(D_9, A_17) | ~r2_hidden(D_9, '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_53])).
% 3.02/1.49  tff(c_930, plain, (![A_17]: (r2_hidden('#skF_2'('#skF_4', '#skF_4', '#skF_3'), A_17) | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_901, c_56])).
% 3.02/1.49  tff(c_932, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_930])).
% 3.02/1.49  tff(c_984, plain, (k2_xboole_0('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_932, c_24])).
% 3.02/1.49  tff(c_987, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_534, c_984])).
% 3.02/1.49  tff(c_22, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.02/1.49  tff(c_985, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_932, c_22])).
% 3.02/1.49  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_987, c_985])).
% 3.02/1.49  tff(c_1003, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_930])).
% 3.02/1.49  tff(c_1004, plain, (![A_77]: (r2_hidden('#skF_2'('#skF_4', '#skF_4', '#skF_3'), A_77))), inference(splitRight, [status(thm)], [c_930])).
% 3.02/1.49  tff(c_119, plain, (![B_2, C_3]: (~r2_hidden('#skF_2'(B_2, B_2, C_3), B_2) | k2_xboole_0(B_2, B_2)=C_3 | r2_hidden('#skF_1'(B_2, B_2, C_3), B_2))), inference(factorization, [status(thm), theory('equality')], [c_10])).
% 3.02/1.49  tff(c_580, plain, (![B_58, C_59]: (~r2_hidden('#skF_2'(B_58, B_58, C_59), B_58) | C_59=B_58 | r2_hidden('#skF_1'(B_58, B_58, C_59), B_58))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_119])).
% 3.02/1.49  tff(c_617, plain, (![C_60, A_61]: (r2_hidden('#skF_1'('#skF_4', '#skF_4', C_60), A_61) | ~r2_hidden('#skF_2'('#skF_4', '#skF_4', C_60), '#skF_4') | C_60='#skF_4')), inference(resolution, [status(thm)], [c_580, c_60])).
% 3.02/1.49  tff(c_620, plain, (![A_61]: (k2_xboole_0('#skF_4', '#skF_4')=A_61 | ~r2_hidden('#skF_2'('#skF_4', '#skF_4', A_61), '#skF_4') | A_61='#skF_4')), inference(resolution, [status(thm)], [c_617, c_12])).
% 3.02/1.49  tff(c_642, plain, (![A_61]: (A_61='#skF_4' | ~r2_hidden('#skF_2'('#skF_4', '#skF_4', A_61), '#skF_4') | A_61='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_534, c_620])).
% 3.02/1.49  tff(c_1008, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1004, c_642])).
% 3.02/1.49  tff(c_1025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1003, c_1003, c_1008])).
% 3.02/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.49  
% 3.02/1.49  Inference rules
% 3.02/1.49  ----------------------
% 3.02/1.49  #Ref     : 0
% 3.02/1.49  #Sup     : 194
% 3.02/1.49  #Fact    : 6
% 3.02/1.49  #Define  : 0
% 3.02/1.49  #Split   : 3
% 3.02/1.49  #Chain   : 0
% 3.02/1.49  #Close   : 0
% 3.02/1.49  
% 3.02/1.49  Ordering : KBO
% 3.02/1.49  
% 3.02/1.49  Simplification rules
% 3.02/1.49  ----------------------
% 3.02/1.49  #Subsume      : 58
% 3.02/1.49  #Demod        : 73
% 3.02/1.49  #Tautology    : 54
% 3.02/1.49  #SimpNegUnit  : 1
% 3.02/1.49  #BackRed      : 14
% 3.02/1.49  
% 3.02/1.49  #Partial instantiations: 0
% 3.02/1.49  #Strategies tried      : 1
% 3.02/1.49  
% 3.02/1.49  Timing (in seconds)
% 3.02/1.49  ----------------------
% 3.02/1.49  Preprocessing        : 0.30
% 3.02/1.49  Parsing              : 0.15
% 3.02/1.49  CNF conversion       : 0.02
% 3.02/1.49  Main loop            : 0.39
% 3.02/1.49  Inferencing          : 0.16
% 3.02/1.49  Reduction            : 0.09
% 3.02/1.49  Demodulation         : 0.06
% 3.02/1.49  BG Simplification    : 0.02
% 3.02/1.49  Subsumption          : 0.09
% 3.02/1.49  Abstraction          : 0.02
% 3.02/1.49  MUC search           : 0.00
% 3.02/1.49  Cooper               : 0.00
% 3.02/1.49  Total                : 0.72
% 3.02/1.49  Index Insertion      : 0.00
% 3.02/1.49  Index Deletion       : 0.00
% 3.02/1.49  Index Matching       : 0.00
% 3.02/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
