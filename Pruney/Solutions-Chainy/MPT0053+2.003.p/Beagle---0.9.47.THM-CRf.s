%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:51 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 139 expanded)
%              Number of leaves         :   17 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   52 ( 230 expanded)
%              Number of equality atoms :   29 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_1015,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_hidden('#skF_1'(A_74,B_75,C_76),A_74)
      | r2_hidden('#skF_2'(A_74,B_75,C_76),C_76)
      | k4_xboole_0(A_74,B_75) = C_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1294,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_2'(A_80,B_81,A_80),A_80)
      | k4_xboole_0(A_80,B_81) = A_80 ) ),
    inference(resolution,[status(thm)],[c_1015,c_16])).

tff(c_341,plain,(
    ! [D_47,A_48,B_49] :
      ( r2_hidden(D_47,k4_xboole_0(A_48,B_49))
      | r2_hidden(D_47,B_49)
      | ~ r2_hidden(D_47,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39,plain,(
    ! [B_16,A_17] : k2_xboole_0(B_16,A_17) = k2_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_55,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_22])).

tff(c_127,plain,(
    ! [A_22,B_23] : k4_xboole_0(k2_xboole_0(A_22,B_23),B_23) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_156,plain,(
    ! [A_27] : k4_xboole_0(k1_xboole_0,A_27) = k4_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_127])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_171,plain,(
    ! [D_8,A_27] :
      ( r2_hidden(D_8,A_27)
      | ~ r2_hidden(D_8,k4_xboole_0(k1_xboole_0,A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_8])).

tff(c_384,plain,(
    ! [D_47,B_49] :
      ( r2_hidden(D_47,B_49)
      | ~ r2_hidden(D_47,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_341,c_171])).

tff(c_1343,plain,(
    ! [B_81,B_49] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_81,k1_xboole_0),B_49)
      | k4_xboole_0(k1_xboole_0,B_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1294,c_384])).

tff(c_3948,plain,(
    ! [B_133,B_134] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_133,k1_xboole_0),B_134)
      | k4_xboole_0(k1_xboole_0,B_133) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1294,c_384])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4238,plain,(
    ! [B_138,B_139] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_138,k1_xboole_0),B_139)
      | k4_xboole_0(k1_xboole_0,B_138) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3948,c_6])).

tff(c_4269,plain,(
    ! [B_81] : k4_xboole_0(k1_xboole_0,B_81) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1343,c_4238])).

tff(c_139,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k4_xboole_0(A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_127])).

tff(c_4293,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4269,c_139])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_233,plain,(
    ! [A_34,B_35,C_36] : k4_xboole_0(k4_xboole_0(A_34,B_35),C_36) = k4_xboole_0(A_34,k2_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_535,plain,(
    ! [A_69,C_70] : k4_xboole_0(k4_xboole_0(k1_xboole_0,A_69),C_70) = k4_xboole_0(A_69,k2_xboole_0(A_69,C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_233])).

tff(c_1503,plain,(
    ! [A_87,B_88] : k4_xboole_0(k4_xboole_0(k1_xboole_0,A_87),B_88) = k4_xboole_0(A_87,k2_xboole_0(B_88,A_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_535])).

tff(c_1727,plain,(
    ! [A_17,B_88] : k4_xboole_0(k4_xboole_0(A_17,A_17),B_88) = k4_xboole_0(A_17,k2_xboole_0(B_88,A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_1503])).

tff(c_4410,plain,(
    ! [A_17,B_88] : k4_xboole_0(A_17,k2_xboole_0(B_88,A_17)) = k4_xboole_0(k1_xboole_0,B_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4293,c_1727])).

tff(c_4415,plain,(
    ! [A_17,B_88] : k4_xboole_0(A_17,k2_xboole_0(B_88,A_17)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4269,c_4410])).

tff(c_28,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_29,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_4645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4415,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:49:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/1.99  
% 5.18/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/2.00  %$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 5.18/2.00  
% 5.18/2.00  %Foreground sorts:
% 5.18/2.00  
% 5.18/2.00  
% 5.18/2.00  %Background operators:
% 5.18/2.00  
% 5.18/2.00  
% 5.18/2.00  %Foreground operators:
% 5.18/2.00  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.18/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.18/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.18/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.18/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.18/2.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.18/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.18/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.18/2.00  
% 5.18/2.01  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.18/2.01  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.18/2.01  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.18/2.01  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.18/2.01  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.18/2.01  tff(f_46, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.18/2.01  tff(c_1015, plain, (![A_74, B_75, C_76]: (r2_hidden('#skF_1'(A_74, B_75, C_76), A_74) | r2_hidden('#skF_2'(A_74, B_75, C_76), C_76) | k4_xboole_0(A_74, B_75)=C_76)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.18/2.01  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.18/2.01  tff(c_1294, plain, (![A_80, B_81]: (r2_hidden('#skF_2'(A_80, B_81, A_80), A_80) | k4_xboole_0(A_80, B_81)=A_80)), inference(resolution, [status(thm)], [c_1015, c_16])).
% 5.18/2.01  tff(c_341, plain, (![D_47, A_48, B_49]: (r2_hidden(D_47, k4_xboole_0(A_48, B_49)) | r2_hidden(D_47, B_49) | ~r2_hidden(D_47, A_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.18/2.01  tff(c_39, plain, (![B_16, A_17]: (k2_xboole_0(B_16, A_17)=k2_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.18/2.01  tff(c_22, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.18/2.01  tff(c_55, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, A_17)=A_17)), inference(superposition, [status(thm), theory('equality')], [c_39, c_22])).
% 5.18/2.01  tff(c_127, plain, (![A_22, B_23]: (k4_xboole_0(k2_xboole_0(A_22, B_23), B_23)=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.18/2.01  tff(c_156, plain, (![A_27]: (k4_xboole_0(k1_xboole_0, A_27)=k4_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_55, c_127])).
% 5.18/2.01  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.18/2.01  tff(c_171, plain, (![D_8, A_27]: (r2_hidden(D_8, A_27) | ~r2_hidden(D_8, k4_xboole_0(k1_xboole_0, A_27)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_8])).
% 5.18/2.01  tff(c_384, plain, (![D_47, B_49]: (r2_hidden(D_47, B_49) | ~r2_hidden(D_47, k1_xboole_0))), inference(resolution, [status(thm)], [c_341, c_171])).
% 5.18/2.01  tff(c_1343, plain, (![B_81, B_49]: (r2_hidden('#skF_2'(k1_xboole_0, B_81, k1_xboole_0), B_49) | k4_xboole_0(k1_xboole_0, B_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1294, c_384])).
% 5.18/2.01  tff(c_3948, plain, (![B_133, B_134]: (r2_hidden('#skF_2'(k1_xboole_0, B_133, k1_xboole_0), B_134) | k4_xboole_0(k1_xboole_0, B_133)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1294, c_384])).
% 5.18/2.01  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.18/2.01  tff(c_4238, plain, (![B_138, B_139]: (~r2_hidden('#skF_2'(k1_xboole_0, B_138, k1_xboole_0), B_139) | k4_xboole_0(k1_xboole_0, B_138)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3948, c_6])).
% 5.18/2.01  tff(c_4269, plain, (![B_81]: (k4_xboole_0(k1_xboole_0, B_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1343, c_4238])).
% 5.18/2.01  tff(c_139, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k4_xboole_0(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_55, c_127])).
% 5.18/2.01  tff(c_4293, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4269, c_139])).
% 5.18/2.01  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.18/2.01  tff(c_233, plain, (![A_34, B_35, C_36]: (k4_xboole_0(k4_xboole_0(A_34, B_35), C_36)=k4_xboole_0(A_34, k2_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.18/2.01  tff(c_535, plain, (![A_69, C_70]: (k4_xboole_0(k4_xboole_0(k1_xboole_0, A_69), C_70)=k4_xboole_0(A_69, k2_xboole_0(A_69, C_70)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_233])).
% 5.18/2.01  tff(c_1503, plain, (![A_87, B_88]: (k4_xboole_0(k4_xboole_0(k1_xboole_0, A_87), B_88)=k4_xboole_0(A_87, k2_xboole_0(B_88, A_87)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_535])).
% 5.18/2.01  tff(c_1727, plain, (![A_17, B_88]: (k4_xboole_0(k4_xboole_0(A_17, A_17), B_88)=k4_xboole_0(A_17, k2_xboole_0(B_88, A_17)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_1503])).
% 5.18/2.01  tff(c_4410, plain, (![A_17, B_88]: (k4_xboole_0(A_17, k2_xboole_0(B_88, A_17))=k4_xboole_0(k1_xboole_0, B_88))), inference(demodulation, [status(thm), theory('equality')], [c_4293, c_1727])).
% 5.18/2.01  tff(c_4415, plain, (![A_17, B_88]: (k4_xboole_0(A_17, k2_xboole_0(B_88, A_17))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4269, c_4410])).
% 5.18/2.01  tff(c_28, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.18/2.01  tff(c_29, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 5.18/2.01  tff(c_4645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4415, c_29])).
% 5.18/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/2.01  
% 5.18/2.01  Inference rules
% 5.18/2.01  ----------------------
% 5.18/2.01  #Ref     : 0
% 5.18/2.01  #Sup     : 1130
% 5.18/2.01  #Fact    : 0
% 5.18/2.01  #Define  : 0
% 5.18/2.01  #Split   : 0
% 5.18/2.01  #Chain   : 0
% 5.18/2.01  #Close   : 0
% 5.18/2.01  
% 5.18/2.01  Ordering : KBO
% 5.18/2.01  
% 5.18/2.01  Simplification rules
% 5.18/2.01  ----------------------
% 5.18/2.01  #Subsume      : 348
% 5.18/2.01  #Demod        : 707
% 5.18/2.01  #Tautology    : 229
% 5.18/2.01  #SimpNegUnit  : 0
% 5.18/2.01  #BackRed      : 20
% 5.18/2.01  
% 5.18/2.01  #Partial instantiations: 0
% 5.18/2.01  #Strategies tried      : 1
% 5.18/2.01  
% 5.18/2.01  Timing (in seconds)
% 5.18/2.01  ----------------------
% 5.18/2.01  Preprocessing        : 0.27
% 5.18/2.01  Parsing              : 0.14
% 5.18/2.01  CNF conversion       : 0.02
% 5.18/2.01  Main loop            : 0.97
% 5.18/2.01  Inferencing          : 0.29
% 5.18/2.01  Reduction            : 0.44
% 5.18/2.01  Demodulation         : 0.37
% 5.18/2.01  BG Simplification    : 0.04
% 5.18/2.01  Subsumption          : 0.16
% 5.18/2.01  Abstraction          : 0.05
% 5.18/2.01  MUC search           : 0.00
% 5.18/2.01  Cooper               : 0.00
% 5.18/2.01  Total                : 1.27
% 5.18/2.01  Index Insertion      : 0.00
% 5.18/2.01  Index Deletion       : 0.00
% 5.18/2.01  Index Matching       : 0.00
% 5.18/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
