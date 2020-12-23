%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:36 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 240 expanded)
%              Number of leaves         :   18 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 ( 564 expanded)
%              Number of equality atoms :   24 ( 197 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ! [D] :
          ( ~ r2_hidden(D,A)
        <=> ( r2_hidden(D,B)
          <=> r2_hidden(D,C) ) )
     => A = k5_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_0)).

tff(c_142,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden('#skF_1'(A_36,B_37,C_38),A_36)
      | r2_hidden('#skF_2'(A_36,B_37,C_38),C_38)
      | k4_xboole_0(A_36,B_37) = C_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_170,plain,(
    ! [A_36,C_38] :
      ( r2_hidden('#skF_2'(A_36,A_36,C_38),C_38)
      | k4_xboole_0(A_36,A_36) = C_38 ) ),
    inference(resolution,[status(thm)],[c_142,c_16])).

tff(c_177,plain,(
    ! [A_39,C_40] :
      ( r2_hidden('#skF_2'(A_39,A_39,C_40),C_40)
      | k4_xboole_0(A_39,A_39) = C_40 ) ),
    inference(resolution,[status(thm)],[c_142,c_16])).

tff(c_52,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [D_18,B_19,A_20] :
      ( ~ r2_hidden(D_18,B_19)
      | ~ r2_hidden(D_18,k4_xboole_0(A_20,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [D_18,A_13] :
      ( ~ r2_hidden(D_18,k1_xboole_0)
      | ~ r2_hidden(D_18,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_68])).

tff(c_213,plain,(
    ! [A_46,A_47] :
      ( ~ r2_hidden('#skF_2'(A_46,A_46,k1_xboole_0),A_47)
      | k4_xboole_0(A_46,A_46) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_177,c_71])).

tff(c_230,plain,(
    ! [A_36] : k4_xboole_0(A_36,A_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_213])).

tff(c_234,plain,(
    ! [A_48] : k4_xboole_0(A_48,A_48) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_213])).

tff(c_20,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),k4_xboole_0(B_8,A_7)) = k5_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_250,plain,(
    ! [A_48] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_48,A_48)) = k5_xboole_0(A_48,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_20])).

tff(c_273,plain,(
    ! [A_48] : k5_xboole_0(A_48,A_48) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_250])).

tff(c_54,plain,(
    k5_xboole_0('#skF_5','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_279,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_54])).

tff(c_944,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden('#skF_3'(A_103,B_104,C_105),A_103)
      | r2_hidden('#skF_4'(A_103,B_104,C_105),B_104)
      | r2_hidden('#skF_4'(A_103,B_104,C_105),C_105)
      | k5_xboole_0(B_104,C_105) = A_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_3'(A_9,B_10,C_11),A_9)
      | ~ r2_hidden('#skF_4'(A_9,B_10,C_11),A_9)
      | k5_xboole_0(B_10,C_11) = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1073,plain,(
    ! [B_110,C_111] :
      ( r2_hidden('#skF_3'(B_110,B_110,C_111),B_110)
      | r2_hidden('#skF_4'(B_110,B_110,C_111),C_111)
      | k5_xboole_0(B_110,C_111) = B_110 ) ),
    inference(resolution,[status(thm)],[c_944,c_46])).

tff(c_1095,plain,(
    ! [C_111] :
      ( r2_hidden('#skF_3'(C_111,C_111,C_111),C_111)
      | k5_xboole_0(C_111,C_111) = C_111 ) ),
    inference(resolution,[status(thm)],[c_1073,c_46])).

tff(c_1119,plain,(
    ! [C_112] :
      ( r2_hidden('#skF_3'(C_112,C_112,C_112),C_112)
      | k2_xboole_0(k1_xboole_0,k1_xboole_0) = C_112 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_1095])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_259,plain,(
    ! [D_6,A_48] :
      ( r2_hidden(D_6,A_48)
      | ~ r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_6])).

tff(c_1126,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_3'(k1_xboole_0,k1_xboole_0,k1_xboole_0),A_48)
      | k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1119,c_259])).

tff(c_1144,plain,(
    ! [A_48] : r2_hidden('#skF_3'(k1_xboole_0,k1_xboole_0,k1_xboole_0),A_48) ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_1126])).

tff(c_1150,plain,(
    ! [A_113] : r2_hidden('#skF_3'(k1_xboole_0,k1_xboole_0,k1_xboole_0),A_113) ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_1126])).

tff(c_1162,plain,(
    ! [A_13] : ~ r2_hidden('#skF_3'(k1_xboole_0,k1_xboole_0,k1_xboole_0),A_13) ),
    inference(resolution,[status(thm)],[c_1150,c_71])).

tff(c_1182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_1162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:23:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.81  
% 2.78/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.81  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3
% 2.78/1.81  
% 2.78/1.81  %Foreground sorts:
% 2.78/1.81  
% 2.78/1.81  
% 2.78/1.81  %Background operators:
% 2.78/1.81  
% 2.78/1.81  
% 2.78/1.81  %Foreground operators:
% 2.78/1.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.78/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.81  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.78/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.81  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.78/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.78/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.81  
% 2.95/1.82  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.95/1.82  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.95/1.82  tff(f_37, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.95/1.82  tff(f_52, negated_conjecture, ~(![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.95/1.82  tff(f_47, axiom, (![A, B, C]: ((![D]: (~r2_hidden(D, A) <=> (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (A = k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_0)).
% 2.95/1.82  tff(c_142, plain, (![A_36, B_37, C_38]: (r2_hidden('#skF_1'(A_36, B_37, C_38), A_36) | r2_hidden('#skF_2'(A_36, B_37, C_38), C_38) | k4_xboole_0(A_36, B_37)=C_38)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.82  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.82  tff(c_170, plain, (![A_36, C_38]: (r2_hidden('#skF_2'(A_36, A_36, C_38), C_38) | k4_xboole_0(A_36, A_36)=C_38)), inference(resolution, [status(thm)], [c_142, c_16])).
% 2.95/1.82  tff(c_177, plain, (![A_39, C_40]: (r2_hidden('#skF_2'(A_39, A_39, C_40), C_40) | k4_xboole_0(A_39, A_39)=C_40)), inference(resolution, [status(thm)], [c_142, c_16])).
% 2.95/1.82  tff(c_52, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.95/1.82  tff(c_68, plain, (![D_18, B_19, A_20]: (~r2_hidden(D_18, B_19) | ~r2_hidden(D_18, k4_xboole_0(A_20, B_19)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.82  tff(c_71, plain, (![D_18, A_13]: (~r2_hidden(D_18, k1_xboole_0) | ~r2_hidden(D_18, A_13))), inference(superposition, [status(thm), theory('equality')], [c_52, c_68])).
% 2.95/1.82  tff(c_213, plain, (![A_46, A_47]: (~r2_hidden('#skF_2'(A_46, A_46, k1_xboole_0), A_47) | k4_xboole_0(A_46, A_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_177, c_71])).
% 2.95/1.82  tff(c_230, plain, (![A_36]: (k4_xboole_0(A_36, A_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_170, c_213])).
% 2.95/1.82  tff(c_234, plain, (![A_48]: (k4_xboole_0(A_48, A_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_170, c_213])).
% 2.95/1.82  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), k4_xboole_0(B_8, A_7))=k5_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.95/1.82  tff(c_250, plain, (![A_48]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_48, A_48))=k5_xboole_0(A_48, A_48))), inference(superposition, [status(thm), theory('equality')], [c_234, c_20])).
% 2.95/1.82  tff(c_273, plain, (![A_48]: (k5_xboole_0(A_48, A_48)=k2_xboole_0(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_250])).
% 2.95/1.82  tff(c_54, plain, (k5_xboole_0('#skF_5', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.95/1.82  tff(c_279, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_273, c_54])).
% 2.95/1.82  tff(c_944, plain, (![A_103, B_104, C_105]: (r2_hidden('#skF_3'(A_103, B_104, C_105), A_103) | r2_hidden('#skF_4'(A_103, B_104, C_105), B_104) | r2_hidden('#skF_4'(A_103, B_104, C_105), C_105) | k5_xboole_0(B_104, C_105)=A_103)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.95/1.82  tff(c_46, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_3'(A_9, B_10, C_11), A_9) | ~r2_hidden('#skF_4'(A_9, B_10, C_11), A_9) | k5_xboole_0(B_10, C_11)=A_9)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.95/1.82  tff(c_1073, plain, (![B_110, C_111]: (r2_hidden('#skF_3'(B_110, B_110, C_111), B_110) | r2_hidden('#skF_4'(B_110, B_110, C_111), C_111) | k5_xboole_0(B_110, C_111)=B_110)), inference(resolution, [status(thm)], [c_944, c_46])).
% 2.95/1.82  tff(c_1095, plain, (![C_111]: (r2_hidden('#skF_3'(C_111, C_111, C_111), C_111) | k5_xboole_0(C_111, C_111)=C_111)), inference(resolution, [status(thm)], [c_1073, c_46])).
% 2.95/1.82  tff(c_1119, plain, (![C_112]: (r2_hidden('#skF_3'(C_112, C_112, C_112), C_112) | k2_xboole_0(k1_xboole_0, k1_xboole_0)=C_112)), inference(demodulation, [status(thm), theory('equality')], [c_273, c_1095])).
% 2.95/1.82  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.82  tff(c_259, plain, (![D_6, A_48]: (r2_hidden(D_6, A_48) | ~r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_234, c_6])).
% 2.95/1.82  tff(c_1126, plain, (![A_48]: (r2_hidden('#skF_3'(k1_xboole_0, k1_xboole_0, k1_xboole_0), A_48) | k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1119, c_259])).
% 2.95/1.82  tff(c_1144, plain, (![A_48]: (r2_hidden('#skF_3'(k1_xboole_0, k1_xboole_0, k1_xboole_0), A_48))), inference(negUnitSimplification, [status(thm)], [c_279, c_1126])).
% 2.95/1.82  tff(c_1150, plain, (![A_113]: (r2_hidden('#skF_3'(k1_xboole_0, k1_xboole_0, k1_xboole_0), A_113))), inference(negUnitSimplification, [status(thm)], [c_279, c_1126])).
% 2.95/1.82  tff(c_1162, plain, (![A_13]: (~r2_hidden('#skF_3'(k1_xboole_0, k1_xboole_0, k1_xboole_0), A_13))), inference(resolution, [status(thm)], [c_1150, c_71])).
% 2.95/1.82  tff(c_1182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1144, c_1162])).
% 2.95/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.82  
% 2.95/1.82  Inference rules
% 2.95/1.82  ----------------------
% 2.95/1.82  #Ref     : 0
% 2.95/1.82  #Sup     : 226
% 2.95/1.82  #Fact    : 2
% 2.95/1.82  #Define  : 0
% 2.95/1.82  #Split   : 0
% 2.95/1.82  #Chain   : 0
% 2.95/1.82  #Close   : 0
% 2.95/1.82  
% 2.95/1.82  Ordering : KBO
% 2.95/1.82  
% 2.95/1.82  Simplification rules
% 2.95/1.82  ----------------------
% 2.95/1.82  #Subsume      : 28
% 2.95/1.82  #Demod        : 143
% 2.95/1.82  #Tautology    : 131
% 2.95/1.82  #SimpNegUnit  : 4
% 2.95/1.82  #BackRed      : 4
% 2.95/1.82  
% 2.95/1.82  #Partial instantiations: 0
% 2.95/1.82  #Strategies tried      : 1
% 2.95/1.82  
% 2.95/1.82  Timing (in seconds)
% 2.95/1.82  ----------------------
% 2.95/1.82  Preprocessing        : 0.43
% 2.95/1.82  Parsing              : 0.26
% 2.95/1.82  CNF conversion       : 0.03
% 2.95/1.82  Main loop            : 0.36
% 2.95/1.82  Inferencing          : 0.15
% 2.95/1.82  Reduction            : 0.09
% 2.95/1.82  Demodulation         : 0.07
% 2.95/1.82  BG Simplification    : 0.02
% 2.95/1.82  Subsumption          : 0.07
% 2.95/1.82  Abstraction          : 0.02
% 2.95/1.82  MUC search           : 0.00
% 2.95/1.82  Cooper               : 0.00
% 2.95/1.82  Total                : 0.82
% 2.95/1.82  Index Insertion      : 0.00
% 2.95/1.82  Index Deletion       : 0.00
% 2.95/1.82  Index Matching       : 0.00
% 2.95/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
