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
% DateTime   : Thu Dec  3 09:54:57 EST 2020

% Result     : Theorem 8.54s
% Output     : CNFRefutation 8.60s
% Verified   : 
% Statistics : Number of formulae       :   51 (  76 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   50 (  92 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_32,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_133,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_161,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_133])).

tff(c_34,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_704,plain,(
    ! [A_61,B_62,C_63] : k3_xboole_0(k3_xboole_0(A_61,B_62),C_63) = k3_xboole_0(A_61,k3_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1723,plain,(
    ! [C_85,A_86,B_87] : k3_xboole_0(C_85,k3_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,k3_xboole_0(B_87,C_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_2])).

tff(c_2089,plain,(
    ! [A_88] : k3_xboole_0(A_88,k1_tarski('#skF_4')) = k3_xboole_0('#skF_3',k3_xboole_0(A_88,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1723])).

tff(c_2258,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_2089])).

tff(c_2306,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2258])).

tff(c_56,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [B_31,A_32] : r1_tarski(k3_xboole_0(B_31,A_32),A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_10])).

tff(c_3238,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2306,c_71])).

tff(c_24,plain,(
    ! [B_25,A_24] :
      ( k1_tarski(B_25) = A_24
      | k1_xboole_0 = A_24
      | ~ r1_tarski(A_24,k1_tarski(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3262,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3238,c_24])).

tff(c_3268,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3262])).

tff(c_3271,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3268,c_2306])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_314,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden(A_44,B_45)
      | ~ r1_xboole_0(k1_tarski(A_44),B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_358,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden(A_49,B_50)
      | k3_xboole_0(k1_tarski(A_49),B_50) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_314])).

tff(c_13118,plain,(
    ! [A_174,A_175] :
      ( ~ r2_hidden(A_174,A_175)
      | k3_xboole_0(A_175,k1_tarski(A_174)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_358])).

tff(c_13133,plain,(
    ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3271,c_13118])).

tff(c_13183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_13133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:58:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.54/2.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.00  
% 8.55/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.00  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.55/3.00  
% 8.55/3.00  %Foreground sorts:
% 8.55/3.00  
% 8.55/3.00  
% 8.55/3.00  %Background operators:
% 8.55/3.00  
% 8.55/3.00  
% 8.55/3.00  %Foreground operators:
% 8.55/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.55/3.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.55/3.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.55/3.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.55/3.00  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.55/3.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.55/3.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.55/3.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.55/3.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.55/3.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.55/3.00  tff('#skF_2', type, '#skF_2': $i).
% 8.55/3.00  tff('#skF_3', type, '#skF_3': $i).
% 8.55/3.00  tff('#skF_1', type, '#skF_1': $i).
% 8.55/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.55/3.00  tff('#skF_4', type, '#skF_4': $i).
% 8.55/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.55/3.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.55/3.00  
% 8.60/3.01  tff(f_67, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 8.60/3.01  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.60/3.01  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.60/3.01  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 8.60/3.01  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.60/3.01  tff(f_58, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 8.60/3.01  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.60/3.01  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 8.60/3.01  tff(c_32, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.60/3.01  tff(c_30, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.60/3.01  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.60/3.01  tff(c_36, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.60/3.01  tff(c_133, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.60/3.01  tff(c_161, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_36, c_133])).
% 8.60/3.01  tff(c_34, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.60/3.01  tff(c_704, plain, (![A_61, B_62, C_63]: (k3_xboole_0(k3_xboole_0(A_61, B_62), C_63)=k3_xboole_0(A_61, k3_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.60/3.01  tff(c_1723, plain, (![C_85, A_86, B_87]: (k3_xboole_0(C_85, k3_xboole_0(A_86, B_87))=k3_xboole_0(A_86, k3_xboole_0(B_87, C_85)))), inference(superposition, [status(thm), theory('equality')], [c_704, c_2])).
% 8.60/3.01  tff(c_2089, plain, (![A_88]: (k3_xboole_0(A_88, k1_tarski('#skF_4'))=k3_xboole_0('#skF_3', k3_xboole_0(A_88, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1723])).
% 8.60/3.01  tff(c_2258, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_161, c_2089])).
% 8.60/3.01  tff(c_2306, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2258])).
% 8.60/3.01  tff(c_56, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.60/3.01  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.60/3.01  tff(c_71, plain, (![B_31, A_32]: (r1_tarski(k3_xboole_0(B_31, A_32), A_32))), inference(superposition, [status(thm), theory('equality')], [c_56, c_10])).
% 8.60/3.01  tff(c_3238, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2306, c_71])).
% 8.60/3.01  tff(c_24, plain, (![B_25, A_24]: (k1_tarski(B_25)=A_24 | k1_xboole_0=A_24 | ~r1_tarski(A_24, k1_tarski(B_25)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.60/3.01  tff(c_3262, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3238, c_24])).
% 8.60/3.01  tff(c_3268, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_30, c_3262])).
% 8.60/3.01  tff(c_3271, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3268, c_2306])).
% 8.60/3.01  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.60/3.01  tff(c_314, plain, (![A_44, B_45]: (~r2_hidden(A_44, B_45) | ~r1_xboole_0(k1_tarski(A_44), B_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.60/3.01  tff(c_358, plain, (![A_49, B_50]: (~r2_hidden(A_49, B_50) | k3_xboole_0(k1_tarski(A_49), B_50)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_314])).
% 8.60/3.01  tff(c_13118, plain, (![A_174, A_175]: (~r2_hidden(A_174, A_175) | k3_xboole_0(A_175, k1_tarski(A_174))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_358])).
% 8.60/3.01  tff(c_13133, plain, (~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3271, c_13118])).
% 8.60/3.01  tff(c_13183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_13133])).
% 8.60/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.60/3.01  
% 8.60/3.01  Inference rules
% 8.60/3.01  ----------------------
% 8.60/3.01  #Ref     : 0
% 8.60/3.01  #Sup     : 3195
% 8.60/3.01  #Fact    : 1
% 8.60/3.01  #Define  : 0
% 8.60/3.01  #Split   : 2
% 8.60/3.01  #Chain   : 0
% 8.60/3.01  #Close   : 0
% 8.60/3.01  
% 8.60/3.01  Ordering : KBO
% 8.60/3.01  
% 8.60/3.01  Simplification rules
% 8.60/3.01  ----------------------
% 8.60/3.01  #Subsume      : 84
% 8.60/3.01  #Demod        : 4032
% 8.60/3.01  #Tautology    : 1982
% 8.60/3.01  #SimpNegUnit  : 9
% 8.60/3.01  #BackRed      : 6
% 8.60/3.01  
% 8.60/3.01  #Partial instantiations: 0
% 8.60/3.01  #Strategies tried      : 1
% 8.60/3.01  
% 8.60/3.01  Timing (in seconds)
% 8.60/3.01  ----------------------
% 8.60/3.01  Preprocessing        : 0.29
% 8.60/3.01  Parsing              : 0.16
% 8.60/3.01  CNF conversion       : 0.02
% 8.60/3.01  Main loop            : 1.91
% 8.60/3.01  Inferencing          : 0.39
% 8.60/3.01  Reduction            : 1.13
% 8.60/3.01  Demodulation         : 1.01
% 8.60/3.01  BG Simplification    : 0.05
% 8.60/3.01  Subsumption          : 0.25
% 8.60/3.01  Abstraction          : 0.06
% 8.60/3.01  MUC search           : 0.00
% 8.60/3.01  Cooper               : 0.00
% 8.60/3.01  Total                : 2.23
% 8.60/3.01  Index Insertion      : 0.00
% 8.60/3.01  Index Deletion       : 0.00
% 8.60/3.01  Index Matching       : 0.00
% 8.60/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
