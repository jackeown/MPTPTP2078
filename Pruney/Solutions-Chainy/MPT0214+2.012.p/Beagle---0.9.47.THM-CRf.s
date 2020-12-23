%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:31 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 105 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 165 expanded)
%              Number of equality atoms :   35 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_82,plain,(
    r1_tarski(k1_tarski('#skF_8'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_259,plain,(
    ! [B_79,A_80] :
      ( k1_tarski(B_79) = A_80
      | k1_xboole_0 = A_80
      | ~ r1_tarski(A_80,k1_tarski(B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_270,plain,
    ( k1_tarski('#skF_9') = k1_tarski('#skF_8')
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_259])).

tff(c_275,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_58,plain,(
    ! [C_26] : r2_hidden(C_26,k1_tarski(C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_300,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_58])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_112,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,(
    ! [B_10] : k3_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_26,c_112])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_159,plain,(
    ! [D_57,A_58,B_59] :
      ( r2_hidden(D_57,A_58)
      | ~ r2_hidden(D_57,k4_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_164,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_58,B_59)),A_58)
      | k4_xboole_0(A_58,B_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_159])).

tff(c_194,plain,(
    ! [D_65,B_66,A_67] :
      ( ~ r2_hidden(D_65,B_66)
      | ~ r2_hidden(D_65,k4_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_844,plain,(
    ! [A_1360,B_1361] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_1360,B_1361)),B_1361)
      | k4_xboole_0(A_1360,B_1361) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_194])).

tff(c_859,plain,(
    ! [A_1395] : k4_xboole_0(A_1395,A_1395) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_164,c_844])).

tff(c_200,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_209,plain,(
    ! [D_6,A_68,B_69] :
      ( ~ r2_hidden(D_6,k4_xboole_0(A_68,B_69))
      | ~ r2_hidden(D_6,k3_xboole_0(A_68,B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_4])).

tff(c_874,plain,(
    ! [D_6,A_1395] :
      ( ~ r2_hidden(D_6,k1_xboole_0)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1395,A_1395)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_859,c_209])).

tff(c_994,plain,(
    ! [D_1533,A_1534] :
      ( ~ r2_hidden(D_1533,k1_xboole_0)
      | ~ r2_hidden(D_1533,A_1534) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_874])).

tff(c_1004,plain,(
    ! [A_1534] : ~ r2_hidden('#skF_8',A_1534) ),
    inference(resolution,[status(thm)],[c_300,c_994])).

tff(c_1008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1004,c_300])).

tff(c_1010,plain,(
    k1_tarski('#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_80,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1009,plain,(
    k1_tarski('#skF_9') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_101,plain,(
    ! [C_49,A_50] :
      ( C_49 = A_50
      | ~ r2_hidden(C_49,k1_tarski(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_109,plain,(
    ! [A_50] :
      ( '#skF_3'(k1_tarski(A_50)) = A_50
      | k1_tarski(A_50) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_101])).

tff(c_1025,plain,
    ( '#skF_3'(k1_tarski('#skF_8')) = '#skF_9'
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_109])).

tff(c_1041,plain,
    ( '#skF_3'(k1_tarski('#skF_8')) = '#skF_9'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_1025])).

tff(c_1042,plain,(
    '#skF_3'(k1_tarski('#skF_8')) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_1010,c_1041])).

tff(c_1049,plain,
    ( '#skF_9' = '#skF_8'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_109])).

tff(c_1059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1010,c_80,c_1049])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.43  
% 2.84/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.43  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_7
% 2.84/1.43  
% 2.84/1.43  %Foreground sorts:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Background operators:
% 2.84/1.43  
% 2.84/1.43  
% 2.84/1.43  %Foreground operators:
% 2.84/1.43  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.84/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.84/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.84/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.84/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.43  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.84/1.43  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.84/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.43  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.84/1.43  
% 2.84/1.45  tff(f_94, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.84/1.45  tff(f_89, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.84/1.45  tff(f_77, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.84/1.45  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.84/1.45  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.84/1.45  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.84/1.45  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.84/1.45  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.84/1.45  tff(c_82, plain, (r1_tarski(k1_tarski('#skF_8'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.84/1.45  tff(c_259, plain, (![B_79, A_80]: (k1_tarski(B_79)=A_80 | k1_xboole_0=A_80 | ~r1_tarski(A_80, k1_tarski(B_79)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.84/1.45  tff(c_270, plain, (k1_tarski('#skF_9')=k1_tarski('#skF_8') | k1_tarski('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_82, c_259])).
% 2.84/1.45  tff(c_275, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_270])).
% 2.84/1.45  tff(c_58, plain, (![C_26]: (r2_hidden(C_26, k1_tarski(C_26)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.45  tff(c_300, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_275, c_58])).
% 2.84/1.45  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.84/1.45  tff(c_112, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.84/1.45  tff(c_124, plain, (![B_10]: (k3_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_26, c_112])).
% 2.84/1.45  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.45  tff(c_159, plain, (![D_57, A_58, B_59]: (r2_hidden(D_57, A_58) | ~r2_hidden(D_57, k4_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.45  tff(c_164, plain, (![A_58, B_59]: (r2_hidden('#skF_3'(k4_xboole_0(A_58, B_59)), A_58) | k4_xboole_0(A_58, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_159])).
% 2.84/1.45  tff(c_194, plain, (![D_65, B_66, A_67]: (~r2_hidden(D_65, B_66) | ~r2_hidden(D_65, k4_xboole_0(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.45  tff(c_844, plain, (![A_1360, B_1361]: (~r2_hidden('#skF_3'(k4_xboole_0(A_1360, B_1361)), B_1361) | k4_xboole_0(A_1360, B_1361)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_194])).
% 2.84/1.45  tff(c_859, plain, (![A_1395]: (k4_xboole_0(A_1395, A_1395)=k1_xboole_0)), inference(resolution, [status(thm)], [c_164, c_844])).
% 2.84/1.45  tff(c_200, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.84/1.45  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.45  tff(c_209, plain, (![D_6, A_68, B_69]: (~r2_hidden(D_6, k4_xboole_0(A_68, B_69)) | ~r2_hidden(D_6, k3_xboole_0(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_200, c_4])).
% 2.84/1.45  tff(c_874, plain, (![D_6, A_1395]: (~r2_hidden(D_6, k1_xboole_0) | ~r2_hidden(D_6, k3_xboole_0(A_1395, A_1395)))), inference(superposition, [status(thm), theory('equality')], [c_859, c_209])).
% 2.84/1.45  tff(c_994, plain, (![D_1533, A_1534]: (~r2_hidden(D_1533, k1_xboole_0) | ~r2_hidden(D_1533, A_1534))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_874])).
% 2.84/1.45  tff(c_1004, plain, (![A_1534]: (~r2_hidden('#skF_8', A_1534))), inference(resolution, [status(thm)], [c_300, c_994])).
% 2.84/1.45  tff(c_1008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1004, c_300])).
% 2.84/1.45  tff(c_1010, plain, (k1_tarski('#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_270])).
% 2.84/1.45  tff(c_80, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.84/1.45  tff(c_1009, plain, (k1_tarski('#skF_9')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_270])).
% 2.84/1.45  tff(c_101, plain, (![C_49, A_50]: (C_49=A_50 | ~r2_hidden(C_49, k1_tarski(A_50)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.45  tff(c_109, plain, (![A_50]: ('#skF_3'(k1_tarski(A_50))=A_50 | k1_tarski(A_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_101])).
% 2.84/1.45  tff(c_1025, plain, ('#skF_3'(k1_tarski('#skF_8'))='#skF_9' | k1_tarski('#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1009, c_109])).
% 2.84/1.45  tff(c_1041, plain, ('#skF_3'(k1_tarski('#skF_8'))='#skF_9' | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_1025])).
% 2.84/1.45  tff(c_1042, plain, ('#skF_3'(k1_tarski('#skF_8'))='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_1010, c_1041])).
% 2.84/1.45  tff(c_1049, plain, ('#skF_9'='#skF_8' | k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1042, c_109])).
% 2.84/1.45  tff(c_1059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1010, c_80, c_1049])).
% 2.84/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.45  
% 2.84/1.45  Inference rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Ref     : 0
% 2.84/1.45  #Sup     : 159
% 2.84/1.45  #Fact    : 0
% 2.84/1.45  #Define  : 0
% 2.84/1.45  #Split   : 3
% 2.84/1.45  #Chain   : 0
% 2.84/1.45  #Close   : 0
% 2.84/1.45  
% 2.84/1.45  Ordering : KBO
% 2.84/1.45  
% 2.84/1.45  Simplification rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Subsume      : 3
% 2.84/1.45  #Demod        : 48
% 2.84/1.45  #Tautology    : 84
% 2.84/1.45  #SimpNegUnit  : 4
% 2.84/1.45  #BackRed      : 5
% 2.84/1.45  
% 2.84/1.45  #Partial instantiations: 688
% 2.84/1.45  #Strategies tried      : 1
% 2.84/1.45  
% 2.84/1.45  Timing (in seconds)
% 2.84/1.45  ----------------------
% 2.84/1.45  Preprocessing        : 0.33
% 2.84/1.45  Parsing              : 0.16
% 2.84/1.45  CNF conversion       : 0.03
% 2.84/1.45  Main loop            : 0.35
% 2.84/1.45  Inferencing          : 0.16
% 2.84/1.45  Reduction            : 0.09
% 2.84/1.45  Demodulation         : 0.07
% 2.84/1.45  BG Simplification    : 0.02
% 2.84/1.45  Subsumption          : 0.05
% 2.84/1.45  Abstraction          : 0.02
% 2.84/1.45  MUC search           : 0.00
% 2.84/1.45  Cooper               : 0.00
% 2.84/1.45  Total                : 0.71
% 2.84/1.45  Index Insertion      : 0.00
% 2.84/1.45  Index Deletion       : 0.00
% 2.84/1.45  Index Matching       : 0.00
% 2.84/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
