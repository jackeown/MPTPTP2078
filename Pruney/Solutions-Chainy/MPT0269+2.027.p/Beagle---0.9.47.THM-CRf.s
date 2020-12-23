%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:47 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   52 (  65 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 (  99 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_233,plain,(
    ! [A_70,B_71,C_72] :
      ( r1_tarski(k2_tarski(A_70,B_71),C_72)
      | ~ r2_hidden(B_71,C_72)
      | ~ r2_hidden(A_70,C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_754,plain,(
    ! [A_981,C_982] :
      ( r1_tarski(k1_tarski(A_981),C_982)
      | ~ r2_hidden(A_981,C_982)
      | ~ r2_hidden(A_981,C_982) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_233])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_812,plain,(
    ! [A_981,C_982] :
      ( k4_xboole_0(k1_tarski(A_981),C_982) = k1_xboole_0
      | ~ r2_hidden(A_981,C_982) ) ),
    inference(resolution,[status(thm)],[c_754,c_18])).

tff(c_46,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_252,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | k4_xboole_0(A_74,B_73) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_965,plain,(
    ! [B_1079,A_1080] :
      ( B_1079 = A_1080
      | k4_xboole_0(B_1079,A_1080) != k1_xboole_0
      | k4_xboole_0(A_1080,B_1079) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_252])).

tff(c_974,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_965])).

tff(c_983,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_974])).

tff(c_996,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_812,c_983])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_217,plain,(
    ! [C_67,B_68,A_69] :
      ( r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_674,plain,(
    ! [A_882,B_883] :
      ( r2_hidden('#skF_2'(A_882),B_883)
      | ~ r1_tarski(A_882,B_883)
      | k1_xboole_0 = A_882 ) ),
    inference(resolution,[status(thm)],[c_8,c_217])).

tff(c_22,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_687,plain,(
    ! [A_907,A_908] :
      ( A_907 = '#skF_2'(A_908)
      | ~ r1_tarski(A_908,k1_tarski(A_907))
      | k1_xboole_0 = A_908 ) ),
    inference(resolution,[status(thm)],[c_674,c_22])).

tff(c_1122,plain,(
    ! [A_1223,A_1224] :
      ( A_1223 = '#skF_2'(A_1224)
      | k1_xboole_0 = A_1224
      | k4_xboole_0(A_1224,k1_tarski(A_1223)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_687])).

tff(c_1142,plain,
    ( '#skF_2'('#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1122])).

tff(c_1148,plain,(
    '#skF_2'('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1142])).

tff(c_1155,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1148,c_8])).

tff(c_1160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_996,c_1155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:50:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.34  
% 2.68/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.34  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 2.68/1.34  
% 2.68/1.34  %Foreground sorts:
% 2.68/1.34  
% 2.68/1.34  
% 2.68/1.34  %Background operators:
% 2.68/1.34  
% 2.68/1.34  
% 2.68/1.34  %Foreground operators:
% 2.68/1.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.68/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.68/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.68/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.68/1.34  
% 2.68/1.35  tff(f_81, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 2.68/1.35  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.68/1.35  tff(f_71, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.68/1.35  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.68/1.35  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.68/1.35  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.68/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.68/1.35  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.68/1.35  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.68/1.35  tff(c_34, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.35  tff(c_233, plain, (![A_70, B_71, C_72]: (r1_tarski(k2_tarski(A_70, B_71), C_72) | ~r2_hidden(B_71, C_72) | ~r2_hidden(A_70, C_72))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.68/1.35  tff(c_754, plain, (![A_981, C_982]: (r1_tarski(k1_tarski(A_981), C_982) | ~r2_hidden(A_981, C_982) | ~r2_hidden(A_981, C_982))), inference(superposition, [status(thm), theory('equality')], [c_34, c_233])).
% 2.68/1.35  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.68/1.35  tff(c_812, plain, (![A_981, C_982]: (k4_xboole_0(k1_tarski(A_981), C_982)=k1_xboole_0 | ~r2_hidden(A_981, C_982))), inference(resolution, [status(thm)], [c_754, c_18])).
% 2.68/1.35  tff(c_46, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.68/1.35  tff(c_50, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.68/1.35  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.68/1.35  tff(c_142, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.35  tff(c_252, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | k4_xboole_0(A_74, B_73)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_142])).
% 2.68/1.35  tff(c_965, plain, (![B_1079, A_1080]: (B_1079=A_1080 | k4_xboole_0(B_1079, A_1080)!=k1_xboole_0 | k4_xboole_0(A_1080, B_1079)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_252])).
% 2.68/1.35  tff(c_974, plain, (k1_tarski('#skF_6')='#skF_5' | k4_xboole_0(k1_tarski('#skF_6'), '#skF_5')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_50, c_965])).
% 2.68/1.35  tff(c_983, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_46, c_974])).
% 2.68/1.35  tff(c_996, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_812, c_983])).
% 2.68/1.35  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.68/1.35  tff(c_217, plain, (![C_67, B_68, A_69]: (r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.35  tff(c_674, plain, (![A_882, B_883]: (r2_hidden('#skF_2'(A_882), B_883) | ~r1_tarski(A_882, B_883) | k1_xboole_0=A_882)), inference(resolution, [status(thm)], [c_8, c_217])).
% 2.68/1.35  tff(c_22, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.68/1.35  tff(c_687, plain, (![A_907, A_908]: (A_907='#skF_2'(A_908) | ~r1_tarski(A_908, k1_tarski(A_907)) | k1_xboole_0=A_908)), inference(resolution, [status(thm)], [c_674, c_22])).
% 2.68/1.35  tff(c_1122, plain, (![A_1223, A_1224]: (A_1223='#skF_2'(A_1224) | k1_xboole_0=A_1224 | k4_xboole_0(A_1224, k1_tarski(A_1223))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_687])).
% 2.68/1.35  tff(c_1142, plain, ('#skF_2'('#skF_5')='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_50, c_1122])).
% 2.68/1.35  tff(c_1148, plain, ('#skF_2'('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_48, c_1142])).
% 2.68/1.35  tff(c_1155, plain, (r2_hidden('#skF_6', '#skF_5') | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1148, c_8])).
% 2.68/1.35  tff(c_1160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_996, c_1155])).
% 2.68/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.35  
% 2.68/1.35  Inference rules
% 2.68/1.35  ----------------------
% 2.68/1.35  #Ref     : 0
% 2.68/1.35  #Sup     : 159
% 2.68/1.35  #Fact    : 0
% 2.68/1.35  #Define  : 0
% 2.68/1.35  #Split   : 1
% 2.68/1.35  #Chain   : 0
% 2.68/1.35  #Close   : 0
% 2.68/1.35  
% 2.68/1.35  Ordering : KBO
% 2.68/1.35  
% 2.68/1.35  Simplification rules
% 2.68/1.35  ----------------------
% 2.68/1.35  #Subsume      : 13
% 2.68/1.35  #Demod        : 18
% 2.68/1.35  #Tautology    : 60
% 2.68/1.35  #SimpNegUnit  : 6
% 2.68/1.35  #BackRed      : 0
% 2.68/1.35  
% 2.68/1.35  #Partial instantiations: 686
% 2.68/1.35  #Strategies tried      : 1
% 2.68/1.35  
% 2.68/1.35  Timing (in seconds)
% 2.68/1.35  ----------------------
% 2.68/1.36  Preprocessing        : 0.29
% 2.68/1.36  Parsing              : 0.15
% 2.68/1.36  CNF conversion       : 0.02
% 2.68/1.36  Main loop            : 0.34
% 2.68/1.36  Inferencing          : 0.17
% 2.68/1.36  Reduction            : 0.08
% 2.68/1.36  Demodulation         : 0.06
% 2.68/1.36  BG Simplification    : 0.02
% 2.68/1.36  Subsumption          : 0.06
% 2.68/1.36  Abstraction          : 0.02
% 2.68/1.36  MUC search           : 0.00
% 2.68/1.36  Cooper               : 0.00
% 2.68/1.36  Total                : 0.65
% 2.68/1.36  Index Insertion      : 0.00
% 2.68/1.36  Index Deletion       : 0.00
% 2.68/1.36  Index Matching       : 0.00
% 2.68/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
