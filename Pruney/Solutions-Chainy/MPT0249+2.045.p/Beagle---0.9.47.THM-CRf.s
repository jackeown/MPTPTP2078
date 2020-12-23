%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:29 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 115 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :   71 ( 201 expanded)
%              Number of equality atoms :   39 ( 142 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_62,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_81,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_81])).

tff(c_360,plain,(
    ! [B_70,A_71] :
      ( k1_tarski(B_70) = A_71
      | k1_xboole_0 = A_71
      | ~ r1_tarski(A_71,k1_tarski(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_371,plain,
    ( k1_tarski('#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_84,c_360])).

tff(c_382,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_371])).

tff(c_34,plain,(
    ! [C_22] : r2_hidden(C_22,k1_tarski(C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_411,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_34])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [D_51,B_52,A_53] :
      ( ~ r2_hidden(D_51,B_52)
      | r2_hidden(D_51,k2_xboole_0(A_53,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_248,plain,(
    ! [D_57] :
      ( ~ r2_hidden(D_57,'#skF_9')
      | r2_hidden(D_57,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_185])).

tff(c_32,plain,(
    ! [C_22,A_18] :
      ( C_22 = A_18
      | ~ r2_hidden(C_22,k1_tarski(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_259,plain,(
    ! [D_60] :
      ( D_60 = '#skF_7'
      | ~ r2_hidden(D_60,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_248,c_32])).

tff(c_268,plain,(
    ! [B_2] :
      ( '#skF_1'('#skF_9',B_2) = '#skF_7'
      | r1_tarski('#skF_9',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_259])).

tff(c_368,plain,(
    ! [B_70] :
      ( k1_tarski(B_70) = '#skF_9'
      | k1_xboole_0 = '#skF_9'
      | '#skF_1'('#skF_9',k1_tarski(B_70)) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_268,c_360])).

tff(c_671,plain,(
    ! [B_90] :
      ( k1_tarski(B_90) = '#skF_9'
      | '#skF_1'('#skF_9',k1_tarski(B_90)) = '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_368])).

tff(c_686,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | '#skF_1'('#skF_9','#skF_8') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_671])).

tff(c_690,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_1'('#skF_9','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_686])).

tff(c_691,plain,(
    '#skF_1'('#skF_9','#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_690])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_695,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r1_tarski('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_691,c_4])).

tff(c_702,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_695])).

tff(c_50,plain,(
    ! [B_30,A_29] :
      ( k1_tarski(B_30) = A_29
      | k1_xboole_0 = A_29
      | ~ r1_tarski(A_29,k1_tarski(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_394,plain,(
    ! [A_29] :
      ( k1_tarski('#skF_7') = A_29
      | k1_xboole_0 = A_29
      | ~ r1_tarski(A_29,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_50])).

tff(c_797,plain,(
    ! [A_98] :
      ( A_98 = '#skF_8'
      | k1_xboole_0 = A_98
      | ~ r1_tarski(A_98,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_394])).

tff(c_800,plain,
    ( '#skF_9' = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_702,c_797])).

tff(c_815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_62,c_800])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:57:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.48  
% 3.06/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.48  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 3.06/1.48  
% 3.06/1.48  %Foreground sorts:
% 3.06/1.48  
% 3.06/1.48  
% 3.06/1.48  %Background operators:
% 3.06/1.48  
% 3.06/1.48  
% 3.06/1.48  %Foreground operators:
% 3.06/1.48  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.06/1.48  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.06/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.06/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.06/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.06/1.48  tff('#skF_9', type, '#skF_9': $i).
% 3.06/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.06/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.06/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.48  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.06/1.48  
% 3.06/1.49  tff(f_89, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.06/1.49  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.06/1.49  tff(f_74, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.06/1.49  tff(f_62, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.06/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.06/1.49  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.06/1.49  tff(c_58, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.06/1.49  tff(c_62, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.06/1.49  tff(c_60, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.06/1.49  tff(c_64, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.06/1.49  tff(c_81, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.06/1.49  tff(c_84, plain, (r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_81])).
% 3.06/1.49  tff(c_360, plain, (![B_70, A_71]: (k1_tarski(B_70)=A_71 | k1_xboole_0=A_71 | ~r1_tarski(A_71, k1_tarski(B_70)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.06/1.49  tff(c_371, plain, (k1_tarski('#skF_7')='#skF_8' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_84, c_360])).
% 3.06/1.49  tff(c_382, plain, (k1_tarski('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_60, c_371])).
% 3.06/1.49  tff(c_34, plain, (![C_22]: (r2_hidden(C_22, k1_tarski(C_22)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.49  tff(c_411, plain, (r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_382, c_34])).
% 3.06/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.49  tff(c_185, plain, (![D_51, B_52, A_53]: (~r2_hidden(D_51, B_52) | r2_hidden(D_51, k2_xboole_0(A_53, B_52)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.06/1.49  tff(c_248, plain, (![D_57]: (~r2_hidden(D_57, '#skF_9') | r2_hidden(D_57, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_185])).
% 3.06/1.49  tff(c_32, plain, (![C_22, A_18]: (C_22=A_18 | ~r2_hidden(C_22, k1_tarski(A_18)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.49  tff(c_259, plain, (![D_60]: (D_60='#skF_7' | ~r2_hidden(D_60, '#skF_9'))), inference(resolution, [status(thm)], [c_248, c_32])).
% 3.06/1.49  tff(c_268, plain, (![B_2]: ('#skF_1'('#skF_9', B_2)='#skF_7' | r1_tarski('#skF_9', B_2))), inference(resolution, [status(thm)], [c_6, c_259])).
% 3.06/1.49  tff(c_368, plain, (![B_70]: (k1_tarski(B_70)='#skF_9' | k1_xboole_0='#skF_9' | '#skF_1'('#skF_9', k1_tarski(B_70))='#skF_7')), inference(resolution, [status(thm)], [c_268, c_360])).
% 3.06/1.49  tff(c_671, plain, (![B_90]: (k1_tarski(B_90)='#skF_9' | '#skF_1'('#skF_9', k1_tarski(B_90))='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_58, c_368])).
% 3.06/1.49  tff(c_686, plain, (k1_tarski('#skF_7')='#skF_9' | '#skF_1'('#skF_9', '#skF_8')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_382, c_671])).
% 3.06/1.49  tff(c_690, plain, ('#skF_9'='#skF_8' | '#skF_1'('#skF_9', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_382, c_686])).
% 3.06/1.49  tff(c_691, plain, ('#skF_1'('#skF_9', '#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_62, c_690])).
% 3.06/1.49  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.06/1.49  tff(c_695, plain, (~r2_hidden('#skF_7', '#skF_8') | r1_tarski('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_691, c_4])).
% 3.06/1.49  tff(c_702, plain, (r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_695])).
% 3.06/1.49  tff(c_50, plain, (![B_30, A_29]: (k1_tarski(B_30)=A_29 | k1_xboole_0=A_29 | ~r1_tarski(A_29, k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.06/1.49  tff(c_394, plain, (![A_29]: (k1_tarski('#skF_7')=A_29 | k1_xboole_0=A_29 | ~r1_tarski(A_29, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_382, c_50])).
% 3.06/1.49  tff(c_797, plain, (![A_98]: (A_98='#skF_8' | k1_xboole_0=A_98 | ~r1_tarski(A_98, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_394])).
% 3.06/1.49  tff(c_800, plain, ('#skF_9'='#skF_8' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_702, c_797])).
% 3.06/1.49  tff(c_815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_62, c_800])).
% 3.06/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.49  
% 3.06/1.49  Inference rules
% 3.06/1.49  ----------------------
% 3.06/1.49  #Ref     : 0
% 3.06/1.49  #Sup     : 175
% 3.06/1.49  #Fact    : 0
% 3.06/1.50  #Define  : 0
% 3.06/1.50  #Split   : 2
% 3.06/1.50  #Chain   : 0
% 3.06/1.50  #Close   : 0
% 3.06/1.50  
% 3.06/1.50  Ordering : KBO
% 3.06/1.50  
% 3.06/1.50  Simplification rules
% 3.06/1.50  ----------------------
% 3.06/1.50  #Subsume      : 6
% 3.06/1.50  #Demod        : 56
% 3.06/1.50  #Tautology    : 105
% 3.06/1.50  #SimpNegUnit  : 12
% 3.06/1.50  #BackRed      : 6
% 3.06/1.50  
% 3.06/1.50  #Partial instantiations: 0
% 3.06/1.50  #Strategies tried      : 1
% 3.06/1.50  
% 3.06/1.50  Timing (in seconds)
% 3.06/1.50  ----------------------
% 3.06/1.50  Preprocessing        : 0.36
% 3.06/1.50  Parsing              : 0.16
% 3.06/1.50  CNF conversion       : 0.03
% 3.06/1.50  Main loop            : 0.35
% 3.06/1.50  Inferencing          : 0.13
% 3.06/1.50  Reduction            : 0.11
% 3.06/1.50  Demodulation         : 0.08
% 3.06/1.50  BG Simplification    : 0.02
% 3.06/1.50  Subsumption          : 0.07
% 3.06/1.50  Abstraction          : 0.02
% 3.06/1.50  MUC search           : 0.00
% 3.06/1.50  Cooper               : 0.00
% 3.06/1.50  Total                : 0.75
% 3.06/1.50  Index Insertion      : 0.00
% 3.06/1.50  Index Deletion       : 0.00
% 3.06/1.50  Index Matching       : 0.00
% 3.06/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
