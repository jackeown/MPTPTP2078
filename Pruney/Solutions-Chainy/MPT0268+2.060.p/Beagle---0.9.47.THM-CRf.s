%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:42 EST 2020

% Result     : Theorem 5.87s
% Output     : CNFRefutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 137 expanded)
%              Number of equality atoms :   24 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_44,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_61,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1316,plain,(
    ! [A_1204,B_1205,C_1206] :
      ( ~ r2_hidden('#skF_1'(A_1204,B_1205,C_1206),C_1206)
      | r2_hidden('#skF_2'(A_1204,B_1205,C_1206),C_1206)
      | k4_xboole_0(A_1204,B_1205) = C_1206 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1342,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_1316])).

tff(c_2141,plain,(
    ! [A_1490,B_1491,C_1492] :
      ( r2_hidden('#skF_1'(A_1490,B_1491,C_1492),A_1490)
      | r2_hidden('#skF_2'(A_1490,B_1491,C_1492),B_1491)
      | ~ r2_hidden('#skF_2'(A_1490,B_1491,C_1492),A_1490)
      | k4_xboole_0(A_1490,B_1491) = C_1492 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3384,plain,(
    ! [A_1948,B_1949] :
      ( r2_hidden('#skF_2'(A_1948,B_1949,A_1948),B_1949)
      | ~ r2_hidden('#skF_2'(A_1948,B_1949,A_1948),A_1948)
      | k4_xboole_0(A_1948,B_1949) = A_1948 ) ),
    inference(resolution,[status(thm)],[c_2141,c_8])).

tff(c_3899,plain,(
    ! [A_2122,B_2123] :
      ( r2_hidden('#skF_2'(A_2122,B_2123,A_2122),B_2123)
      | k4_xboole_0(A_2122,B_2123) = A_2122 ) ),
    inference(resolution,[status(thm)],[c_1342,c_3384])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6975,plain,(
    ! [A_2550,A_2551] :
      ( '#skF_2'(A_2550,k1_tarski(A_2551),A_2550) = A_2551
      | k4_xboole_0(A_2550,k1_tarski(A_2551)) = A_2550 ) ),
    inference(resolution,[status(thm)],[c_3899,c_22])).

tff(c_7247,plain,(
    '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6975,c_79])).

tff(c_7262,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_7247,c_1342])).

tff(c_7310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_61,c_7262])).

tff(c_7311,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_24,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_7312,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7368,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7312,c_48])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7379,plain,(
    ! [D_2614] :
      ( ~ r2_hidden(D_2614,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_2614,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7368,c_4])).

tff(c_7383,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_7379])).

tff(c_7387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7311,c_7383])).

tff(c_7388,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_7389,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7416,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7389,c_50])).

tff(c_7421,plain,(
    ! [D_2621,B_2622,A_2623] :
      ( ~ r2_hidden(D_2621,B_2622)
      | ~ r2_hidden(D_2621,k4_xboole_0(A_2623,B_2622)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7425,plain,(
    ! [D_2624] :
      ( ~ r2_hidden(D_2624,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_2624,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7416,c_7421])).

tff(c_7429,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_7425])).

tff(c_7433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7388,c_7429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:51:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.87/2.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.21  
% 5.87/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.21  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 5.87/2.21  
% 5.87/2.21  %Foreground sorts:
% 5.87/2.21  
% 5.87/2.21  
% 5.87/2.21  %Background operators:
% 5.87/2.21  
% 5.87/2.21  
% 5.87/2.21  %Foreground operators:
% 5.87/2.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.87/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.87/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.87/2.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.87/2.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.87/2.21  tff('#skF_7', type, '#skF_7': $i).
% 5.87/2.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.87/2.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.87/2.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.87/2.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.87/2.21  tff('#skF_5', type, '#skF_5': $i).
% 5.87/2.21  tff('#skF_6', type, '#skF_6': $i).
% 5.87/2.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.87/2.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.87/2.21  tff('#skF_8', type, '#skF_8': $i).
% 5.87/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.87/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.87/2.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.87/2.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.87/2.21  
% 5.87/2.22  tff(f_61, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.87/2.22  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.87/2.22  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.87/2.22  tff(c_44, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.87/2.22  tff(c_79, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_44])).
% 5.87/2.22  tff(c_46, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.87/2.22  tff(c_61, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 5.87/2.22  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.87/2.22  tff(c_1316, plain, (![A_1204, B_1205, C_1206]: (~r2_hidden('#skF_1'(A_1204, B_1205, C_1206), C_1206) | r2_hidden('#skF_2'(A_1204, B_1205, C_1206), C_1206) | k4_xboole_0(A_1204, B_1205)=C_1206)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.87/2.22  tff(c_1342, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_1316])).
% 5.87/2.22  tff(c_2141, plain, (![A_1490, B_1491, C_1492]: (r2_hidden('#skF_1'(A_1490, B_1491, C_1492), A_1490) | r2_hidden('#skF_2'(A_1490, B_1491, C_1492), B_1491) | ~r2_hidden('#skF_2'(A_1490, B_1491, C_1492), A_1490) | k4_xboole_0(A_1490, B_1491)=C_1492)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.87/2.22  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.87/2.22  tff(c_3384, plain, (![A_1948, B_1949]: (r2_hidden('#skF_2'(A_1948, B_1949, A_1948), B_1949) | ~r2_hidden('#skF_2'(A_1948, B_1949, A_1948), A_1948) | k4_xboole_0(A_1948, B_1949)=A_1948)), inference(resolution, [status(thm)], [c_2141, c_8])).
% 5.87/2.22  tff(c_3899, plain, (![A_2122, B_2123]: (r2_hidden('#skF_2'(A_2122, B_2123, A_2122), B_2123) | k4_xboole_0(A_2122, B_2123)=A_2122)), inference(resolution, [status(thm)], [c_1342, c_3384])).
% 5.87/2.22  tff(c_22, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.87/2.22  tff(c_6975, plain, (![A_2550, A_2551]: ('#skF_2'(A_2550, k1_tarski(A_2551), A_2550)=A_2551 | k4_xboole_0(A_2550, k1_tarski(A_2551))=A_2550)), inference(resolution, [status(thm)], [c_3899, c_22])).
% 5.87/2.22  tff(c_7247, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_6975, c_79])).
% 5.87/2.22  tff(c_7262, plain, (r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_7247, c_1342])).
% 5.87/2.22  tff(c_7310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_61, c_7262])).
% 5.87/2.22  tff(c_7311, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 5.87/2.22  tff(c_24, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.87/2.22  tff(c_7312, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 5.87/2.22  tff(c_48, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.87/2.22  tff(c_7368, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7312, c_48])).
% 5.87/2.22  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.87/2.22  tff(c_7379, plain, (![D_2614]: (~r2_hidden(D_2614, k1_tarski('#skF_8')) | ~r2_hidden(D_2614, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_7368, c_4])).
% 5.87/2.22  tff(c_7383, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_24, c_7379])).
% 5.87/2.22  tff(c_7387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7311, c_7383])).
% 5.87/2.22  tff(c_7388, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 5.87/2.22  tff(c_7389, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 5.87/2.22  tff(c_50, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.87/2.22  tff(c_7416, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7389, c_50])).
% 5.87/2.22  tff(c_7421, plain, (![D_2621, B_2622, A_2623]: (~r2_hidden(D_2621, B_2622) | ~r2_hidden(D_2621, k4_xboole_0(A_2623, B_2622)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.87/2.22  tff(c_7425, plain, (![D_2624]: (~r2_hidden(D_2624, k1_tarski('#skF_8')) | ~r2_hidden(D_2624, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_7416, c_7421])).
% 5.87/2.22  tff(c_7429, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_24, c_7425])).
% 5.87/2.22  tff(c_7433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7388, c_7429])).
% 5.87/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.22  
% 5.87/2.22  Inference rules
% 5.87/2.22  ----------------------
% 5.87/2.22  #Ref     : 0
% 5.87/2.22  #Sup     : 1615
% 5.87/2.22  #Fact    : 0
% 5.87/2.22  #Define  : 0
% 5.87/2.22  #Split   : 7
% 5.87/2.22  #Chain   : 0
% 5.87/2.22  #Close   : 0
% 5.87/2.22  
% 5.87/2.22  Ordering : KBO
% 5.87/2.22  
% 5.87/2.22  Simplification rules
% 5.87/2.22  ----------------------
% 5.87/2.22  #Subsume      : 521
% 5.87/2.22  #Demod        : 333
% 5.87/2.22  #Tautology    : 354
% 5.87/2.22  #SimpNegUnit  : 113
% 5.87/2.22  #BackRed      : 2
% 5.87/2.22  
% 5.87/2.22  #Partial instantiations: 1350
% 5.87/2.22  #Strategies tried      : 1
% 5.87/2.22  
% 5.87/2.22  Timing (in seconds)
% 5.87/2.22  ----------------------
% 5.87/2.22  Preprocessing        : 0.33
% 5.87/2.22  Parsing              : 0.16
% 5.87/2.22  CNF conversion       : 0.03
% 5.87/2.22  Main loop            : 1.08
% 5.87/2.22  Inferencing          : 0.42
% 5.87/2.22  Reduction            : 0.29
% 5.87/2.22  Demodulation         : 0.20
% 5.87/2.22  BG Simplification    : 0.05
% 5.87/2.22  Subsumption          : 0.23
% 5.87/2.22  Abstraction          : 0.07
% 5.87/2.22  MUC search           : 0.00
% 5.87/2.22  Cooper               : 0.00
% 5.87/2.22  Total                : 1.44
% 5.87/2.22  Index Insertion      : 0.00
% 5.87/2.22  Index Deletion       : 0.00
% 5.87/2.22  Index Matching       : 0.00
% 5.87/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
