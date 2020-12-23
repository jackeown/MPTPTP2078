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
% DateTime   : Thu Dec  3 09:54:33 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 102 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 165 expanded)
%              Number of equality atoms :   25 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_60,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_295,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_tarski(A_65),B_66)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_303,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(k1_tarski(A_65),B_66) = k1_xboole_0
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_295,c_30])).

tff(c_42,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_323,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_3'(A_74,B_75),B_75)
      | r1_xboole_0(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1172,plain,(
    ! [A_157,A_158,B_159] :
      ( ~ r2_hidden('#skF_3'(A_157,k4_xboole_0(A_158,B_159)),B_159)
      | r1_xboole_0(A_157,k4_xboole_0(A_158,B_159)) ) ),
    inference(resolution,[status(thm)],[c_323,c_6])).

tff(c_1202,plain,(
    ! [A_160,A_161] : r1_xboole_0(A_160,k4_xboole_0(A_161,A_160)) ),
    inference(resolution,[status(thm)],[c_26,c_1172])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = A_21
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1224,plain,(
    ! [A_160,A_161] : k4_xboole_0(A_160,k4_xboole_0(A_161,A_160)) = A_160 ),
    inference(resolution,[status(thm)],[c_1202,c_38])).

tff(c_1230,plain,(
    ! [A_162,A_163] : k4_xboole_0(A_162,k4_xboole_0(A_163,A_162)) = A_162 ),
    inference(resolution,[status(thm)],[c_1202,c_38])).

tff(c_1497,plain,(
    ! [A_175,A_176] : k4_xboole_0(k4_xboole_0(A_175,A_176),A_176) = k4_xboole_0(A_175,A_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_1224,c_1230])).

tff(c_1538,plain,(
    ! [A_176,A_175] : k5_xboole_0(A_176,k4_xboole_0(A_175,A_176)) = k2_xboole_0(A_176,k4_xboole_0(A_175,A_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_42])).

tff(c_1707,plain,(
    ! [A_181,A_182] : k2_xboole_0(A_181,k4_xboole_0(A_182,A_181)) = k2_xboole_0(A_181,A_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1538])).

tff(c_1743,plain,(
    ! [B_66,A_65] :
      ( k2_xboole_0(B_66,k1_tarski(A_65)) = k2_xboole_0(B_66,k1_xboole_0)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_1707])).

tff(c_2319,plain,(
    ! [B_203,A_204] :
      ( k2_xboole_0(B_203,k1_tarski(A_204)) = B_203
      | ~ r2_hidden(A_204,B_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1743])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1593,plain,(
    ! [A_176,A_175] : k2_xboole_0(A_176,k4_xboole_0(A_175,A_176)) = k2_xboole_0(A_176,A_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1538])).

tff(c_58,plain,(
    k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_61,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k4_xboole_0('#skF_5',k1_tarski('#skF_4'))) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_1705,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1593,c_61])).

tff(c_1706,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1705])).

tff(c_2325,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2319,c_1706])).

tff(c_2363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:47:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.67  
% 3.70/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.70/1.67  
% 3.70/1.67  %Foreground sorts:
% 3.70/1.67  
% 3.70/1.67  
% 3.70/1.67  %Background operators:
% 3.70/1.67  
% 3.70/1.67  
% 3.70/1.67  %Foreground operators:
% 3.70/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.70/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.70/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.70/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.70/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.70/1.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.70/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.70/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.70/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.70/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.70/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.70/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.70/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.70/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.70/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.70/1.67  
% 3.70/1.68  tff(f_90, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 3.70/1.68  tff(f_63, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.70/1.68  tff(f_83, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.70/1.68  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.70/1.68  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.70/1.68  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.70/1.68  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.70/1.68  tff(f_69, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.70/1.68  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.70/1.68  tff(c_60, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.70/1.68  tff(c_34, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.70/1.68  tff(c_295, plain, (![A_65, B_66]: (r1_tarski(k1_tarski(A_65), B_66) | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.70/1.68  tff(c_30, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.70/1.68  tff(c_303, plain, (![A_65, B_66]: (k4_xboole_0(k1_tarski(A_65), B_66)=k1_xboole_0 | ~r2_hidden(A_65, B_66))), inference(resolution, [status(thm)], [c_295, c_30])).
% 3.70/1.68  tff(c_42, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.68  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.70/1.68  tff(c_323, plain, (![A_74, B_75]: (r2_hidden('#skF_3'(A_74, B_75), B_75) | r1_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.70/1.68  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.70/1.68  tff(c_1172, plain, (![A_157, A_158, B_159]: (~r2_hidden('#skF_3'(A_157, k4_xboole_0(A_158, B_159)), B_159) | r1_xboole_0(A_157, k4_xboole_0(A_158, B_159)))), inference(resolution, [status(thm)], [c_323, c_6])).
% 3.70/1.68  tff(c_1202, plain, (![A_160, A_161]: (r1_xboole_0(A_160, k4_xboole_0(A_161, A_160)))), inference(resolution, [status(thm)], [c_26, c_1172])).
% 3.70/1.68  tff(c_38, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=A_21 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.70/1.68  tff(c_1224, plain, (![A_160, A_161]: (k4_xboole_0(A_160, k4_xboole_0(A_161, A_160))=A_160)), inference(resolution, [status(thm)], [c_1202, c_38])).
% 3.70/1.68  tff(c_1230, plain, (![A_162, A_163]: (k4_xboole_0(A_162, k4_xboole_0(A_163, A_162))=A_162)), inference(resolution, [status(thm)], [c_1202, c_38])).
% 3.70/1.68  tff(c_1497, plain, (![A_175, A_176]: (k4_xboole_0(k4_xboole_0(A_175, A_176), A_176)=k4_xboole_0(A_175, A_176))), inference(superposition, [status(thm), theory('equality')], [c_1224, c_1230])).
% 3.70/1.68  tff(c_1538, plain, (![A_176, A_175]: (k5_xboole_0(A_176, k4_xboole_0(A_175, A_176))=k2_xboole_0(A_176, k4_xboole_0(A_175, A_176)))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_42])).
% 3.70/1.68  tff(c_1707, plain, (![A_181, A_182]: (k2_xboole_0(A_181, k4_xboole_0(A_182, A_181))=k2_xboole_0(A_181, A_182))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1538])).
% 3.70/1.68  tff(c_1743, plain, (![B_66, A_65]: (k2_xboole_0(B_66, k1_tarski(A_65))=k2_xboole_0(B_66, k1_xboole_0) | ~r2_hidden(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_303, c_1707])).
% 3.70/1.68  tff(c_2319, plain, (![B_203, A_204]: (k2_xboole_0(B_203, k1_tarski(A_204))=B_203 | ~r2_hidden(A_204, B_203))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1743])).
% 3.70/1.68  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.70/1.68  tff(c_1593, plain, (![A_176, A_175]: (k2_xboole_0(A_176, k4_xboole_0(A_175, A_176))=k2_xboole_0(A_176, A_175))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1538])).
% 3.70/1.68  tff(c_58, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.70/1.68  tff(c_61, plain, (k2_xboole_0(k1_tarski('#skF_4'), k4_xboole_0('#skF_5', k1_tarski('#skF_4')))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_58])).
% 3.70/1.68  tff(c_1705, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1593, c_61])).
% 3.70/1.68  tff(c_1706, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1705])).
% 3.70/1.68  tff(c_2325, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2319, c_1706])).
% 3.70/1.68  tff(c_2363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_2325])).
% 3.70/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.68  
% 3.70/1.68  Inference rules
% 3.70/1.68  ----------------------
% 3.70/1.68  #Ref     : 0
% 3.70/1.68  #Sup     : 545
% 3.70/1.68  #Fact    : 0
% 3.70/1.68  #Define  : 0
% 3.70/1.68  #Split   : 0
% 3.70/1.68  #Chain   : 0
% 3.70/1.68  #Close   : 0
% 3.70/1.68  
% 3.70/1.68  Ordering : KBO
% 3.70/1.68  
% 3.70/1.68  Simplification rules
% 3.70/1.68  ----------------------
% 3.70/1.68  #Subsume      : 80
% 3.70/1.68  #Demod        : 330
% 3.70/1.68  #Tautology    : 330
% 3.70/1.68  #SimpNegUnit  : 7
% 3.70/1.68  #BackRed      : 3
% 3.70/1.68  
% 3.70/1.68  #Partial instantiations: 0
% 3.70/1.68  #Strategies tried      : 1
% 3.70/1.68  
% 3.70/1.68  Timing (in seconds)
% 3.70/1.68  ----------------------
% 3.70/1.68  Preprocessing        : 0.36
% 3.70/1.68  Parsing              : 0.19
% 3.70/1.68  CNF conversion       : 0.02
% 3.70/1.68  Main loop            : 0.51
% 3.70/1.68  Inferencing          : 0.18
% 3.70/1.68  Reduction            : 0.18
% 3.70/1.68  Demodulation         : 0.13
% 3.70/1.68  BG Simplification    : 0.02
% 3.81/1.68  Subsumption          : 0.09
% 3.81/1.68  Abstraction          : 0.03
% 3.81/1.68  MUC search           : 0.00
% 3.81/1.68  Cooper               : 0.00
% 3.81/1.68  Total                : 0.90
% 3.81/1.68  Index Insertion      : 0.00
% 3.81/1.68  Index Deletion       : 0.00
% 3.81/1.68  Index Matching       : 0.00
% 3.81/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
