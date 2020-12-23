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
% DateTime   : Thu Dec  3 09:52:47 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :   53 (  64 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  87 expanded)
%              Number of equality atoms :   34 (  53 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_64,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_68,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_795,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(B_82,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2234,plain,(
    ! [B_137,A_138] :
      ( B_137 = A_138
      | ~ r1_tarski(B_137,A_138)
      | k4_xboole_0(A_138,B_137) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_795])).

tff(c_2424,plain,(
    ! [B_146,A_147] :
      ( B_146 = A_147
      | k4_xboole_0(B_146,A_147) != k1_xboole_0
      | k4_xboole_0(A_147,B_146) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_2234])).

tff(c_2440,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2424])).

tff(c_2459,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2440])).

tff(c_44,plain,(
    ! [C_27] : r2_hidden(C_27,k1_tarski(C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_418,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,k1_tarski(B_66)) = A_65
      | r2_hidden(B_66,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_444,plain,
    ( k1_xboole_0 = '#skF_3'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_68])).

tff(c_473,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_444])).

tff(c_32,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_148,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_164,plain,(
    ! [A_15,B_16] : k4_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_148])).

tff(c_3303,plain,(
    ! [B_175,B_176] :
      ( k4_xboole_0(k1_tarski(B_175),B_176) = k1_xboole_0
      | r2_hidden(B_175,k4_xboole_0(k1_tarski(B_175),B_176)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_418])).

tff(c_30,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1136,plain,(
    ! [A_102,B_103] : k2_xboole_0(k4_xboole_0(A_102,B_103),k4_xboole_0(B_103,A_102)) = k5_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1186,plain,(
    k2_xboole_0(k4_xboole_0(k1_tarski('#skF_4'),'#skF_3'),k1_xboole_0) = k5_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1136])).

tff(c_1212,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1186])).

tff(c_2192,plain,(
    ! [A_134,C_135,B_136] :
      ( ~ r2_hidden(A_134,C_135)
      | ~ r2_hidden(A_134,B_136)
      | ~ r2_hidden(A_134,k5_xboole_0(B_136,C_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2210,plain,(
    ! [A_134] :
      ( ~ r2_hidden(A_134,'#skF_3')
      | ~ r2_hidden(A_134,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_134,k4_xboole_0(k1_tarski('#skF_4'),'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1212,c_2192])).

tff(c_3311,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3303,c_2210])).

tff(c_3345,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_473,c_3311])).

tff(c_3347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2459,c_3345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.78  
% 4.01/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.79  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.01/1.79  
% 4.01/1.79  %Foreground sorts:
% 4.01/1.79  
% 4.01/1.79  
% 4.01/1.79  %Background operators:
% 4.01/1.79  
% 4.01/1.79  
% 4.01/1.79  %Foreground operators:
% 4.01/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.01/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.01/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.01/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.01/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.01/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.01/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.01/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.01/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.01/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.01/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.01/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.01/1.79  
% 4.11/1.80  tff(f_90, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 4.11/1.80  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.11/1.80  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.11/1.80  tff(f_69, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.11/1.80  tff(f_80, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.11/1.80  tff(f_54, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.11/1.80  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.11/1.80  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.11/1.80  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 4.11/1.80  tff(c_64, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.11/1.80  tff(c_68, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.11/1.80  tff(c_22, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | k4_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.11/1.80  tff(c_795, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(B_82, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.11/1.80  tff(c_2234, plain, (![B_137, A_138]: (B_137=A_138 | ~r1_tarski(B_137, A_138) | k4_xboole_0(A_138, B_137)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_795])).
% 4.11/1.80  tff(c_2424, plain, (![B_146, A_147]: (B_146=A_147 | k4_xboole_0(B_146, A_147)!=k1_xboole_0 | k4_xboole_0(A_147, B_146)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_2234])).
% 4.11/1.80  tff(c_2440, plain, (k1_tarski('#skF_4')='#skF_3' | k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_68, c_2424])).
% 4.11/1.80  tff(c_2459, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_2440])).
% 4.11/1.80  tff(c_44, plain, (![C_27]: (r2_hidden(C_27, k1_tarski(C_27)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.11/1.80  tff(c_66, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.11/1.80  tff(c_418, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k1_tarski(B_66))=A_65 | r2_hidden(B_66, A_65))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.11/1.80  tff(c_444, plain, (k1_xboole_0='#skF_3' | r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_418, c_68])).
% 4.11/1.80  tff(c_473, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_444])).
% 4.11/1.80  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.11/1.80  tff(c_148, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.11/1.80  tff(c_164, plain, (![A_15, B_16]: (k4_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_148])).
% 4.11/1.80  tff(c_3303, plain, (![B_175, B_176]: (k4_xboole_0(k1_tarski(B_175), B_176)=k1_xboole_0 | r2_hidden(B_175, k4_xboole_0(k1_tarski(B_175), B_176)))), inference(superposition, [status(thm), theory('equality')], [c_164, c_418])).
% 4.11/1.80  tff(c_30, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.11/1.80  tff(c_1136, plain, (![A_102, B_103]: (k2_xboole_0(k4_xboole_0(A_102, B_103), k4_xboole_0(B_103, A_102))=k5_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.11/1.80  tff(c_1186, plain, (k2_xboole_0(k4_xboole_0(k1_tarski('#skF_4'), '#skF_3'), k1_xboole_0)=k5_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_68, c_1136])).
% 4.11/1.80  tff(c_1212, plain, (k5_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1186])).
% 4.11/1.80  tff(c_2192, plain, (![A_134, C_135, B_136]: (~r2_hidden(A_134, C_135) | ~r2_hidden(A_134, B_136) | ~r2_hidden(A_134, k5_xboole_0(B_136, C_135)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.11/1.80  tff(c_2210, plain, (![A_134]: (~r2_hidden(A_134, '#skF_3') | ~r2_hidden(A_134, k1_tarski('#skF_4')) | ~r2_hidden(A_134, k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1212, c_2192])).
% 4.11/1.80  tff(c_3311, plain, (~r2_hidden('#skF_4', '#skF_3') | ~r2_hidden('#skF_4', k1_tarski('#skF_4')) | k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3303, c_2210])).
% 4.11/1.80  tff(c_3345, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_473, c_3311])).
% 4.11/1.80  tff(c_3347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2459, c_3345])).
% 4.11/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.80  
% 4.11/1.80  Inference rules
% 4.11/1.80  ----------------------
% 4.11/1.80  #Ref     : 0
% 4.11/1.80  #Sup     : 768
% 4.11/1.80  #Fact    : 0
% 4.11/1.80  #Define  : 0
% 4.11/1.80  #Split   : 0
% 4.11/1.80  #Chain   : 0
% 4.11/1.80  #Close   : 0
% 4.11/1.80  
% 4.11/1.80  Ordering : KBO
% 4.11/1.80  
% 4.11/1.80  Simplification rules
% 4.11/1.80  ----------------------
% 4.11/1.80  #Subsume      : 110
% 4.11/1.80  #Demod        : 623
% 4.11/1.80  #Tautology    : 505
% 4.11/1.80  #SimpNegUnit  : 33
% 4.11/1.80  #BackRed      : 0
% 4.11/1.80  
% 4.11/1.80  #Partial instantiations: 0
% 4.11/1.80  #Strategies tried      : 1
% 4.11/1.80  
% 4.11/1.80  Timing (in seconds)
% 4.11/1.80  ----------------------
% 4.11/1.81  Preprocessing        : 0.39
% 4.11/1.81  Parsing              : 0.21
% 4.11/1.81  CNF conversion       : 0.03
% 4.11/1.81  Main loop            : 0.64
% 4.11/1.81  Inferencing          : 0.22
% 4.11/1.81  Reduction            : 0.25
% 4.11/1.81  Demodulation         : 0.19
% 4.11/1.81  BG Simplification    : 0.03
% 4.11/1.81  Subsumption          : 0.10
% 4.11/1.81  Abstraction          : 0.04
% 4.11/1.81  MUC search           : 0.00
% 4.11/1.81  Cooper               : 0.00
% 4.11/1.81  Total                : 1.07
% 4.11/1.81  Index Insertion      : 0.00
% 4.11/1.81  Index Deletion       : 0.00
% 4.11/1.81  Index Matching       : 0.00
% 4.11/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
