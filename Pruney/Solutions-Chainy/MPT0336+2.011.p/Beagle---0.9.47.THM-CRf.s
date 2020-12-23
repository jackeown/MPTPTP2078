%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:01 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   60 (  70 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 (  90 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
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

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    ! [A_41,B_42] :
      ( r1_xboole_0(k1_tarski(A_41),B_42)
      | r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_140,plain,(
    ! [B_51,A_52] :
      ( r1_xboole_0(B_51,A_52)
      | ~ r1_xboole_0(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_146,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_140])).

tff(c_2060,plain,(
    ! [A_145,B_146,C_147] :
      ( k3_xboole_0(A_145,k2_xboole_0(B_146,C_147)) = k3_xboole_0(A_145,C_147)
      | ~ r1_xboole_0(A_145,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_194,plain,(
    ! [A_59,B_60] :
      ( r1_xboole_0(A_59,B_60)
      | k3_xboole_0(A_59,B_60) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_202,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_194,c_54])).

tff(c_206,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_202])).

tff(c_2120,plain,
    ( k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2060,c_206])).

tff(c_2187,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2120])).

tff(c_400,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | r1_xboole_0(A_77,k3_xboole_0(B_78,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3659,plain,(
    ! [A_167,B_168,C_169] :
      ( k3_xboole_0(A_167,k3_xboole_0(B_168,C_169)) = k1_xboole_0
      | ~ r1_xboole_0(A_167,B_168) ) ),
    inference(resolution,[status(thm)],[c_400,c_6])).

tff(c_52,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_53,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_52])).

tff(c_379,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,B_74) = A_73
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_383,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_379])).

tff(c_682,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_4])).

tff(c_3687,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3659,c_682])).

tff(c_3912,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2187,c_3687])).

tff(c_4011,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_3912])).

tff(c_1031,plain,(
    ! [A_108,B_109,C_110] :
      ( ~ r1_xboole_0(A_108,B_109)
      | ~ r2_hidden(C_110,B_109)
      | ~ r2_hidden(C_110,A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1070,plain,(
    ! [C_110] :
      ( ~ r2_hidden(C_110,'#skF_3')
      | ~ r2_hidden(C_110,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_1031])).

tff(c_4032,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_4011,c_1070])).

tff(c_4036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4032])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.89  
% 4.35/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.89  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.35/1.89  
% 4.35/1.89  %Foreground sorts:
% 4.35/1.89  
% 4.35/1.89  
% 4.35/1.89  %Background operators:
% 4.35/1.89  
% 4.35/1.89  
% 4.35/1.89  %Foreground operators:
% 4.35/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.35/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.35/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.35/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.35/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.35/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.35/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.35/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.35/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.35/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.35/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.35/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.35/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.35/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.35/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.35/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.35/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.35/1.89  
% 4.35/1.90  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.35/1.90  tff(f_94, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.35/1.90  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.35/1.90  tff(f_75, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.35/1.90  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.35/1.90  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.35/1.90  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.35/1.90  tff(f_71, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 4.35/1.90  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.35/1.90  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.35/1.90  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.35/1.90  tff(c_44, plain, (![A_41, B_42]: (r1_xboole_0(k1_tarski(A_41), B_42) | r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.35/1.90  tff(c_48, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.35/1.90  tff(c_140, plain, (![B_51, A_52]: (r1_xboole_0(B_51, A_52) | ~r1_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.35/1.90  tff(c_146, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_140])).
% 4.35/1.90  tff(c_2060, plain, (![A_145, B_146, C_147]: (k3_xboole_0(A_145, k2_xboole_0(B_146, C_147))=k3_xboole_0(A_145, C_147) | ~r1_xboole_0(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.35/1.90  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.35/1.90  tff(c_194, plain, (![A_59, B_60]: (r1_xboole_0(A_59, B_60) | k3_xboole_0(A_59, B_60)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.35/1.90  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.35/1.90  tff(c_46, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.35/1.90  tff(c_54, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 4.35/1.90  tff(c_202, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_194, c_54])).
% 4.35/1.90  tff(c_206, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_202])).
% 4.35/1.90  tff(c_2120, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0 | ~r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2060, c_206])).
% 4.35/1.90  tff(c_2187, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2120])).
% 4.35/1.90  tff(c_400, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | r1_xboole_0(A_77, k3_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.35/1.90  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.35/1.90  tff(c_3659, plain, (![A_167, B_168, C_169]: (k3_xboole_0(A_167, k3_xboole_0(B_168, C_169))=k1_xboole_0 | ~r1_xboole_0(A_167, B_168))), inference(resolution, [status(thm)], [c_400, c_6])).
% 4.35/1.90  tff(c_52, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.35/1.90  tff(c_53, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_52])).
% 4.35/1.90  tff(c_379, plain, (![A_73, B_74]: (k3_xboole_0(A_73, B_74)=A_73 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.35/1.90  tff(c_383, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_53, c_379])).
% 4.35/1.90  tff(c_682, plain, (k3_xboole_0(k1_tarski('#skF_5'), k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_383, c_4])).
% 4.35/1.90  tff(c_3687, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3659, c_682])).
% 4.35/1.90  tff(c_3912, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2187, c_3687])).
% 4.35/1.90  tff(c_4011, plain, (r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_3912])).
% 4.35/1.90  tff(c_1031, plain, (![A_108, B_109, C_110]: (~r1_xboole_0(A_108, B_109) | ~r2_hidden(C_110, B_109) | ~r2_hidden(C_110, A_108))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.35/1.90  tff(c_1070, plain, (![C_110]: (~r2_hidden(C_110, '#skF_3') | ~r2_hidden(C_110, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_1031])).
% 4.35/1.90  tff(c_4032, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_4011, c_1070])).
% 4.35/1.90  tff(c_4036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_4032])).
% 4.35/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.90  
% 4.35/1.90  Inference rules
% 4.35/1.90  ----------------------
% 4.35/1.90  #Ref     : 0
% 4.35/1.90  #Sup     : 977
% 4.35/1.90  #Fact    : 0
% 4.35/1.90  #Define  : 0
% 4.35/1.90  #Split   : 0
% 4.35/1.90  #Chain   : 0
% 4.35/1.90  #Close   : 0
% 4.35/1.90  
% 4.35/1.90  Ordering : KBO
% 4.35/1.90  
% 4.35/1.90  Simplification rules
% 4.35/1.90  ----------------------
% 4.35/1.90  #Subsume      : 45
% 4.35/1.90  #Demod        : 690
% 4.35/1.90  #Tautology    : 674
% 4.35/1.90  #SimpNegUnit  : 6
% 4.35/1.90  #BackRed      : 2
% 4.35/1.90  
% 4.35/1.90  #Partial instantiations: 0
% 4.35/1.90  #Strategies tried      : 1
% 4.35/1.90  
% 4.35/1.90  Timing (in seconds)
% 4.35/1.90  ----------------------
% 4.35/1.90  Preprocessing        : 0.34
% 4.35/1.90  Parsing              : 0.18
% 4.35/1.90  CNF conversion       : 0.02
% 4.35/1.90  Main loop            : 0.75
% 4.35/1.90  Inferencing          : 0.24
% 4.35/1.90  Reduction            : 0.32
% 4.35/1.90  Demodulation         : 0.25
% 4.35/1.90  BG Simplification    : 0.03
% 4.35/1.90  Subsumption          : 0.12
% 4.35/1.90  Abstraction          : 0.03
% 4.35/1.90  MUC search           : 0.00
% 4.35/1.90  Cooper               : 0.00
% 4.35/1.90  Total                : 1.12
% 4.35/1.90  Index Insertion      : 0.00
% 4.35/1.90  Index Deletion       : 0.00
% 4.35/1.90  Index Matching       : 0.00
% 4.35/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
