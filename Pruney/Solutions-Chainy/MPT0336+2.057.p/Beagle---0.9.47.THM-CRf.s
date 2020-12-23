%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:08 EST 2020

% Result     : Theorem 8.20s
% Output     : CNFRefutation 8.20s
% Verified   : 
% Statistics : Number of formulae       :   60 (  90 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 134 expanded)
%              Number of equality atoms :   14 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(k1_tarski(A_33),B_34)
      | r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_344,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | r1_xboole_0(A_69,k3_xboole_0(B_70,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2627,plain,(
    ! [A_149,B_150,C_151] :
      ( k3_xboole_0(A_149,k3_xboole_0(B_150,C_151)) = k1_xboole_0
      | ~ r1_xboole_0(A_149,B_150) ) ),
    inference(resolution,[status(thm)],[c_344,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_49,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_150,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_154,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_150])).

tff(c_313,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_2])).

tff(c_2644,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2627,c_313])).

tff(c_2871,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2644])).

tff(c_2891,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_2871])).

tff(c_44,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_620,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,B_84)
      | ~ r2_hidden(C_85,A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_665,plain,(
    ! [C_85] :
      ( ~ r2_hidden(C_85,'#skF_3')
      | ~ r2_hidden(C_85,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_620])).

tff(c_2895,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2891,c_665])).

tff(c_2899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2895])).

tff(c_2900,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2644])).

tff(c_192,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(A_52,B_53)
      | k3_xboole_0(A_52,B_53) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_206,plain,(
    ! [B_53,A_52] :
      ( r1_xboole_0(B_53,A_52)
      | k3_xboole_0(A_52,B_53) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_192,c_8])).

tff(c_59,plain,(
    ! [B_36,A_37] :
      ( r1_xboole_0(B_36,A_37)
      | ~ r1_xboole_0(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_912,plain,(
    ! [A_93,C_94,B_95] :
      ( ~ r1_xboole_0(A_93,C_94)
      | ~ r1_xboole_0(A_93,B_95)
      | r1_xboole_0(A_93,k2_xboole_0(B_95,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_15705,plain,(
    ! [B_273,C_274,A_275] :
      ( r1_xboole_0(k2_xboole_0(B_273,C_274),A_275)
      | ~ r1_xboole_0(A_275,C_274)
      | ~ r1_xboole_0(A_275,B_273) ) ),
    inference(resolution,[status(thm)],[c_912,c_8])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_15742,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_15705,c_42])).

tff(c_15755,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_15742])).

tff(c_15761,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_206,c_15755])).

tff(c_15772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2900,c_2,c_15761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:42:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.20/2.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/2.94  
% 8.20/2.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/2.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.20/2.94  
% 8.20/2.94  %Foreground sorts:
% 8.20/2.94  
% 8.20/2.94  
% 8.20/2.94  %Background operators:
% 8.20/2.94  
% 8.20/2.94  
% 8.20/2.94  %Foreground operators:
% 8.20/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.20/2.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.20/2.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.20/2.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.20/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.20/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.20/2.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.20/2.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.20/2.94  tff('#skF_5', type, '#skF_5': $i).
% 8.20/2.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.20/2.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.20/2.94  tff('#skF_2', type, '#skF_2': $i).
% 8.20/2.94  tff('#skF_3', type, '#skF_3': $i).
% 8.20/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.20/2.94  tff('#skF_4', type, '#skF_4': $i).
% 8.20/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.20/2.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.20/2.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.20/2.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.20/2.94  
% 8.20/2.95  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 8.20/2.95  tff(f_98, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 8.20/2.95  tff(f_83, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 8.20/2.95  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.20/2.95  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.20/2.95  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.20/2.95  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.20/2.95  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.20/2.95  tff(f_77, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.20/2.95  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.20/2.95  tff(c_40, plain, (![A_33, B_34]: (r1_xboole_0(k1_tarski(A_33), B_34) | r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.20/2.95  tff(c_344, plain, (![A_69, B_70, C_71]: (~r1_xboole_0(A_69, B_70) | r1_xboole_0(A_69, k3_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.20/2.95  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.20/2.95  tff(c_2627, plain, (![A_149, B_150, C_151]: (k3_xboole_0(A_149, k3_xboole_0(B_150, C_151))=k1_xboole_0 | ~r1_xboole_0(A_149, B_150))), inference(resolution, [status(thm)], [c_344, c_4])).
% 8.20/2.95  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.20/2.95  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.20/2.95  tff(c_49, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 8.20/2.95  tff(c_150, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.20/2.95  tff(c_154, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_49, c_150])).
% 8.20/2.95  tff(c_313, plain, (k3_xboole_0(k1_tarski('#skF_5'), k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_154, c_2])).
% 8.20/2.95  tff(c_2644, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2627, c_313])).
% 8.20/2.95  tff(c_2871, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2644])).
% 8.20/2.95  tff(c_2891, plain, (r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_2871])).
% 8.20/2.95  tff(c_44, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.20/2.95  tff(c_620, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, B_84) | ~r2_hidden(C_85, A_83))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.20/2.95  tff(c_665, plain, (![C_85]: (~r2_hidden(C_85, '#skF_3') | ~r2_hidden(C_85, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_620])).
% 8.20/2.95  tff(c_2895, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2891, c_665])).
% 8.20/2.95  tff(c_2899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2895])).
% 8.20/2.95  tff(c_2900, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2644])).
% 8.20/2.95  tff(c_192, plain, (![A_52, B_53]: (r1_xboole_0(A_52, B_53) | k3_xboole_0(A_52, B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.20/2.95  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.20/2.95  tff(c_206, plain, (![B_53, A_52]: (r1_xboole_0(B_53, A_52) | k3_xboole_0(A_52, B_53)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_192, c_8])).
% 8.20/2.95  tff(c_59, plain, (![B_36, A_37]: (r1_xboole_0(B_36, A_37) | ~r1_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.20/2.95  tff(c_62, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_59])).
% 8.20/2.95  tff(c_912, plain, (![A_93, C_94, B_95]: (~r1_xboole_0(A_93, C_94) | ~r1_xboole_0(A_93, B_95) | r1_xboole_0(A_93, k2_xboole_0(B_95, C_94)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.20/2.95  tff(c_15705, plain, (![B_273, C_274, A_275]: (r1_xboole_0(k2_xboole_0(B_273, C_274), A_275) | ~r1_xboole_0(A_275, C_274) | ~r1_xboole_0(A_275, B_273))), inference(resolution, [status(thm)], [c_912, c_8])).
% 8.20/2.95  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.20/2.95  tff(c_15742, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_15705, c_42])).
% 8.20/2.95  tff(c_15755, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_15742])).
% 8.20/2.95  tff(c_15761, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_206, c_15755])).
% 8.20/2.95  tff(c_15772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2900, c_2, c_15761])).
% 8.20/2.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/2.95  
% 8.20/2.95  Inference rules
% 8.20/2.95  ----------------------
% 8.20/2.95  #Ref     : 0
% 8.20/2.95  #Sup     : 4036
% 8.20/2.95  #Fact    : 0
% 8.20/2.95  #Define  : 0
% 8.20/2.95  #Split   : 6
% 8.20/2.95  #Chain   : 0
% 8.20/2.95  #Close   : 0
% 8.20/2.95  
% 8.20/2.95  Ordering : KBO
% 8.20/2.95  
% 8.20/2.95  Simplification rules
% 8.20/2.95  ----------------------
% 8.20/2.95  #Subsume      : 243
% 8.20/2.95  #Demod        : 3540
% 8.20/2.95  #Tautology    : 2905
% 8.20/2.95  #SimpNegUnit  : 15
% 8.20/2.95  #BackRed      : 6
% 8.20/2.95  
% 8.20/2.95  #Partial instantiations: 0
% 8.20/2.95  #Strategies tried      : 1
% 8.20/2.95  
% 8.20/2.95  Timing (in seconds)
% 8.20/2.95  ----------------------
% 8.20/2.95  Preprocessing        : 0.32
% 8.20/2.95  Parsing              : 0.17
% 8.20/2.96  CNF conversion       : 0.02
% 8.20/2.96  Main loop            : 1.87
% 8.20/2.96  Inferencing          : 0.47
% 8.20/2.96  Reduction            : 0.94
% 8.20/2.96  Demodulation         : 0.79
% 8.20/2.96  BG Simplification    : 0.05
% 8.20/2.96  Subsumption          : 0.31
% 8.20/2.96  Abstraction          : 0.07
% 8.20/2.96  MUC search           : 0.00
% 8.20/2.96  Cooper               : 0.00
% 8.20/2.96  Total                : 2.22
% 8.20/2.96  Index Insertion      : 0.00
% 8.20/2.96  Index Deletion       : 0.00
% 8.20/2.96  Index Matching       : 0.00
% 8.20/2.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
