%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:14 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 105 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 187 expanded)
%              Number of equality atoms :   19 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_51,axiom,(
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

tff(c_44,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_224,plain,(
    ! [B_63,A_64] :
      ( k1_tarski(B_63) = A_64
      | k1_xboole_0 = A_64
      | ~ r1_tarski(A_64,k1_tarski(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_234,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_5')
    | k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_224])).

tff(c_239,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_73,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(A_35,B_36)
      | k3_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [B_36,A_35] :
      ( r1_xboole_0(B_36,A_35)
      | k3_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_73,c_6])).

tff(c_40,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_56,plain,(
    ! [B_31,A_32] :
      ( r1_xboole_0(B_31,A_32)
      | ~ r1_xboole_0(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_371,plain,(
    ! [A_82,C_83,B_84] :
      ( ~ r1_xboole_0(A_82,C_83)
      | ~ r1_xboole_0(A_82,B_84)
      | r1_xboole_0(A_82,k2_xboole_0(B_84,C_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_595,plain,(
    ! [B_109,C_110,A_111] :
      ( r1_xboole_0(k2_xboole_0(B_109,C_110),A_111)
      | ~ r1_xboole_0(A_111,C_110)
      | ~ r1_xboole_0(A_111,B_109) ) ),
    inference(resolution,[status(thm)],[c_371,c_6])).

tff(c_38,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_617,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_595,c_38])).

tff(c_629,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_617])).

tff(c_632,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79,c_629])).

tff(c_639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_632])).

tff(c_640,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_641,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_642,plain,(
    k1_tarski('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_641])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_729,plain,(
    ! [A_132,C_133,B_134] :
      ( r1_xboole_0(k2_tarski(A_132,C_133),B_134)
      | r2_hidden(C_133,B_134)
      | r2_hidden(A_132,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_815,plain,(
    ! [A_147,B_148] :
      ( r1_xboole_0(k1_tarski(A_147),B_148)
      | r2_hidden(A_147,B_148)
      | r2_hidden(A_147,B_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_729])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( ~ r1_xboole_0(k3_xboole_0(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_650,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3')
    | r1_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_20])).

tff(c_654,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_650])).

tff(c_839,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_815,c_654])).

tff(c_663,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r1_xboole_0(A_112,B_113)
      | ~ r2_hidden(C_114,B_113)
      | ~ r2_hidden(C_114,A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_675,plain,(
    ! [C_114] :
      ( ~ r2_hidden(C_114,'#skF_3')
      | ~ r2_hidden(C_114,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_663])).

tff(c_849,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_839,c_675])).

tff(c_854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_849])).

tff(c_855,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_650])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_862,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_855,c_2])).

tff(c_879,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_640])).

tff(c_881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_642,c_879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:56:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.51  
% 3.04/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.04/1.51  
% 3.04/1.51  %Foreground sorts:
% 3.04/1.51  
% 3.04/1.51  
% 3.04/1.51  %Background operators:
% 3.04/1.51  
% 3.04/1.51  
% 3.04/1.51  %Foreground operators:
% 3.04/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.04/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.04/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.04/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.04/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.51  
% 3.08/1.53  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.08/1.53  tff(f_85, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.08/1.53  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.08/1.53  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.08/1.53  tff(f_67, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.08/1.53  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.08/1.53  tff(f_97, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 3.08/1.53  tff(f_73, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.08/1.53  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.08/1.53  tff(c_44, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.08/1.53  tff(c_224, plain, (![B_63, A_64]: (k1_tarski(B_63)=A_64 | k1_xboole_0=A_64 | ~r1_tarski(A_64, k1_tarski(B_63)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.08/1.53  tff(c_234, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_5') | k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_224])).
% 3.08/1.53  tff(c_239, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_234])).
% 3.08/1.53  tff(c_73, plain, (![A_35, B_36]: (r1_xboole_0(A_35, B_36) | k3_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.53  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.08/1.53  tff(c_79, plain, (![B_36, A_35]: (r1_xboole_0(B_36, A_35) | k3_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_73, c_6])).
% 3.08/1.53  tff(c_40, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.08/1.53  tff(c_56, plain, (![B_31, A_32]: (r1_xboole_0(B_31, A_32) | ~r1_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.08/1.53  tff(c_59, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_56])).
% 3.08/1.53  tff(c_371, plain, (![A_82, C_83, B_84]: (~r1_xboole_0(A_82, C_83) | ~r1_xboole_0(A_82, B_84) | r1_xboole_0(A_82, k2_xboole_0(B_84, C_83)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.08/1.53  tff(c_595, plain, (![B_109, C_110, A_111]: (r1_xboole_0(k2_xboole_0(B_109, C_110), A_111) | ~r1_xboole_0(A_111, C_110) | ~r1_xboole_0(A_111, B_109))), inference(resolution, [status(thm)], [c_371, c_6])).
% 3.08/1.53  tff(c_38, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.08/1.53  tff(c_617, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_595, c_38])).
% 3.08/1.53  tff(c_629, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_617])).
% 3.08/1.53  tff(c_632, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_79, c_629])).
% 3.08/1.53  tff(c_639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_632])).
% 3.08/1.53  tff(c_640, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_234])).
% 3.08/1.53  tff(c_641, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_234])).
% 3.08/1.53  tff(c_642, plain, (k1_tarski('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_640, c_641])).
% 3.08/1.53  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.08/1.53  tff(c_22, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.08/1.53  tff(c_729, plain, (![A_132, C_133, B_134]: (r1_xboole_0(k2_tarski(A_132, C_133), B_134) | r2_hidden(C_133, B_134) | r2_hidden(A_132, B_134))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.08/1.53  tff(c_815, plain, (![A_147, B_148]: (r1_xboole_0(k1_tarski(A_147), B_148) | r2_hidden(A_147, B_148) | r2_hidden(A_147, B_148))), inference(superposition, [status(thm), theory('equality')], [c_22, c_729])).
% 3.08/1.53  tff(c_20, plain, (![A_13, B_14]: (~r1_xboole_0(k3_xboole_0(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.08/1.53  tff(c_650, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3') | r1_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_640, c_20])).
% 3.08/1.53  tff(c_654, plain, (~r1_xboole_0(k1_tarski('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_650])).
% 3.08/1.53  tff(c_839, plain, (r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_815, c_654])).
% 3.08/1.53  tff(c_663, plain, (![A_112, B_113, C_114]: (~r1_xboole_0(A_112, B_113) | ~r2_hidden(C_114, B_113) | ~r2_hidden(C_114, A_112))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.53  tff(c_675, plain, (![C_114]: (~r2_hidden(C_114, '#skF_3') | ~r2_hidden(C_114, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_663])).
% 3.08/1.53  tff(c_849, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_839, c_675])).
% 3.08/1.53  tff(c_854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_849])).
% 3.08/1.53  tff(c_855, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_650])).
% 3.08/1.53  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.53  tff(c_862, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_855, c_2])).
% 3.08/1.53  tff(c_879, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_862, c_640])).
% 3.08/1.53  tff(c_881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_642, c_879])).
% 3.08/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.53  
% 3.08/1.53  Inference rules
% 3.08/1.53  ----------------------
% 3.08/1.53  #Ref     : 0
% 3.08/1.53  #Sup     : 201
% 3.08/1.53  #Fact    : 0
% 3.08/1.53  #Define  : 0
% 3.08/1.53  #Split   : 4
% 3.08/1.53  #Chain   : 0
% 3.08/1.53  #Close   : 0
% 3.08/1.53  
% 3.08/1.53  Ordering : KBO
% 3.08/1.53  
% 3.08/1.53  Simplification rules
% 3.08/1.53  ----------------------
% 3.08/1.53  #Subsume      : 35
% 3.08/1.53  #Demod        : 28
% 3.08/1.53  #Tautology    : 54
% 3.08/1.53  #SimpNegUnit  : 1
% 3.08/1.53  #BackRed      : 4
% 3.08/1.53  
% 3.08/1.53  #Partial instantiations: 0
% 3.08/1.53  #Strategies tried      : 1
% 3.08/1.53  
% 3.08/1.53  Timing (in seconds)
% 3.08/1.53  ----------------------
% 3.08/1.53  Preprocessing        : 0.32
% 3.08/1.53  Parsing              : 0.17
% 3.08/1.53  CNF conversion       : 0.02
% 3.08/1.53  Main loop            : 0.43
% 3.08/1.53  Inferencing          : 0.16
% 3.08/1.53  Reduction            : 0.11
% 3.08/1.53  Demodulation         : 0.08
% 3.08/1.53  BG Simplification    : 0.02
% 3.08/1.53  Subsumption          : 0.09
% 3.08/1.53  Abstraction          : 0.02
% 3.08/1.53  MUC search           : 0.00
% 3.08/1.53  Cooper               : 0.00
% 3.08/1.54  Total                : 0.78
% 3.08/1.54  Index Insertion      : 0.00
% 3.08/1.54  Index Deletion       : 0.00
% 3.08/1.54  Index Matching       : 0.00
% 3.08/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
