%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:11 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   57 (  70 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 119 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_49,axiom,(
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

tff(f_104,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_38,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_192,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(C_65,B_64)
      | ~ r2_hidden(C_65,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_211,plain,(
    ! [C_66] :
      ( ~ r2_hidden(C_66,'#skF_4')
      | ~ r2_hidden(C_66,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_192])).

tff(c_225,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_211])).

tff(c_92,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(k1_tarski(A_36),B_37)
      | r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [B_37,A_36] :
      ( r1_xboole_0(B_37,k1_tarski(A_36))
      | r2_hidden(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_41,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_134,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),B_50)
      | r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_139,plain,(
    ! [A_10,B_11,A_49] :
      ( ~ r1_xboole_0(A_10,B_11)
      | r1_xboole_0(A_49,k3_xboole_0(A_10,B_11)) ) ),
    inference(resolution,[status(thm)],[c_134,c_14])).

tff(c_423,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r1_xboole_0(A_99,k3_xboole_0(B_100,C_101))
      | ~ r1_tarski(A_99,C_101)
      | r1_xboole_0(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_454,plain,(
    ! [A_103,B_104,A_105] :
      ( ~ r1_tarski(A_103,B_104)
      | r1_xboole_0(A_103,A_105)
      | ~ r1_xboole_0(A_105,B_104) ) ),
    inference(resolution,[status(thm)],[c_139,c_423])).

tff(c_462,plain,(
    ! [A_109] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),A_109)
      | ~ r1_xboole_0(A_109,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_41,c_454])).

tff(c_479,plain,(
    ! [B_110] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),B_110)
      | r2_hidden('#skF_6',B_110) ) ),
    inference(resolution,[status(thm)],[c_95,c_462])).

tff(c_109,plain,(
    ! [A_42,B_43] :
      ( ~ r1_xboole_0(k3_xboole_0(A_42,B_43),B_43)
      | r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_116,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(k3_xboole_0(B_2,A_1),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_490,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_479,c_116])).

tff(c_511,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_490])).

tff(c_522,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_511,c_4])).

tff(c_51,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_359,plain,(
    ! [A_85,C_86,B_87] :
      ( ~ r1_xboole_0(A_85,C_86)
      | ~ r1_xboole_0(A_85,B_87)
      | r1_xboole_0(A_85,k2_xboole_0(B_87,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_542,plain,(
    ! [B_112,C_113,A_114] :
      ( r1_xboole_0(k2_xboole_0(B_112,C_113),A_114)
      | ~ r1_xboole_0(A_114,C_113)
      | ~ r1_xboole_0(A_114,B_112) ) ),
    inference(resolution,[status(thm)],[c_359,c_4])).

tff(c_34,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_564,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_542,c_34])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_54,c_564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.37  
% 2.39/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.39/1.37  
% 2.39/1.37  %Foreground sorts:
% 2.39/1.37  
% 2.39/1.37  
% 2.39/1.37  %Background operators:
% 2.39/1.37  
% 2.39/1.37  
% 2.39/1.37  %Foreground operators:
% 2.39/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.39/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.39/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.39/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.39/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.39/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.39/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.39/1.37  
% 2.73/1.39  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 2.73/1.39  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.73/1.39  tff(f_104, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.73/1.39  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.73/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.73/1.39  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.73/1.39  tff(f_93, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.73/1.39  tff(f_85, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.73/1.39  tff(f_79, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.73/1.39  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.73/1.39  tff(c_36, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.73/1.39  tff(c_192, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(C_65, B_64) | ~r2_hidden(C_65, A_63))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.39  tff(c_211, plain, (![C_66]: (~r2_hidden(C_66, '#skF_4') | ~r2_hidden(C_66, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_192])).
% 2.73/1.39  tff(c_225, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_211])).
% 2.73/1.39  tff(c_92, plain, (![A_36, B_37]: (r1_xboole_0(k1_tarski(A_36), B_37) | r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.73/1.39  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.39  tff(c_95, plain, (![B_37, A_36]: (r1_xboole_0(B_37, k1_tarski(A_36)) | r2_hidden(A_36, B_37))), inference(resolution, [status(thm)], [c_92, c_4])).
% 2.73/1.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.73/1.39  tff(c_40, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.73/1.39  tff(c_41, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 2.73/1.39  tff(c_134, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), B_50) | r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.39  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.73/1.39  tff(c_139, plain, (![A_10, B_11, A_49]: (~r1_xboole_0(A_10, B_11) | r1_xboole_0(A_49, k3_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_134, c_14])).
% 2.73/1.39  tff(c_423, plain, (![A_99, B_100, C_101]: (~r1_xboole_0(A_99, k3_xboole_0(B_100, C_101)) | ~r1_tarski(A_99, C_101) | r1_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.73/1.39  tff(c_454, plain, (![A_103, B_104, A_105]: (~r1_tarski(A_103, B_104) | r1_xboole_0(A_103, A_105) | ~r1_xboole_0(A_105, B_104))), inference(resolution, [status(thm)], [c_139, c_423])).
% 2.73/1.39  tff(c_462, plain, (![A_109]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), A_109) | ~r1_xboole_0(A_109, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_41, c_454])).
% 2.73/1.39  tff(c_479, plain, (![B_110]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), B_110) | r2_hidden('#skF_6', B_110))), inference(resolution, [status(thm)], [c_95, c_462])).
% 2.73/1.39  tff(c_109, plain, (![A_42, B_43]: (~r1_xboole_0(k3_xboole_0(A_42, B_43), B_43) | r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.73/1.39  tff(c_116, plain, (![B_2, A_1]: (~r1_xboole_0(k3_xboole_0(B_2, A_1), B_2) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_109])).
% 2.73/1.39  tff(c_490, plain, (r1_xboole_0('#skF_3', '#skF_4') | r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_479, c_116])).
% 2.73/1.39  tff(c_511, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_225, c_490])).
% 2.73/1.39  tff(c_522, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_511, c_4])).
% 2.73/1.39  tff(c_51, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.39  tff(c_54, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_51])).
% 2.73/1.39  tff(c_359, plain, (![A_85, C_86, B_87]: (~r1_xboole_0(A_85, C_86) | ~r1_xboole_0(A_85, B_87) | r1_xboole_0(A_85, k2_xboole_0(B_87, C_86)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.73/1.39  tff(c_542, plain, (![B_112, C_113, A_114]: (r1_xboole_0(k2_xboole_0(B_112, C_113), A_114) | ~r1_xboole_0(A_114, C_113) | ~r1_xboole_0(A_114, B_112))), inference(resolution, [status(thm)], [c_359, c_4])).
% 2.73/1.39  tff(c_34, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.73/1.39  tff(c_564, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_542, c_34])).
% 2.73/1.39  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_522, c_54, c_564])).
% 2.73/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.39  
% 2.73/1.39  Inference rules
% 2.73/1.39  ----------------------
% 2.73/1.39  #Ref     : 0
% 2.73/1.39  #Sup     : 126
% 2.73/1.39  #Fact    : 0
% 2.73/1.39  #Define  : 0
% 2.73/1.39  #Split   : 0
% 2.73/1.39  #Chain   : 0
% 2.73/1.39  #Close   : 0
% 2.73/1.39  
% 2.73/1.39  Ordering : KBO
% 2.73/1.39  
% 2.73/1.39  Simplification rules
% 2.73/1.39  ----------------------
% 2.73/1.39  #Subsume      : 44
% 2.73/1.39  #Demod        : 8
% 2.73/1.39  #Tautology    : 25
% 2.73/1.39  #SimpNegUnit  : 1
% 2.73/1.39  #BackRed      : 0
% 2.73/1.39  
% 2.73/1.39  #Partial instantiations: 0
% 2.73/1.39  #Strategies tried      : 1
% 2.73/1.39  
% 2.73/1.39  Timing (in seconds)
% 2.73/1.39  ----------------------
% 2.73/1.39  Preprocessing        : 0.30
% 2.73/1.39  Parsing              : 0.16
% 2.73/1.39  CNF conversion       : 0.02
% 2.73/1.39  Main loop            : 0.28
% 2.73/1.39  Inferencing          : 0.11
% 2.73/1.39  Reduction            : 0.08
% 2.73/1.39  Demodulation         : 0.06
% 2.73/1.39  BG Simplification    : 0.02
% 2.73/1.39  Subsumption          : 0.06
% 2.73/1.39  Abstraction          : 0.01
% 2.73/1.39  MUC search           : 0.00
% 2.73/1.39  Cooper               : 0.00
% 2.73/1.39  Total                : 0.62
% 2.73/1.39  Index Insertion      : 0.00
% 2.73/1.39  Index Deletion       : 0.00
% 2.73/1.39  Index Matching       : 0.00
% 2.73/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
