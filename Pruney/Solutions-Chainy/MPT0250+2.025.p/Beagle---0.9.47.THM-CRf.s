%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:35 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 108 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :   72 ( 165 expanded)
%              Number of equality atoms :   22 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_100,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_87,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_108,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_59,axiom,(
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

tff(c_76,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_102,plain,(
    ! [D_52,B_53] : r2_hidden(D_52,k2_tarski(D_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_105,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_102])).

tff(c_54,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_170,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_213,plain,(
    ! [B_65,A_66] : k3_tarski(k2_tarski(B_65,A_66)) = k2_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_170])).

tff(c_84,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_219,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,A_66) = k2_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_84])).

tff(c_88,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_255,plain,(
    r1_tarski(k2_xboole_0('#skF_7',k1_tarski('#skF_6')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_88])).

tff(c_38,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_313,plain,
    ( k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_xboole_0('#skF_7',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_255,c_38])).

tff(c_316,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_313])).

tff(c_337,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_xboole_0(A_77,C_78)
      | ~ r1_xboole_0(A_77,k2_xboole_0(B_79,C_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_340,plain,(
    ! [A_77] :
      ( r1_xboole_0(A_77,k1_tarski('#skF_6'))
      | ~ r1_xboole_0(A_77,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_337])).

tff(c_555,plain,(
    ! [A_111,B_112,C_113] :
      ( ~ r1_xboole_0(A_111,B_112)
      | ~ r2_hidden(C_113,B_112)
      | ~ r2_hidden(C_113,A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_742,plain,(
    ! [C_137,A_138] :
      ( ~ r2_hidden(C_137,k1_tarski('#skF_6'))
      | ~ r2_hidden(C_137,A_138)
      | ~ r1_xboole_0(A_138,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_340,c_555])).

tff(c_755,plain,(
    ! [A_139] :
      ( ~ r2_hidden('#skF_6',A_139)
      | ~ r1_xboole_0(A_139,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_105,c_742])).

tff(c_769,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_105,c_755])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),A_10)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_509,plain,(
    ! [D_106,B_107,A_108] :
      ( D_106 = B_107
      | D_106 = A_108
      | ~ r2_hidden(D_106,k2_tarski(A_108,B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_539,plain,(
    ! [D_109,A_110] :
      ( D_109 = A_110
      | D_109 = A_110
      | ~ r2_hidden(D_109,k1_tarski(A_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_509])).

tff(c_857,plain,(
    ! [A_149,B_150] :
      ( '#skF_3'(k1_tarski(A_149),B_150) = A_149
      | r1_xboole_0(k1_tarski(A_149),B_150) ) ),
    inference(resolution,[status(thm)],[c_36,c_539])).

tff(c_875,plain,(
    '#skF_3'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_857,c_769])).

tff(c_34,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),B_11)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_905,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_34])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_769,c_86,c_905])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:21:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.57  
% 3.20/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2
% 3.20/1.57  
% 3.20/1.57  %Foreground sorts:
% 3.20/1.57  
% 3.20/1.57  
% 3.20/1.57  %Background operators:
% 3.20/1.57  
% 3.20/1.57  
% 3.20/1.57  %Foreground operators:
% 3.20/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.20/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.20/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.20/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.20/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.20/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.57  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.20/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.20/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.20/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.20/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.57  
% 3.20/1.58  tff(f_100, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.20/1.58  tff(f_98, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.20/1.58  tff(f_87, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.20/1.58  tff(f_89, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.20/1.58  tff(f_108, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.20/1.58  tff(f_113, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.20/1.58  tff(f_65, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.58  tff(f_83, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.20/1.58  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.20/1.58  tff(c_76, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.20/1.58  tff(c_102, plain, (![D_52, B_53]: (r2_hidden(D_52, k2_tarski(D_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.58  tff(c_105, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_102])).
% 3.20/1.58  tff(c_54, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.20/1.58  tff(c_56, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.20/1.58  tff(c_170, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.20/1.58  tff(c_213, plain, (![B_65, A_66]: (k3_tarski(k2_tarski(B_65, A_66))=k2_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_56, c_170])).
% 3.20/1.58  tff(c_84, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.20/1.58  tff(c_219, plain, (![B_65, A_66]: (k2_xboole_0(B_65, A_66)=k2_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_213, c_84])).
% 3.20/1.58  tff(c_88, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.20/1.58  tff(c_255, plain, (r1_tarski(k2_xboole_0('#skF_7', k1_tarski('#skF_6')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_88])).
% 3.20/1.58  tff(c_38, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.20/1.58  tff(c_313, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7' | ~r1_tarski('#skF_7', k2_xboole_0('#skF_7', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_255, c_38])).
% 3.20/1.58  tff(c_316, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_313])).
% 3.20/1.58  tff(c_337, plain, (![A_77, C_78, B_79]: (r1_xboole_0(A_77, C_78) | ~r1_xboole_0(A_77, k2_xboole_0(B_79, C_78)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.20/1.58  tff(c_340, plain, (![A_77]: (r1_xboole_0(A_77, k1_tarski('#skF_6')) | ~r1_xboole_0(A_77, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_316, c_337])).
% 3.20/1.58  tff(c_555, plain, (![A_111, B_112, C_113]: (~r1_xboole_0(A_111, B_112) | ~r2_hidden(C_113, B_112) | ~r2_hidden(C_113, A_111))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.58  tff(c_742, plain, (![C_137, A_138]: (~r2_hidden(C_137, k1_tarski('#skF_6')) | ~r2_hidden(C_137, A_138) | ~r1_xboole_0(A_138, '#skF_7'))), inference(resolution, [status(thm)], [c_340, c_555])).
% 3.20/1.58  tff(c_755, plain, (![A_139]: (~r2_hidden('#skF_6', A_139) | ~r1_xboole_0(A_139, '#skF_7'))), inference(resolution, [status(thm)], [c_105, c_742])).
% 3.20/1.58  tff(c_769, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_105, c_755])).
% 3.20/1.58  tff(c_86, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.20/1.58  tff(c_36, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), A_10) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.58  tff(c_509, plain, (![D_106, B_107, A_108]: (D_106=B_107 | D_106=A_108 | ~r2_hidden(D_106, k2_tarski(A_108, B_107)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.58  tff(c_539, plain, (![D_109, A_110]: (D_109=A_110 | D_109=A_110 | ~r2_hidden(D_109, k1_tarski(A_110)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_509])).
% 3.20/1.58  tff(c_857, plain, (![A_149, B_150]: ('#skF_3'(k1_tarski(A_149), B_150)=A_149 | r1_xboole_0(k1_tarski(A_149), B_150))), inference(resolution, [status(thm)], [c_36, c_539])).
% 3.20/1.58  tff(c_875, plain, ('#skF_3'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_857, c_769])).
% 3.20/1.58  tff(c_34, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), B_11) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.58  tff(c_905, plain, (r2_hidden('#skF_6', '#skF_7') | r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_875, c_34])).
% 3.20/1.58  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_769, c_86, c_905])).
% 3.20/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.58  
% 3.20/1.58  Inference rules
% 3.20/1.58  ----------------------
% 3.20/1.58  #Ref     : 0
% 3.20/1.58  #Sup     : 194
% 3.20/1.58  #Fact    : 0
% 3.20/1.58  #Define  : 0
% 3.20/1.58  #Split   : 1
% 3.20/1.58  #Chain   : 0
% 3.20/1.58  #Close   : 0
% 3.20/1.58  
% 3.20/1.58  Ordering : KBO
% 3.20/1.58  
% 3.20/1.58  Simplification rules
% 3.20/1.58  ----------------------
% 3.20/1.58  #Subsume      : 18
% 3.20/1.58  #Demod        : 42
% 3.20/1.58  #Tautology    : 81
% 3.20/1.58  #SimpNegUnit  : 2
% 3.20/1.58  #BackRed      : 2
% 3.20/1.58  
% 3.20/1.58  #Partial instantiations: 0
% 3.20/1.58  #Strategies tried      : 1
% 3.20/1.58  
% 3.20/1.58  Timing (in seconds)
% 3.20/1.58  ----------------------
% 3.20/1.58  Preprocessing        : 0.36
% 3.20/1.58  Parsing              : 0.18
% 3.20/1.58  CNF conversion       : 0.03
% 3.20/1.58  Main loop            : 0.39
% 3.20/1.58  Inferencing          : 0.13
% 3.20/1.58  Reduction            : 0.14
% 3.20/1.58  Demodulation         : 0.11
% 3.20/1.58  BG Simplification    : 0.02
% 3.20/1.58  Subsumption          : 0.08
% 3.20/1.58  Abstraction          : 0.02
% 3.20/1.59  MUC search           : 0.00
% 3.20/1.59  Cooper               : 0.00
% 3.20/1.59  Total                : 0.78
% 3.20/1.59  Index Insertion      : 0.00
% 3.20/1.59  Index Deletion       : 0.00
% 3.20/1.59  Index Matching       : 0.00
% 3.20/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
