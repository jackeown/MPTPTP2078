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
% DateTime   : Thu Dec  3 09:55:05 EST 2020

% Result     : Theorem 8.31s
% Output     : CNFRefutation 8.31s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 155 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),k3_xboole_0(A_13,B_14))
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_155,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(k1_tarski(A_46),B_47)
      | r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_162,plain,(
    ! [B_47,A_46] :
      ( r1_xboole_0(B_47,k1_tarski(A_46))
      | r2_hidden(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_155,c_26])).

tff(c_58,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_163,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_167,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_389,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_398,plain,(
    ! [C_78] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7'))
      | ~ r2_hidden(C_78,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_389])).

tff(c_2646,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_2662,plain,(
    r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_162,c_2646])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2711,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_2662,c_6])).

tff(c_54,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_118,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_130,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_118])).

tff(c_404,plain,(
    ! [C_78] :
      ( ~ r1_xboole_0('#skF_6','#skF_5')
      | ~ r2_hidden(C_78,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_389])).

tff(c_418,plain,(
    ! [C_78] : ~ r2_hidden(C_78,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_404])).

tff(c_1446,plain,(
    ! [D_120,A_121,B_122] :
      ( r2_hidden(D_120,k3_xboole_0(A_121,B_122))
      | ~ r2_hidden(D_120,B_122)
      | ~ r2_hidden(D_120,A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1483,plain,(
    ! [D_120] :
      ( r2_hidden(D_120,k1_xboole_0)
      | ~ r2_hidden(D_120,'#skF_5')
      | ~ r2_hidden(D_120,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_1446])).

tff(c_1498,plain,(
    ! [D_120] :
      ( ~ r2_hidden(D_120,'#skF_5')
      | ~ r2_hidden(D_120,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_1483])).

tff(c_2733,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_2711,c_1498])).

tff(c_2737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2733])).

tff(c_2740,plain,(
    ! [C_155] : ~ r2_hidden(C_155,k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_2776,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_2740])).

tff(c_2783,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2776,c_26])).

tff(c_68,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(B_38,A_39)
      | ~ r1_xboole_0(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_68])).

tff(c_1129,plain,(
    ! [A_107,C_108,B_109] :
      ( ~ r1_xboole_0(A_107,C_108)
      | ~ r1_xboole_0(A_107,B_109)
      | r1_xboole_0(A_107,k2_xboole_0(B_109,C_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16285,plain,(
    ! [B_351,C_352,A_353] :
      ( r1_xboole_0(k2_xboole_0(B_351,C_352),A_353)
      | ~ r1_xboole_0(A_353,C_352)
      | ~ r1_xboole_0(A_353,B_351) ) ),
    inference(resolution,[status(thm)],[c_1129,c_26])).

tff(c_52,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16306,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_16285,c_52])).

tff(c_16316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2783,c_71,c_16306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:53:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.31/3.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/3.03  
% 8.31/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/3.03  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 8.31/3.03  
% 8.31/3.03  %Foreground sorts:
% 8.31/3.03  
% 8.31/3.03  
% 8.31/3.03  %Background operators:
% 8.31/3.03  
% 8.31/3.03  
% 8.31/3.03  %Foreground operators:
% 8.31/3.03  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.31/3.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.31/3.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.31/3.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.31/3.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.31/3.03  tff('#skF_7', type, '#skF_7': $i).
% 8.31/3.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.31/3.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.31/3.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.31/3.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.31/3.03  tff('#skF_5', type, '#skF_5': $i).
% 8.31/3.03  tff('#skF_6', type, '#skF_6': $i).
% 8.31/3.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.31/3.03  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.31/3.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.31/3.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.31/3.03  tff('#skF_4', type, '#skF_4': $i).
% 8.31/3.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.31/3.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.31/3.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.31/3.03  
% 8.31/3.04  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.31/3.04  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 8.31/3.04  tff(f_97, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 8.31/3.04  tff(f_44, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.31/3.04  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.31/3.04  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.31/3.04  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.31/3.04  tff(f_80, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 8.31/3.04  tff(c_28, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), k3_xboole_0(A_13, B_14)) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.31/3.04  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.31/3.04  tff(c_155, plain, (![A_46, B_47]: (r1_xboole_0(k1_tarski(A_46), B_47) | r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.31/3.04  tff(c_26, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.31/3.04  tff(c_162, plain, (![B_47, A_46]: (r1_xboole_0(B_47, k1_tarski(A_46)) | r2_hidden(A_46, B_47))), inference(resolution, [status(thm)], [c_155, c_26])).
% 8.31/3.04  tff(c_58, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.31/3.04  tff(c_163, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.31/3.04  tff(c_167, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_163])).
% 8.31/3.04  tff(c_389, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.31/3.04  tff(c_398, plain, (![C_78]: (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7')) | ~r2_hidden(C_78, k3_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_167, c_389])).
% 8.31/3.04  tff(c_2646, plain, (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_398])).
% 8.31/3.04  tff(c_2662, plain, (r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_162, c_2646])).
% 8.31/3.04  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.31/3.04  tff(c_2711, plain, (r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_2662, c_6])).
% 8.31/3.04  tff(c_54, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.31/3.04  tff(c_118, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.31/3.04  tff(c_130, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_118])).
% 8.31/3.04  tff(c_404, plain, (![C_78]: (~r1_xboole_0('#skF_6', '#skF_5') | ~r2_hidden(C_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_130, c_389])).
% 8.31/3.04  tff(c_418, plain, (![C_78]: (~r2_hidden(C_78, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_404])).
% 8.31/3.04  tff(c_1446, plain, (![D_120, A_121, B_122]: (r2_hidden(D_120, k3_xboole_0(A_121, B_122)) | ~r2_hidden(D_120, B_122) | ~r2_hidden(D_120, A_121))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.31/3.04  tff(c_1483, plain, (![D_120]: (r2_hidden(D_120, k1_xboole_0) | ~r2_hidden(D_120, '#skF_5') | ~r2_hidden(D_120, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_1446])).
% 8.31/3.04  tff(c_1498, plain, (![D_120]: (~r2_hidden(D_120, '#skF_5') | ~r2_hidden(D_120, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_418, c_1483])).
% 8.31/3.04  tff(c_2733, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_2711, c_1498])).
% 8.31/3.04  tff(c_2737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_2733])).
% 8.31/3.04  tff(c_2740, plain, (![C_155]: (~r2_hidden(C_155, k3_xboole_0('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_398])).
% 8.31/3.04  tff(c_2776, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_2740])).
% 8.31/3.04  tff(c_2783, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2776, c_26])).
% 8.31/3.04  tff(c_68, plain, (![B_38, A_39]: (r1_xboole_0(B_38, A_39) | ~r1_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.31/3.04  tff(c_71, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_68])).
% 8.31/3.04  tff(c_1129, plain, (![A_107, C_108, B_109]: (~r1_xboole_0(A_107, C_108) | ~r1_xboole_0(A_107, B_109) | r1_xboole_0(A_107, k2_xboole_0(B_109, C_108)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.31/3.04  tff(c_16285, plain, (![B_351, C_352, A_353]: (r1_xboole_0(k2_xboole_0(B_351, C_352), A_353) | ~r1_xboole_0(A_353, C_352) | ~r1_xboole_0(A_353, B_351))), inference(resolution, [status(thm)], [c_1129, c_26])).
% 8.31/3.04  tff(c_52, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.31/3.04  tff(c_16306, plain, (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_16285, c_52])).
% 8.31/3.04  tff(c_16316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2783, c_71, c_16306])).
% 8.31/3.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/3.04  
% 8.31/3.04  Inference rules
% 8.31/3.04  ----------------------
% 8.31/3.04  #Ref     : 0
% 8.31/3.04  #Sup     : 4007
% 8.31/3.04  #Fact    : 0
% 8.31/3.04  #Define  : 0
% 8.31/3.04  #Split   : 6
% 8.31/3.04  #Chain   : 0
% 8.31/3.04  #Close   : 0
% 8.31/3.04  
% 8.31/3.04  Ordering : KBO
% 8.31/3.04  
% 8.31/3.04  Simplification rules
% 8.31/3.04  ----------------------
% 8.31/3.04  #Subsume      : 413
% 8.31/3.04  #Demod        : 3364
% 8.31/3.04  #Tautology    : 2605
% 8.31/3.04  #SimpNegUnit  : 136
% 8.31/3.04  #BackRed      : 6
% 8.31/3.04  
% 8.31/3.04  #Partial instantiations: 0
% 8.31/3.04  #Strategies tried      : 1
% 8.31/3.04  
% 8.31/3.04  Timing (in seconds)
% 8.31/3.04  ----------------------
% 8.31/3.05  Preprocessing        : 0.33
% 8.31/3.05  Parsing              : 0.18
% 8.31/3.05  CNF conversion       : 0.02
% 8.31/3.05  Main loop            : 1.87
% 8.31/3.05  Inferencing          : 0.45
% 8.31/3.05  Reduction            : 0.94
% 8.31/3.05  Demodulation         : 0.78
% 8.31/3.05  BG Simplification    : 0.05
% 8.31/3.05  Subsumption          : 0.34
% 8.31/3.05  Abstraction          : 0.06
% 8.31/3.05  MUC search           : 0.00
% 8.31/3.05  Cooper               : 0.00
% 8.31/3.05  Total                : 2.23
% 8.31/3.05  Index Insertion      : 0.00
% 8.55/3.05  Index Deletion       : 0.00
% 8.55/3.05  Index Matching       : 0.00
% 8.55/3.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
