%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:08 EST 2020

% Result     : Theorem 6.97s
% Output     : CNFRefutation 6.97s
% Verified   : 
% Statistics : Number of formulae       :   71 (  98 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 152 expanded)
%              Number of equality atoms :   26 (  40 expanded)
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

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_57,axiom,(
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

tff(c_222,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_231,plain,(
    ! [A_58,B_59] : r1_tarski(k3_xboole_0(A_58,B_59),A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_18])).

tff(c_40,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(B_35,A_36)
      | ~ r1_xboole_0(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_944,plain,(
    ! [A_97,C_98,B_99] :
      ( r1_xboole_0(A_97,C_98)
      | ~ r1_xboole_0(B_99,C_98)
      | ~ r1_tarski(A_97,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_981,plain,(
    ! [A_101] :
      ( r1_xboole_0(A_101,'#skF_4')
      | ~ r1_tarski(A_101,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_59,c_944])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1741,plain,(
    ! [A_135] :
      ( k3_xboole_0(A_135,'#skF_4') = k1_xboole_0
      | ~ r1_tarski(A_135,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_981,c_4])).

tff(c_2002,plain,(
    ! [B_143] : k3_xboole_0(k3_xboole_0('#skF_3',B_143),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_231,c_1741])).

tff(c_130,plain,(
    ! [A_41,B_42] :
      ( r1_xboole_0(A_41,B_42)
      | k3_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [B_51,A_52] :
      ( r1_xboole_0(B_51,A_52)
      | k3_xboole_0(A_52,B_51) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_130,c_8])).

tff(c_186,plain,(
    ! [B_51,A_52] :
      ( k3_xboole_0(B_51,A_52) = k1_xboole_0
      | k3_xboole_0(A_52,B_51) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_177,c_4])).

tff(c_2085,plain,(
    ! [B_143] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',B_143)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2002,c_186])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_140,plain,(
    ! [B_42,A_41] :
      ( r1_xboole_0(B_42,A_41)
      | k3_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_130,c_8])).

tff(c_1167,plain,(
    ! [A_108,C_109,B_110] :
      ( ~ r1_xboole_0(A_108,C_109)
      | ~ r1_xboole_0(A_108,B_110)
      | r1_xboole_0(A_108,k2_xboole_0(B_110,C_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3454,plain,(
    ! [B_175,C_176,A_177] :
      ( r1_xboole_0(k2_xboole_0(B_175,C_176),A_177)
      | ~ r1_xboole_0(A_177,C_176)
      | ~ r1_xboole_0(A_177,B_175) ) ),
    inference(resolution,[status(thm)],[c_1167,c_8])).

tff(c_38,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3474,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3454,c_38])).

tff(c_3483,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_3474])).

tff(c_3489,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_140,c_3483])).

tff(c_3495,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3489])).

tff(c_143,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(k1_tarski(A_43),B_44)
      | r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_679,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(k1_tarski(A_80),B_81) = k1_xboole_0
      | r2_hidden(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_143,c_4])).

tff(c_783,plain,(
    ! [B_91,A_92] :
      ( k3_xboole_0(B_91,k1_tarski(A_92)) = k1_xboole_0
      | r2_hidden(A_92,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_679])).

tff(c_44,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_45,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_151,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_45,c_151])).

tff(c_815,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_158])).

tff(c_9459,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_3495,c_815])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_726,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r1_xboole_0(A_82,B_83)
      | ~ r2_hidden(C_84,B_83)
      | ~ r2_hidden(C_84,A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2926,plain,(
    ! [C_159,B_160,A_161] :
      ( ~ r2_hidden(C_159,B_160)
      | ~ r2_hidden(C_159,A_161)
      | k3_xboole_0(A_161,B_160) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_726])).

tff(c_2947,plain,(
    ! [A_161] :
      ( ~ r2_hidden('#skF_5',A_161)
      | k3_xboole_0(A_161,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_2926])).

tff(c_9464,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9459,c_2947])).

tff(c_9471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2085,c_2,c_9464])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.97/2.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.97/2.45  
% 6.97/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.97/2.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.97/2.45  
% 6.97/2.45  %Foreground sorts:
% 6.97/2.45  
% 6.97/2.45  
% 6.97/2.45  %Background operators:
% 6.97/2.45  
% 6.97/2.45  
% 6.97/2.45  %Foreground operators:
% 6.97/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.97/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.97/2.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.97/2.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.97/2.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.97/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.97/2.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.97/2.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.97/2.45  tff('#skF_5', type, '#skF_5': $i).
% 6.97/2.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.97/2.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.97/2.45  tff('#skF_2', type, '#skF_2': $i).
% 6.97/2.45  tff('#skF_3', type, '#skF_3': $i).
% 6.97/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.97/2.45  tff('#skF_4', type, '#skF_4': $i).
% 6.97/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.97/2.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.97/2.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.97/2.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.97/2.45  
% 6.97/2.47  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.97/2.47  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.97/2.47  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 6.97/2.47  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.97/2.47  tff(f_67, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 6.97/2.47  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.97/2.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.97/2.47  tff(f_83, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.97/2.47  tff(f_94, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.97/2.47  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.97/2.47  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.97/2.47  tff(c_222, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.97/2.47  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.97/2.47  tff(c_231, plain, (![A_58, B_59]: (r1_tarski(k3_xboole_0(A_58, B_59), A_58))), inference(superposition, [status(thm), theory('equality')], [c_222, c_18])).
% 6.97/2.47  tff(c_40, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.97/2.47  tff(c_56, plain, (![B_35, A_36]: (r1_xboole_0(B_35, A_36) | ~r1_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.97/2.47  tff(c_59, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_56])).
% 6.97/2.47  tff(c_944, plain, (![A_97, C_98, B_99]: (r1_xboole_0(A_97, C_98) | ~r1_xboole_0(B_99, C_98) | ~r1_tarski(A_97, B_99))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.97/2.47  tff(c_981, plain, (![A_101]: (r1_xboole_0(A_101, '#skF_4') | ~r1_tarski(A_101, '#skF_3'))), inference(resolution, [status(thm)], [c_59, c_944])).
% 6.97/2.47  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.97/2.47  tff(c_1741, plain, (![A_135]: (k3_xboole_0(A_135, '#skF_4')=k1_xboole_0 | ~r1_tarski(A_135, '#skF_3'))), inference(resolution, [status(thm)], [c_981, c_4])).
% 6.97/2.47  tff(c_2002, plain, (![B_143]: (k3_xboole_0(k3_xboole_0('#skF_3', B_143), '#skF_4')=k1_xboole_0)), inference(resolution, [status(thm)], [c_231, c_1741])).
% 6.97/2.47  tff(c_130, plain, (![A_41, B_42]: (r1_xboole_0(A_41, B_42) | k3_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.97/2.47  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.97/2.47  tff(c_177, plain, (![B_51, A_52]: (r1_xboole_0(B_51, A_52) | k3_xboole_0(A_52, B_51)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_8])).
% 6.97/2.47  tff(c_186, plain, (![B_51, A_52]: (k3_xboole_0(B_51, A_52)=k1_xboole_0 | k3_xboole_0(A_52, B_51)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_177, c_4])).
% 6.97/2.47  tff(c_2085, plain, (![B_143]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', B_143))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2002, c_186])).
% 6.97/2.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.97/2.47  tff(c_140, plain, (![B_42, A_41]: (r1_xboole_0(B_42, A_41) | k3_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_8])).
% 6.97/2.47  tff(c_1167, plain, (![A_108, C_109, B_110]: (~r1_xboole_0(A_108, C_109) | ~r1_xboole_0(A_108, B_110) | r1_xboole_0(A_108, k2_xboole_0(B_110, C_109)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.97/2.47  tff(c_3454, plain, (![B_175, C_176, A_177]: (r1_xboole_0(k2_xboole_0(B_175, C_176), A_177) | ~r1_xboole_0(A_177, C_176) | ~r1_xboole_0(A_177, B_175))), inference(resolution, [status(thm)], [c_1167, c_8])).
% 6.97/2.47  tff(c_38, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.97/2.47  tff(c_3474, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3454, c_38])).
% 6.97/2.47  tff(c_3483, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_3474])).
% 6.97/2.47  tff(c_3489, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_140, c_3483])).
% 6.97/2.47  tff(c_3495, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3489])).
% 6.97/2.47  tff(c_143, plain, (![A_43, B_44]: (r1_xboole_0(k1_tarski(A_43), B_44) | r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.97/2.47  tff(c_679, plain, (![A_80, B_81]: (k3_xboole_0(k1_tarski(A_80), B_81)=k1_xboole_0 | r2_hidden(A_80, B_81))), inference(resolution, [status(thm)], [c_143, c_4])).
% 6.97/2.47  tff(c_783, plain, (![B_91, A_92]: (k3_xboole_0(B_91, k1_tarski(A_92))=k1_xboole_0 | r2_hidden(A_92, B_91))), inference(superposition, [status(thm), theory('equality')], [c_2, c_679])).
% 6.97/2.47  tff(c_44, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.97/2.47  tff(c_45, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 6.97/2.47  tff(c_151, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.97/2.47  tff(c_158, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_45, c_151])).
% 6.97/2.47  tff(c_815, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_783, c_158])).
% 6.97/2.47  tff(c_9459, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_3495, c_815])).
% 6.97/2.47  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.97/2.47  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.97/2.47  tff(c_726, plain, (![A_82, B_83, C_84]: (~r1_xboole_0(A_82, B_83) | ~r2_hidden(C_84, B_83) | ~r2_hidden(C_84, A_82))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.97/2.47  tff(c_2926, plain, (![C_159, B_160, A_161]: (~r2_hidden(C_159, B_160) | ~r2_hidden(C_159, A_161) | k3_xboole_0(A_161, B_160)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_726])).
% 6.97/2.47  tff(c_2947, plain, (![A_161]: (~r2_hidden('#skF_5', A_161) | k3_xboole_0(A_161, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_2926])).
% 6.97/2.47  tff(c_9464, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_9459, c_2947])).
% 6.97/2.47  tff(c_9471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2085, c_2, c_9464])).
% 6.97/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.97/2.47  
% 6.97/2.47  Inference rules
% 6.97/2.47  ----------------------
% 6.97/2.47  #Ref     : 0
% 6.97/2.47  #Sup     : 2363
% 6.97/2.47  #Fact    : 0
% 6.97/2.47  #Define  : 0
% 6.97/2.47  #Split   : 4
% 6.97/2.47  #Chain   : 0
% 6.97/2.47  #Close   : 0
% 6.97/2.47  
% 6.97/2.47  Ordering : KBO
% 6.97/2.47  
% 6.97/2.47  Simplification rules
% 6.97/2.47  ----------------------
% 6.97/2.47  #Subsume      : 162
% 6.97/2.47  #Demod        : 2264
% 6.97/2.47  #Tautology    : 1669
% 6.97/2.47  #SimpNegUnit  : 1
% 6.97/2.47  #BackRed      : 7
% 6.97/2.47  
% 6.97/2.47  #Partial instantiations: 0
% 6.97/2.47  #Strategies tried      : 1
% 6.97/2.47  
% 6.97/2.47  Timing (in seconds)
% 6.97/2.47  ----------------------
% 6.97/2.47  Preprocessing        : 0.30
% 6.97/2.47  Parsing              : 0.16
% 6.97/2.47  CNF conversion       : 0.02
% 6.97/2.47  Main loop            : 1.40
% 6.97/2.47  Inferencing          : 0.38
% 6.97/2.47  Reduction            : 0.63
% 6.97/2.47  Demodulation         : 0.51
% 6.97/2.47  BG Simplification    : 0.04
% 6.97/2.47  Subsumption          : 0.25
% 6.97/2.47  Abstraction          : 0.05
% 6.97/2.47  MUC search           : 0.00
% 6.97/2.47  Cooper               : 0.00
% 6.97/2.47  Total                : 1.74
% 6.97/2.47  Index Insertion      : 0.00
% 6.97/2.47  Index Deletion       : 0.00
% 6.97/2.47  Index Matching       : 0.00
% 6.97/2.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
