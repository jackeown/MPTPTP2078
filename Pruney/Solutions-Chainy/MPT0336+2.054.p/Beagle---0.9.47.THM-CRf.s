%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:07 EST 2020

% Result     : Theorem 4.22s
% Output     : CNFRefutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 114 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 175 expanded)
%              Number of equality atoms :   31 (  60 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_122,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_42] : k3_xboole_0(A_42,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_122])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_144,plain,(
    ! [A_42] : k3_xboole_0(k1_xboole_0,A_42) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_2])).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_133,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_122])).

tff(c_430,plain,(
    ! [A_70,B_71,C_72] : k3_xboole_0(k3_xboole_0(A_70,B_71),C_72) = k3_xboole_0(A_70,k3_xboole_0(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_494,plain,(
    ! [C_72] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',C_72)) = k3_xboole_0(k1_xboole_0,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_430])).

tff(c_522,plain,(
    ! [C_72] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_3',C_72)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_494])).

tff(c_38,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_39,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_193,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_197,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_39,c_193])).

tff(c_207,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_2])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(k1_tarski(A_25),B_26)
      | r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_132,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(k1_tarski(A_25),B_26) = k1_xboole_0
      | r2_hidden(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_28,c_122])).

tff(c_419,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_132])).

tff(c_429,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_262,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,B_55)
      | ~ r2_hidden(C_56,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2103,plain,(
    ! [C_97,B_98,A_99] :
      ( ~ r2_hidden(C_97,B_98)
      | ~ r2_hidden(C_97,A_99)
      | k3_xboole_0(A_99,B_98) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_262])).

tff(c_2119,plain,(
    ! [A_100] :
      ( ~ r2_hidden('#skF_5',A_100)
      | k3_xboole_0(A_100,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_2103])).

tff(c_2125,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_429,c_2119])).

tff(c_2134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_2,c_2125])).

tff(c_2135,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_275,plain,(
    ! [C_57] :
      ( ~ r2_hidden(C_57,'#skF_3')
      | ~ r2_hidden(C_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_262])).

tff(c_345,plain,(
    ! [B_62] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_62),'#skF_4')
      | r1_xboole_0('#skF_3',B_62) ) ),
    inference(resolution,[status(thm)],[c_12,c_275])).

tff(c_350,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_345])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_357,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_350,c_4])).

tff(c_2274,plain,(
    ! [A_105,B_106,C_107] :
      ( k3_xboole_0(A_105,k2_xboole_0(B_106,C_107)) = k3_xboole_0(A_105,C_107)
      | ~ r1_xboole_0(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_217,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(A_46,B_47)
      | k3_xboole_0(A_46,B_47) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_223,plain,(
    k3_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_217,c_32])).

tff(c_226,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_223])).

tff(c_2295,plain,
    ( k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2274,c_226])).

tff(c_2337,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_2295])).

tff(c_2346,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2337])).

tff(c_2350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2135,c_2346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:33:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.22/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.22/1.81  
% 4.22/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.22/1.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.22/1.81  
% 4.22/1.81  %Foreground sorts:
% 4.22/1.81  
% 4.22/1.81  
% 4.22/1.81  %Background operators:
% 4.22/1.81  
% 4.22/1.81  
% 4.22/1.81  %Foreground operators:
% 4.22/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.22/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.22/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.22/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.22/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.22/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.22/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.22/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.22/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.22/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.22/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.22/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.22/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.22/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.22/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.22/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.22/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.22/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.22/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.22/1.81  
% 4.22/1.83  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.22/1.83  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.22/1.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.22/1.83  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.22/1.83  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.22/1.83  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.22/1.83  tff(f_72, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.22/1.83  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.22/1.83  tff(f_61, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 4.22/1.83  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.22/1.83  tff(c_122, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.22/1.83  tff(c_139, plain, (![A_42]: (k3_xboole_0(A_42, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_122])).
% 4.22/1.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.22/1.83  tff(c_144, plain, (![A_42]: (k3_xboole_0(k1_xboole_0, A_42)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_139, c_2])).
% 4.22/1.83  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.22/1.83  tff(c_133, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_122])).
% 4.22/1.83  tff(c_430, plain, (![A_70, B_71, C_72]: (k3_xboole_0(k3_xboole_0(A_70, B_71), C_72)=k3_xboole_0(A_70, k3_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.22/1.83  tff(c_494, plain, (![C_72]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', C_72))=k3_xboole_0(k1_xboole_0, C_72))), inference(superposition, [status(thm), theory('equality')], [c_133, c_430])).
% 4.22/1.83  tff(c_522, plain, (![C_72]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', C_72))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_494])).
% 4.22/1.83  tff(c_38, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.22/1.83  tff(c_39, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 4.22/1.83  tff(c_193, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.22/1.83  tff(c_197, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_39, c_193])).
% 4.22/1.83  tff(c_207, plain, (k3_xboole_0(k1_tarski('#skF_5'), k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_197, c_2])).
% 4.22/1.83  tff(c_28, plain, (![A_25, B_26]: (r1_xboole_0(k1_tarski(A_25), B_26) | r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.22/1.83  tff(c_132, plain, (![A_25, B_26]: (k3_xboole_0(k1_tarski(A_25), B_26)=k1_xboole_0 | r2_hidden(A_25, B_26))), inference(resolution, [status(thm)], [c_28, c_122])).
% 4.22/1.83  tff(c_419, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_132])).
% 4.22/1.83  tff(c_429, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_419])).
% 4.22/1.83  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.22/1.83  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.22/1.83  tff(c_262, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, B_55) | ~r2_hidden(C_56, A_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.22/1.83  tff(c_2103, plain, (![C_97, B_98, A_99]: (~r2_hidden(C_97, B_98) | ~r2_hidden(C_97, A_99) | k3_xboole_0(A_99, B_98)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_262])).
% 4.22/1.83  tff(c_2119, plain, (![A_100]: (~r2_hidden('#skF_5', A_100) | k3_xboole_0(A_100, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_2103])).
% 4.22/1.83  tff(c_2125, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_429, c_2119])).
% 4.22/1.83  tff(c_2134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_522, c_2, c_2125])).
% 4.22/1.83  tff(c_2135, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_419])).
% 4.22/1.83  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.22/1.83  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.22/1.83  tff(c_275, plain, (![C_57]: (~r2_hidden(C_57, '#skF_3') | ~r2_hidden(C_57, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_262])).
% 4.22/1.83  tff(c_345, plain, (![B_62]: (~r2_hidden('#skF_1'('#skF_3', B_62), '#skF_4') | r1_xboole_0('#skF_3', B_62))), inference(resolution, [status(thm)], [c_12, c_275])).
% 4.22/1.83  tff(c_350, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_345])).
% 4.22/1.83  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.22/1.83  tff(c_357, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_350, c_4])).
% 4.22/1.83  tff(c_2274, plain, (![A_105, B_106, C_107]: (k3_xboole_0(A_105, k2_xboole_0(B_106, C_107))=k3_xboole_0(A_105, C_107) | ~r1_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.22/1.83  tff(c_217, plain, (![A_46, B_47]: (r1_xboole_0(A_46, B_47) | k3_xboole_0(A_46, B_47)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.22/1.83  tff(c_32, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.22/1.83  tff(c_223, plain, (k3_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_217, c_32])).
% 4.22/1.83  tff(c_226, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_223])).
% 4.22/1.83  tff(c_2295, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0 | ~r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2274, c_226])).
% 4.22/1.83  tff(c_2337, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_2295])).
% 4.22/1.83  tff(c_2346, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_2337])).
% 4.22/1.83  tff(c_2350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2135, c_2346])).
% 4.22/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.22/1.83  
% 4.22/1.83  Inference rules
% 4.22/1.83  ----------------------
% 4.22/1.83  #Ref     : 0
% 4.22/1.83  #Sup     : 574
% 4.22/1.83  #Fact    : 0
% 4.22/1.83  #Define  : 0
% 4.22/1.83  #Split   : 2
% 4.22/1.83  #Chain   : 0
% 4.22/1.83  #Close   : 0
% 4.22/1.83  
% 4.22/1.83  Ordering : KBO
% 4.22/1.83  
% 4.22/1.83  Simplification rules
% 4.22/1.83  ----------------------
% 4.22/1.83  #Subsume      : 13
% 4.22/1.83  #Demod        : 495
% 4.22/1.83  #Tautology    : 358
% 4.22/1.83  #SimpNegUnit  : 3
% 4.22/1.83  #BackRed      : 3
% 4.22/1.83  
% 4.22/1.83  #Partial instantiations: 0
% 4.22/1.83  #Strategies tried      : 1
% 4.22/1.83  
% 4.22/1.83  Timing (in seconds)
% 4.22/1.83  ----------------------
% 4.22/1.83  Preprocessing        : 0.32
% 4.22/1.83  Parsing              : 0.17
% 4.22/1.83  CNF conversion       : 0.02
% 4.22/1.83  Main loop            : 0.67
% 4.22/1.83  Inferencing          : 0.20
% 4.22/1.83  Reduction            : 0.33
% 4.22/1.83  Demodulation         : 0.28
% 4.22/1.83  BG Simplification    : 0.02
% 4.22/1.83  Subsumption          : 0.09
% 4.22/1.83  Abstraction          : 0.03
% 4.22/1.83  MUC search           : 0.00
% 4.22/1.83  Cooper               : 0.00
% 4.22/1.83  Total                : 1.03
% 4.22/1.83  Index Insertion      : 0.00
% 4.22/1.83  Index Deletion       : 0.00
% 4.22/1.83  Index Matching       : 0.00
% 4.22/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
