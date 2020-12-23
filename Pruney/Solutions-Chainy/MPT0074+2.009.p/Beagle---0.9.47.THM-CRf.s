%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:27 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 128 expanded)
%              Number of equality atoms :   28 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_427,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r2_hidden('#skF_1'(A_83,B_84,C_85),B_84)
      | r2_hidden('#skF_2'(A_83,B_84,C_85),C_85)
      | k4_xboole_0(A_83,B_84) = C_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_436,plain,(
    ! [A_86,C_87] :
      ( r2_hidden('#skF_2'(A_86,A_86,C_87),C_87)
      | k4_xboole_0(A_86,A_86) = C_87 ) ),
    inference(resolution,[status(thm)],[c_18,c_427])).

tff(c_24,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_466,plain,(
    ! [A_88,B_89,A_90] :
      ( ~ r1_xboole_0(A_88,B_89)
      | k4_xboole_0(A_90,A_90) = k3_xboole_0(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_436,c_24])).

tff(c_472,plain,(
    ! [A_91] : k4_xboole_0(A_91,A_91) = k3_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_466])).

tff(c_296,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_1'(A_75,B_76,C_77),A_75)
      | r2_hidden('#skF_2'(A_75,B_76,C_77),C_77)
      | k4_xboole_0(A_75,B_76) = C_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_347,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_2'(A_75,B_76,A_75),A_75)
      | k4_xboole_0(A_75,B_76) = A_75 ) ),
    inference(resolution,[status(thm)],[c_296,c_14])).

tff(c_357,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_2'(A_78,B_79,A_78),A_78)
      | k4_xboole_0(A_78,B_79) = A_78 ) ),
    inference(resolution,[status(thm)],[c_296,c_14])).

tff(c_32,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,(
    ! [D_38,B_39,A_40] :
      ( ~ r2_hidden(D_38,B_39)
      | ~ r2_hidden(D_38,k4_xboole_0(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [D_38,A_24] :
      ( ~ r2_hidden(D_38,k1_xboole_0)
      | ~ r2_hidden(D_38,A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_71])).

tff(c_387,plain,(
    ! [B_80,A_81] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_80,k1_xboole_0),A_81)
      | k4_xboole_0(k1_xboole_0,B_80) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_357,c_74])).

tff(c_398,plain,(
    ! [B_76] : k4_xboole_0(k1_xboole_0,B_76) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_347,c_387])).

tff(c_477,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_398])).

tff(c_30,plain,(
    ! [A_20,C_22,B_21,D_23] :
      ( r1_tarski(k3_xboole_0(A_20,C_22),k3_xboole_0(B_21,D_23))
      | ~ r1_tarski(C_22,D_23)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_93,plain,(
    ! [A_48,B_49,C_50] : k3_xboole_0(k2_xboole_0(A_48,B_49),k2_xboole_0(A_48,C_50)) = k2_xboole_0(A_48,k3_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_121,plain,(
    ! [A_55,C_56] : k3_xboole_0(A_55,k2_xboole_0(A_55,C_56)) = k2_xboole_0(A_55,k3_xboole_0(A_55,C_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_93])).

tff(c_145,plain,(
    ! [A_57] : k2_xboole_0(A_57,k3_xboole_0(A_57,A_57)) = k3_xboole_0(A_57,A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_121])).

tff(c_26,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_tarski(A_14,C_16)
      | ~ r1_tarski(k2_xboole_0(A_14,B_15),C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_171,plain,(
    ! [A_58,C_59] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(k3_xboole_0(A_58,A_58),C_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_26])).

tff(c_180,plain,(
    ! [C_22,B_21,D_23] :
      ( r1_tarski(C_22,k3_xboole_0(B_21,D_23))
      | ~ r1_tarski(C_22,D_23)
      | ~ r1_tarski(C_22,B_21) ) ),
    inference(resolution,[status(thm)],[c_30,c_171])).

tff(c_707,plain,(
    ! [C_104] :
      ( r1_tarski(C_104,k1_xboole_0)
      | ~ r1_tarski(C_104,'#skF_6')
      | ~ r1_tarski(C_104,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_180])).

tff(c_34,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_722,plain,(
    ! [C_105] :
      ( k1_xboole_0 = C_105
      | ~ r1_tarski(C_105,'#skF_6')
      | ~ r1_tarski(C_105,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_707,c_34])).

tff(c_725,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_722])).

tff(c_728,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_725])).

tff(c_730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_728])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:19:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.37  
% 2.61/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.61/1.37  
% 2.61/1.37  %Foreground sorts:
% 2.61/1.37  
% 2.61/1.37  
% 2.61/1.37  %Background operators:
% 2.61/1.37  
% 2.61/1.37  
% 2.61/1.37  %Foreground operators:
% 2.61/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.61/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.61/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.61/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.37  
% 2.61/1.39  tff(f_78, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.61/1.39  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.61/1.39  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.61/1.39  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.61/1.39  tff(f_63, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 2.61/1.39  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.61/1.39  tff(f_57, axiom, (![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 2.61/1.39  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.61/1.39  tff(f_69, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.61/1.39  tff(c_36, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.39  tff(c_40, plain, (r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.39  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.39  tff(c_38, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.39  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.39  tff(c_427, plain, (![A_83, B_84, C_85]: (~r2_hidden('#skF_1'(A_83, B_84, C_85), B_84) | r2_hidden('#skF_2'(A_83, B_84, C_85), C_85) | k4_xboole_0(A_83, B_84)=C_85)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.39  tff(c_436, plain, (![A_86, C_87]: (r2_hidden('#skF_2'(A_86, A_86, C_87), C_87) | k4_xboole_0(A_86, A_86)=C_87)), inference(resolution, [status(thm)], [c_18, c_427])).
% 2.61/1.39  tff(c_24, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.61/1.39  tff(c_466, plain, (![A_88, B_89, A_90]: (~r1_xboole_0(A_88, B_89) | k4_xboole_0(A_90, A_90)=k3_xboole_0(A_88, B_89))), inference(resolution, [status(thm)], [c_436, c_24])).
% 2.61/1.39  tff(c_472, plain, (![A_91]: (k4_xboole_0(A_91, A_91)=k3_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_466])).
% 2.61/1.39  tff(c_296, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_1'(A_75, B_76, C_77), A_75) | r2_hidden('#skF_2'(A_75, B_76, C_77), C_77) | k4_xboole_0(A_75, B_76)=C_77)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.39  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.39  tff(c_347, plain, (![A_75, B_76]: (r2_hidden('#skF_2'(A_75, B_76, A_75), A_75) | k4_xboole_0(A_75, B_76)=A_75)), inference(resolution, [status(thm)], [c_296, c_14])).
% 2.61/1.39  tff(c_357, plain, (![A_78, B_79]: (r2_hidden('#skF_2'(A_78, B_79, A_78), A_78) | k4_xboole_0(A_78, B_79)=A_78)), inference(resolution, [status(thm)], [c_296, c_14])).
% 2.61/1.39  tff(c_32, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.61/1.39  tff(c_71, plain, (![D_38, B_39, A_40]: (~r2_hidden(D_38, B_39) | ~r2_hidden(D_38, k4_xboole_0(A_40, B_39)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.39  tff(c_74, plain, (![D_38, A_24]: (~r2_hidden(D_38, k1_xboole_0) | ~r2_hidden(D_38, A_24))), inference(superposition, [status(thm), theory('equality')], [c_32, c_71])).
% 2.61/1.39  tff(c_387, plain, (![B_80, A_81]: (~r2_hidden('#skF_2'(k1_xboole_0, B_80, k1_xboole_0), A_81) | k4_xboole_0(k1_xboole_0, B_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_357, c_74])).
% 2.61/1.39  tff(c_398, plain, (![B_76]: (k4_xboole_0(k1_xboole_0, B_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_347, c_387])).
% 2.61/1.39  tff(c_477, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_472, c_398])).
% 2.61/1.39  tff(c_30, plain, (![A_20, C_22, B_21, D_23]: (r1_tarski(k3_xboole_0(A_20, C_22), k3_xboole_0(B_21, D_23)) | ~r1_tarski(C_22, D_23) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.39  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.39  tff(c_93, plain, (![A_48, B_49, C_50]: (k3_xboole_0(k2_xboole_0(A_48, B_49), k2_xboole_0(A_48, C_50))=k2_xboole_0(A_48, k3_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.39  tff(c_121, plain, (![A_55, C_56]: (k3_xboole_0(A_55, k2_xboole_0(A_55, C_56))=k2_xboole_0(A_55, k3_xboole_0(A_55, C_56)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_93])).
% 2.61/1.39  tff(c_145, plain, (![A_57]: (k2_xboole_0(A_57, k3_xboole_0(A_57, A_57))=k3_xboole_0(A_57, A_57))), inference(superposition, [status(thm), theory('equality')], [c_20, c_121])).
% 2.61/1.39  tff(c_26, plain, (![A_14, C_16, B_15]: (r1_tarski(A_14, C_16) | ~r1_tarski(k2_xboole_0(A_14, B_15), C_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.39  tff(c_171, plain, (![A_58, C_59]: (r1_tarski(A_58, C_59) | ~r1_tarski(k3_xboole_0(A_58, A_58), C_59))), inference(superposition, [status(thm), theory('equality')], [c_145, c_26])).
% 2.61/1.39  tff(c_180, plain, (![C_22, B_21, D_23]: (r1_tarski(C_22, k3_xboole_0(B_21, D_23)) | ~r1_tarski(C_22, D_23) | ~r1_tarski(C_22, B_21))), inference(resolution, [status(thm)], [c_30, c_171])).
% 2.61/1.39  tff(c_707, plain, (![C_104]: (r1_tarski(C_104, k1_xboole_0) | ~r1_tarski(C_104, '#skF_6') | ~r1_tarski(C_104, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_477, c_180])).
% 2.61/1.39  tff(c_34, plain, (![A_25]: (k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.61/1.39  tff(c_722, plain, (![C_105]: (k1_xboole_0=C_105 | ~r1_tarski(C_105, '#skF_6') | ~r1_tarski(C_105, '#skF_5'))), inference(resolution, [status(thm)], [c_707, c_34])).
% 2.61/1.39  tff(c_725, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_722])).
% 2.61/1.39  tff(c_728, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_725])).
% 2.61/1.39  tff(c_730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_728])).
% 2.61/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.39  
% 2.61/1.39  Inference rules
% 2.61/1.39  ----------------------
% 2.61/1.39  #Ref     : 0
% 2.61/1.39  #Sup     : 158
% 2.61/1.39  #Fact    : 0
% 2.61/1.39  #Define  : 0
% 2.61/1.39  #Split   : 0
% 2.61/1.39  #Chain   : 0
% 2.61/1.39  #Close   : 0
% 2.61/1.39  
% 2.61/1.39  Ordering : KBO
% 2.61/1.39  
% 2.61/1.39  Simplification rules
% 2.61/1.39  ----------------------
% 2.61/1.39  #Subsume      : 17
% 2.61/1.39  #Demod        : 26
% 2.61/1.39  #Tautology    : 48
% 2.61/1.39  #SimpNegUnit  : 2
% 2.61/1.39  #BackRed      : 3
% 2.61/1.39  
% 2.61/1.39  #Partial instantiations: 0
% 2.61/1.39  #Strategies tried      : 1
% 2.61/1.39  
% 2.61/1.39  Timing (in seconds)
% 2.61/1.39  ----------------------
% 2.61/1.39  Preprocessing        : 0.28
% 2.61/1.39  Parsing              : 0.15
% 2.61/1.39  CNF conversion       : 0.02
% 2.61/1.39  Main loop            : 0.30
% 2.61/1.39  Inferencing          : 0.12
% 2.61/1.39  Reduction            : 0.08
% 2.61/1.39  Demodulation         : 0.06
% 2.61/1.39  BG Simplification    : 0.02
% 2.61/1.39  Subsumption          : 0.06
% 2.61/1.39  Abstraction          : 0.02
% 2.61/1.39  MUC search           : 0.00
% 2.61/1.39  Cooper               : 0.00
% 2.61/1.39  Total                : 0.61
% 2.61/1.39  Index Insertion      : 0.00
% 2.61/1.39  Index Deletion       : 0.00
% 2.61/1.39  Index Matching       : 0.00
% 2.61/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
