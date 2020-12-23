%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:20 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 200 expanded)
%              Number of leaves         :   24 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :   98 ( 356 expanded)
%              Number of equality atoms :   51 ( 173 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

tff(c_42,plain,(
    k1_setfam_1(k1_tarski('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,(
    ! [B_5] : k4_xboole_0(B_5,B_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_66])).

tff(c_26,plain,(
    ! [B_15] : k4_xboole_0(k1_tarski(B_15),k1_tarski(B_15)) != k1_tarski(B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,(
    ! [B_15] : k1_tarski(B_15) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_26])).

tff(c_408,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_93)
      | r2_hidden('#skF_2'(A_92,B_93),A_92)
      | B_93 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [B_36] : k4_xboole_0(B_36,B_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_66])).

tff(c_32,plain,(
    ! [C_18,B_17] : ~ r2_hidden(C_18,k4_xboole_0(B_17,k1_tarski(C_18))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_81,plain,(
    ! [C_18] : ~ r2_hidden(C_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_32])).

tff(c_457,plain,(
    ! [B_94] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_94),B_94)
      | k1_xboole_0 = B_94 ) ),
    inference(resolution,[status(thm)],[c_408,c_81])).

tff(c_104,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(k1_tarski(A_44),k1_tarski(B_45)) = k1_tarski(A_44)
      | B_45 = A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_117,plain,(
    ! [B_45,A_44] :
      ( ~ r2_hidden(B_45,k1_tarski(A_44))
      | B_45 = A_44 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_32])).

tff(c_469,plain,(
    ! [A_44] :
      ( '#skF_1'(k1_xboole_0,k1_tarski(A_44)) = A_44
      | k1_tarski(A_44) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_457,c_117])).

tff(c_487,plain,(
    ! [A_95] : '#skF_1'(k1_xboole_0,k1_tarski(A_95)) = A_95 ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_469])).

tff(c_456,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_93),B_93)
      | k1_xboole_0 = B_93 ) ),
    inference(resolution,[status(thm)],[c_408,c_81])).

tff(c_493,plain,(
    ! [A_95] :
      ( r2_hidden(A_95,k1_tarski(A_95))
      | k1_tarski(A_95) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_456])).

tff(c_503,plain,(
    ! [A_95] : r2_hidden(A_95,k1_tarski(A_95)) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_493])).

tff(c_483,plain,(
    ! [A_44] : '#skF_1'(k1_xboole_0,k1_tarski(A_44)) = A_44 ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_469])).

tff(c_175,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_3'(A_58,B_59),A_58)
      | r1_tarski(B_59,k1_setfam_1(A_58))
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_179,plain,(
    ! [A_44,B_59] :
      ( '#skF_3'(k1_tarski(A_44),B_59) = A_44
      | r1_tarski(B_59,k1_setfam_1(k1_tarski(A_44)))
      | k1_tarski(A_44) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_175,c_117])).

tff(c_250,plain,(
    ! [A_66,B_67] :
      ( '#skF_3'(k1_tarski(A_66),B_67) = A_66
      | r1_tarski(B_67,k1_setfam_1(k1_tarski(A_66))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_179])).

tff(c_153,plain,(
    ! [B_53,C_54,A_55] :
      ( r1_tarski(k1_setfam_1(B_53),C_54)
      | ~ r1_tarski(A_55,C_54)
      | ~ r2_hidden(A_55,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_160,plain,(
    ! [B_56,B_57] :
      ( r1_tarski(k1_setfam_1(B_56),B_57)
      | ~ r2_hidden(B_57,B_56) ) ),
    inference(resolution,[status(thm)],[c_14,c_153])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_173,plain,(
    ! [B_56,B_57] :
      ( k1_setfam_1(B_56) = B_57
      | ~ r1_tarski(B_57,k1_setfam_1(B_56))
      | ~ r2_hidden(B_57,B_56) ) ),
    inference(resolution,[status(thm)],[c_160,c_10])).

tff(c_3522,plain,(
    ! [A_2791,B_2792] :
      ( k1_setfam_1(k1_tarski(A_2791)) = B_2792
      | ~ r2_hidden(B_2792,k1_tarski(A_2791))
      | '#skF_3'(k1_tarski(A_2791),B_2792) = A_2791 ) ),
    inference(resolution,[status(thm)],[c_250,c_173])).

tff(c_3561,plain,(
    ! [A_2791] :
      ( k1_setfam_1(k1_tarski(A_2791)) = '#skF_1'(k1_xboole_0,k1_tarski(A_2791))
      | '#skF_3'(k1_tarski(A_2791),'#skF_1'(k1_xboole_0,k1_tarski(A_2791))) = A_2791
      | k1_tarski(A_2791) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_456,c_3522])).

tff(c_3590,plain,(
    ! [A_2791] :
      ( k1_setfam_1(k1_tarski(A_2791)) = A_2791
      | '#skF_3'(k1_tarski(A_2791),A_2791) = A_2791
      | k1_tarski(A_2791) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_483,c_3561])).

tff(c_3598,plain,(
    ! [A_2793] :
      ( k1_setfam_1(k1_tarski(A_2793)) = A_2793
      | '#skF_3'(k1_tarski(A_2793),A_2793) = A_2793 ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3590])).

tff(c_3688,plain,(
    '#skF_3'(k1_tarski('#skF_4'),'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3598,c_42])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_293,plain,(
    ! [B_71,A_72] :
      ( ~ r1_tarski(B_71,'#skF_3'(A_72,B_71))
      | r1_tarski(B_71,k1_setfam_1(A_72))
      | k1_xboole_0 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_301,plain,(
    ! [A_6,A_72] :
      ( r1_tarski(A_6,k1_setfam_1(A_72))
      | k1_xboole_0 = A_72
      | k4_xboole_0(A_6,'#skF_3'(A_72,A_6)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_293])).

tff(c_3704,plain,
    ( r1_tarski('#skF_4',k1_setfam_1(k1_tarski('#skF_4')))
    | k1_tarski('#skF_4') = k1_xboole_0
    | k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3688,c_301])).

tff(c_3714,plain,
    ( r1_tarski('#skF_4',k1_setfam_1(k1_tarski('#skF_4')))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3704])).

tff(c_3715,plain,(
    r1_tarski('#skF_4',k1_setfam_1(k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_3714])).

tff(c_3724,plain,
    ( k1_setfam_1(k1_tarski('#skF_4')) = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3715,c_173])).

tff(c_3740,plain,(
    k1_setfam_1(k1_tarski('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_3724])).

tff(c_3742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:19:50 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.97  
% 5.01/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.97  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.01/1.97  
% 5.01/1.97  %Foreground sorts:
% 5.01/1.97  
% 5.01/1.97  
% 5.01/1.97  %Background operators:
% 5.01/1.97  
% 5.01/1.97  
% 5.01/1.97  %Foreground operators:
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.01/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.01/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.01/1.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.01/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.01/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.01/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.01/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.01/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.01/1.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.01/1.97  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.01/1.97  
% 5.33/1.99  tff(f_78, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 5.33/1.99  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.33/1.99  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.33/1.99  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 5.33/1.99  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 5.33/1.99  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 5.33/1.99  tff(f_69, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 5.33/1.99  tff(f_75, axiom, (![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 5.33/1.99  tff(c_42, plain, (k1_setfam_1(k1_tarski('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.33/1.99  tff(c_14, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.33/1.99  tff(c_66, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.33/1.99  tff(c_74, plain, (![B_5]: (k4_xboole_0(B_5, B_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_66])).
% 5.33/1.99  tff(c_26, plain, (![B_15]: (k4_xboole_0(k1_tarski(B_15), k1_tarski(B_15))!=k1_tarski(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.33/1.99  tff(c_75, plain, (![B_15]: (k1_tarski(B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_26])).
% 5.33/1.99  tff(c_408, plain, (![A_92, B_93]: (r2_hidden('#skF_1'(A_92, B_93), B_93) | r2_hidden('#skF_2'(A_92, B_93), A_92) | B_93=A_92)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.33/1.99  tff(c_76, plain, (![B_36]: (k4_xboole_0(B_36, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_66])).
% 5.33/1.99  tff(c_32, plain, (![C_18, B_17]: (~r2_hidden(C_18, k4_xboole_0(B_17, k1_tarski(C_18))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.33/1.99  tff(c_81, plain, (![C_18]: (~r2_hidden(C_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_76, c_32])).
% 5.33/1.99  tff(c_457, plain, (![B_94]: (r2_hidden('#skF_1'(k1_xboole_0, B_94), B_94) | k1_xboole_0=B_94)), inference(resolution, [status(thm)], [c_408, c_81])).
% 5.33/1.99  tff(c_104, plain, (![A_44, B_45]: (k4_xboole_0(k1_tarski(A_44), k1_tarski(B_45))=k1_tarski(A_44) | B_45=A_44)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.33/1.99  tff(c_117, plain, (![B_45, A_44]: (~r2_hidden(B_45, k1_tarski(A_44)) | B_45=A_44)), inference(superposition, [status(thm), theory('equality')], [c_104, c_32])).
% 5.33/1.99  tff(c_469, plain, (![A_44]: ('#skF_1'(k1_xboole_0, k1_tarski(A_44))=A_44 | k1_tarski(A_44)=k1_xboole_0)), inference(resolution, [status(thm)], [c_457, c_117])).
% 5.33/1.99  tff(c_487, plain, (![A_95]: ('#skF_1'(k1_xboole_0, k1_tarski(A_95))=A_95)), inference(negUnitSimplification, [status(thm)], [c_75, c_469])).
% 5.33/1.99  tff(c_456, plain, (![B_93]: (r2_hidden('#skF_1'(k1_xboole_0, B_93), B_93) | k1_xboole_0=B_93)), inference(resolution, [status(thm)], [c_408, c_81])).
% 5.33/1.99  tff(c_493, plain, (![A_95]: (r2_hidden(A_95, k1_tarski(A_95)) | k1_tarski(A_95)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_487, c_456])).
% 5.33/1.99  tff(c_503, plain, (![A_95]: (r2_hidden(A_95, k1_tarski(A_95)))), inference(negUnitSimplification, [status(thm)], [c_75, c_493])).
% 5.33/1.99  tff(c_483, plain, (![A_44]: ('#skF_1'(k1_xboole_0, k1_tarski(A_44))=A_44)), inference(negUnitSimplification, [status(thm)], [c_75, c_469])).
% 5.33/1.99  tff(c_175, plain, (![A_58, B_59]: (r2_hidden('#skF_3'(A_58, B_59), A_58) | r1_tarski(B_59, k1_setfam_1(A_58)) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.33/1.99  tff(c_179, plain, (![A_44, B_59]: ('#skF_3'(k1_tarski(A_44), B_59)=A_44 | r1_tarski(B_59, k1_setfam_1(k1_tarski(A_44))) | k1_tarski(A_44)=k1_xboole_0)), inference(resolution, [status(thm)], [c_175, c_117])).
% 5.33/1.99  tff(c_250, plain, (![A_66, B_67]: ('#skF_3'(k1_tarski(A_66), B_67)=A_66 | r1_tarski(B_67, k1_setfam_1(k1_tarski(A_66))))), inference(negUnitSimplification, [status(thm)], [c_75, c_179])).
% 5.33/1.99  tff(c_153, plain, (![B_53, C_54, A_55]: (r1_tarski(k1_setfam_1(B_53), C_54) | ~r1_tarski(A_55, C_54) | ~r2_hidden(A_55, B_53))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.33/1.99  tff(c_160, plain, (![B_56, B_57]: (r1_tarski(k1_setfam_1(B_56), B_57) | ~r2_hidden(B_57, B_56))), inference(resolution, [status(thm)], [c_14, c_153])).
% 5.33/1.99  tff(c_10, plain, (![B_5, A_4]: (B_5=A_4 | ~r1_tarski(B_5, A_4) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.33/1.99  tff(c_173, plain, (![B_56, B_57]: (k1_setfam_1(B_56)=B_57 | ~r1_tarski(B_57, k1_setfam_1(B_56)) | ~r2_hidden(B_57, B_56))), inference(resolution, [status(thm)], [c_160, c_10])).
% 5.33/1.99  tff(c_3522, plain, (![A_2791, B_2792]: (k1_setfam_1(k1_tarski(A_2791))=B_2792 | ~r2_hidden(B_2792, k1_tarski(A_2791)) | '#skF_3'(k1_tarski(A_2791), B_2792)=A_2791)), inference(resolution, [status(thm)], [c_250, c_173])).
% 5.33/1.99  tff(c_3561, plain, (![A_2791]: (k1_setfam_1(k1_tarski(A_2791))='#skF_1'(k1_xboole_0, k1_tarski(A_2791)) | '#skF_3'(k1_tarski(A_2791), '#skF_1'(k1_xboole_0, k1_tarski(A_2791)))=A_2791 | k1_tarski(A_2791)=k1_xboole_0)), inference(resolution, [status(thm)], [c_456, c_3522])).
% 5.33/1.99  tff(c_3590, plain, (![A_2791]: (k1_setfam_1(k1_tarski(A_2791))=A_2791 | '#skF_3'(k1_tarski(A_2791), A_2791)=A_2791 | k1_tarski(A_2791)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_483, c_483, c_3561])).
% 5.33/1.99  tff(c_3598, plain, (![A_2793]: (k1_setfam_1(k1_tarski(A_2793))=A_2793 | '#skF_3'(k1_tarski(A_2793), A_2793)=A_2793)), inference(negUnitSimplification, [status(thm)], [c_75, c_3590])).
% 5.33/1.99  tff(c_3688, plain, ('#skF_3'(k1_tarski('#skF_4'), '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3598, c_42])).
% 5.33/1.99  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.33/1.99  tff(c_293, plain, (![B_71, A_72]: (~r1_tarski(B_71, '#skF_3'(A_72, B_71)) | r1_tarski(B_71, k1_setfam_1(A_72)) | k1_xboole_0=A_72)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.33/1.99  tff(c_301, plain, (![A_6, A_72]: (r1_tarski(A_6, k1_setfam_1(A_72)) | k1_xboole_0=A_72 | k4_xboole_0(A_6, '#skF_3'(A_72, A_6))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_293])).
% 5.33/1.99  tff(c_3704, plain, (r1_tarski('#skF_4', k1_setfam_1(k1_tarski('#skF_4'))) | k1_tarski('#skF_4')=k1_xboole_0 | k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3688, c_301])).
% 5.33/1.99  tff(c_3714, plain, (r1_tarski('#skF_4', k1_setfam_1(k1_tarski('#skF_4'))) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3704])).
% 5.33/1.99  tff(c_3715, plain, (r1_tarski('#skF_4', k1_setfam_1(k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_75, c_3714])).
% 5.33/1.99  tff(c_3724, plain, (k1_setfam_1(k1_tarski('#skF_4'))='#skF_4' | ~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_3715, c_173])).
% 5.33/1.99  tff(c_3740, plain, (k1_setfam_1(k1_tarski('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_503, c_3724])).
% 5.33/1.99  tff(c_3742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_3740])).
% 5.33/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/1.99  
% 5.33/1.99  Inference rules
% 5.33/1.99  ----------------------
% 5.33/1.99  #Ref     : 0
% 5.33/1.99  #Sup     : 874
% 5.33/1.99  #Fact    : 1
% 5.33/1.99  #Define  : 0
% 5.33/1.99  #Split   : 0
% 5.33/1.99  #Chain   : 0
% 5.33/1.99  #Close   : 0
% 5.33/1.99  
% 5.33/1.99  Ordering : KBO
% 5.33/1.99  
% 5.33/1.99  Simplification rules
% 5.33/1.99  ----------------------
% 5.33/1.99  #Subsume      : 144
% 5.33/1.99  #Demod        : 114
% 5.33/1.99  #Tautology    : 169
% 5.33/1.99  #SimpNegUnit  : 120
% 5.33/1.99  #BackRed      : 1
% 5.33/1.99  
% 5.33/1.99  #Partial instantiations: 1496
% 5.33/1.99  #Strategies tried      : 1
% 5.33/1.99  
% 5.33/1.99  Timing (in seconds)
% 5.33/1.99  ----------------------
% 5.33/1.99  Preprocessing        : 0.32
% 5.33/1.99  Parsing              : 0.16
% 5.33/1.99  CNF conversion       : 0.02
% 5.33/1.99  Main loop            : 0.92
% 5.33/1.99  Inferencing          : 0.35
% 5.33/1.99  Reduction            : 0.24
% 5.33/1.99  Demodulation         : 0.15
% 5.33/1.99  BG Simplification    : 0.05
% 5.33/1.99  Subsumption          : 0.21
% 5.33/1.99  Abstraction          : 0.07
% 5.33/1.99  MUC search           : 0.00
% 5.33/1.99  Cooper               : 0.00
% 5.33/1.99  Total                : 1.27
% 5.33/1.99  Index Insertion      : 0.00
% 5.33/1.99  Index Deletion       : 0.00
% 5.33/1.99  Index Matching       : 0.00
% 5.33/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
