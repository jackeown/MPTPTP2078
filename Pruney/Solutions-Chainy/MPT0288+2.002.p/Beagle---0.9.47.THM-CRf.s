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
% DateTime   : Thu Dec  3 09:53:31 EST 2020

% Result     : Theorem 20.16s
% Output     : CNFRefutation 20.16s
% Verified   : 
% Statistics : Number of formulae       :   68 (  73 expanded)
%              Number of leaves         :   33 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 (  96 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_65,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_54,plain,(
    ~ r1_tarski(k3_tarski('#skF_5'),k3_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_4'(A_35,B_36),A_35)
      | r1_tarski(k3_tarski(A_35),B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    ! [A_28] : r1_xboole_0(A_28,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_245,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_249,plain,(
    ! [A_69,C_70] :
      ( ~ r1_xboole_0(A_69,A_69)
      | ~ r2_hidden(C_70,A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_245])).

tff(c_253,plain,(
    ! [C_70] : ~ r2_hidden(C_70,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_249])).

tff(c_44,plain,(
    ! [B_30,A_29] : k2_tarski(B_30,A_29) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_109,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_127,plain,(
    ! [B_50,A_51] : k3_tarski(k2_tarski(B_50,A_51)) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_109])).

tff(c_48,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_133,plain,(
    ! [B_50,A_51] : k2_xboole_0(B_50,A_51) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_48])).

tff(c_36,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_56,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_254,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_287,plain,(
    ! [A_77] :
      ( r1_tarski(A_77,'#skF_6')
      | ~ r1_tarski(A_77,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_254])).

tff(c_300,plain,(
    ! [B_21] : r1_tarski(k4_xboole_0('#skF_5',B_21),'#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_287])).

tff(c_811,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_tarski(A_122,k2_xboole_0(B_123,C_124))
      | ~ r1_tarski(k4_xboole_0(A_122,B_123),C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_889,plain,(
    ! [B_127] : r1_tarski('#skF_5',k2_xboole_0(B_127,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_300,c_811])).

tff(c_1053,plain,(
    ! [A_133] : r1_tarski('#skF_5',k2_xboole_0('#skF_6',A_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_889])).

tff(c_627,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_tarski(k4_xboole_0(A_115,B_116),C_117)
      | ~ r1_tarski(A_115,k2_xboole_0(B_116,C_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_188,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_205,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_188])).

tff(c_664,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(A_115,B_116) = k1_xboole_0
      | ~ r1_tarski(A_115,k2_xboole_0(B_116,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_627,c_205])).

tff(c_1070,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1053,c_664])).

tff(c_1135,plain,(
    ! [D_134,A_135,B_136] :
      ( r2_hidden(D_134,k4_xboole_0(A_135,B_136))
      | r2_hidden(D_134,B_136)
      | ~ r2_hidden(D_134,A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1144,plain,(
    ! [D_134] :
      ( r2_hidden(D_134,k1_xboole_0)
      | r2_hidden(D_134,'#skF_6')
      | ~ r2_hidden(D_134,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1070,c_1135])).

tff(c_1165,plain,(
    ! [D_137] :
      ( r2_hidden(D_137,'#skF_6')
      | ~ r2_hidden(D_137,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_1144])).

tff(c_62990,plain,(
    ! [B_1034] :
      ( r2_hidden('#skF_4'('#skF_5',B_1034),'#skF_6')
      | r1_tarski(k3_tarski('#skF_5'),B_1034) ) ),
    inference(resolution,[status(thm)],[c_52,c_1165])).

tff(c_46,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,k3_tarski(B_32))
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_417,plain,(
    ! [A_91,B_92] :
      ( ~ r1_tarski('#skF_4'(A_91,B_92),B_92)
      | r1_tarski(k3_tarski(A_91),B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_421,plain,(
    ! [A_91,B_32] :
      ( r1_tarski(k3_tarski(A_91),k3_tarski(B_32))
      | ~ r2_hidden('#skF_4'(A_91,k3_tarski(B_32)),B_32) ) ),
    inference(resolution,[status(thm)],[c_46,c_417])).

tff(c_62996,plain,(
    r1_tarski(k3_tarski('#skF_5'),k3_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_62990,c_421])).

tff(c_63001,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_62996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:59:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.16/11.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.16/11.19  
% 20.16/11.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.16/11.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 20.16/11.19  
% 20.16/11.19  %Foreground sorts:
% 20.16/11.19  
% 20.16/11.19  
% 20.16/11.19  %Background operators:
% 20.16/11.19  
% 20.16/11.19  
% 20.16/11.19  %Foreground operators:
% 20.16/11.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 20.16/11.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.16/11.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.16/11.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.16/11.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.16/11.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.16/11.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.16/11.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.16/11.19  tff('#skF_5', type, '#skF_5': $i).
% 20.16/11.19  tff('#skF_6', type, '#skF_6': $i).
% 20.16/11.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 20.16/11.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.16/11.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.16/11.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.16/11.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.16/11.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.16/11.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.16/11.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 20.16/11.19  
% 20.16/11.21  tff(f_97, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 20.16/11.21  tff(f_92, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 20.16/11.21  tff(f_77, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 20.16/11.21  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 20.16/11.21  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 20.16/11.21  tff(f_79, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 20.16/11.21  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 20.16/11.21  tff(f_67, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 20.16/11.21  tff(f_63, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 20.16/11.21  tff(f_75, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 20.16/11.21  tff(f_71, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 20.16/11.21  tff(f_65, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 20.16/11.21  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.16/11.21  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 20.16/11.21  tff(f_83, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 20.16/11.21  tff(c_54, plain, (~r1_tarski(k3_tarski('#skF_5'), k3_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 20.16/11.21  tff(c_52, plain, (![A_35, B_36]: (r2_hidden('#skF_4'(A_35, B_36), A_35) | r1_tarski(k3_tarski(A_35), B_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 20.16/11.21  tff(c_42, plain, (![A_28]: (r1_xboole_0(A_28, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_77])).
% 20.16/11.21  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.16/11.21  tff(c_245, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.16/11.21  tff(c_249, plain, (![A_69, C_70]: (~r1_xboole_0(A_69, A_69) | ~r2_hidden(C_70, A_69))), inference(superposition, [status(thm), theory('equality')], [c_20, c_245])).
% 20.16/11.21  tff(c_253, plain, (![C_70]: (~r2_hidden(C_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_249])).
% 20.16/11.21  tff(c_44, plain, (![B_30, A_29]: (k2_tarski(B_30, A_29)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 20.16/11.21  tff(c_109, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_85])).
% 20.16/11.21  tff(c_127, plain, (![B_50, A_51]: (k3_tarski(k2_tarski(B_50, A_51))=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_44, c_109])).
% 20.16/11.21  tff(c_48, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_85])).
% 20.16/11.21  tff(c_133, plain, (![B_50, A_51]: (k2_xboole_0(B_50, A_51)=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_127, c_48])).
% 20.16/11.21  tff(c_36, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 20.16/11.21  tff(c_56, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 20.16/11.21  tff(c_254, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, C_72) | ~r1_tarski(B_73, C_72) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_63])).
% 20.16/11.21  tff(c_287, plain, (![A_77]: (r1_tarski(A_77, '#skF_6') | ~r1_tarski(A_77, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_254])).
% 20.16/11.21  tff(c_300, plain, (![B_21]: (r1_tarski(k4_xboole_0('#skF_5', B_21), '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_287])).
% 20.16/11.21  tff(c_811, plain, (![A_122, B_123, C_124]: (r1_tarski(A_122, k2_xboole_0(B_123, C_124)) | ~r1_tarski(k4_xboole_0(A_122, B_123), C_124))), inference(cnfTransformation, [status(thm)], [f_75])).
% 20.16/11.21  tff(c_889, plain, (![B_127]: (r1_tarski('#skF_5', k2_xboole_0(B_127, '#skF_6')))), inference(resolution, [status(thm)], [c_300, c_811])).
% 20.16/11.21  tff(c_1053, plain, (![A_133]: (r1_tarski('#skF_5', k2_xboole_0('#skF_6', A_133)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_889])).
% 20.16/11.21  tff(c_627, plain, (![A_115, B_116, C_117]: (r1_tarski(k4_xboole_0(A_115, B_116), C_117) | ~r1_tarski(A_115, k2_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.16/11.21  tff(c_34, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 20.16/11.21  tff(c_188, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 20.16/11.21  tff(c_205, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_188])).
% 20.16/11.21  tff(c_664, plain, (![A_115, B_116]: (k4_xboole_0(A_115, B_116)=k1_xboole_0 | ~r1_tarski(A_115, k2_xboole_0(B_116, k1_xboole_0)))), inference(resolution, [status(thm)], [c_627, c_205])).
% 20.16/11.21  tff(c_1070, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_1053, c_664])).
% 20.16/11.21  tff(c_1135, plain, (![D_134, A_135, B_136]: (r2_hidden(D_134, k4_xboole_0(A_135, B_136)) | r2_hidden(D_134, B_136) | ~r2_hidden(D_134, A_135))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.16/11.21  tff(c_1144, plain, (![D_134]: (r2_hidden(D_134, k1_xboole_0) | r2_hidden(D_134, '#skF_6') | ~r2_hidden(D_134, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1070, c_1135])).
% 20.16/11.21  tff(c_1165, plain, (![D_137]: (r2_hidden(D_137, '#skF_6') | ~r2_hidden(D_137, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_253, c_1144])).
% 20.16/11.21  tff(c_62990, plain, (![B_1034]: (r2_hidden('#skF_4'('#skF_5', B_1034), '#skF_6') | r1_tarski(k3_tarski('#skF_5'), B_1034))), inference(resolution, [status(thm)], [c_52, c_1165])).
% 20.16/11.21  tff(c_46, plain, (![A_31, B_32]: (r1_tarski(A_31, k3_tarski(B_32)) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 20.16/11.21  tff(c_417, plain, (![A_91, B_92]: (~r1_tarski('#skF_4'(A_91, B_92), B_92) | r1_tarski(k3_tarski(A_91), B_92))), inference(cnfTransformation, [status(thm)], [f_92])).
% 20.16/11.21  tff(c_421, plain, (![A_91, B_32]: (r1_tarski(k3_tarski(A_91), k3_tarski(B_32)) | ~r2_hidden('#skF_4'(A_91, k3_tarski(B_32)), B_32))), inference(resolution, [status(thm)], [c_46, c_417])).
% 20.16/11.21  tff(c_62996, plain, (r1_tarski(k3_tarski('#skF_5'), k3_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_62990, c_421])).
% 20.16/11.21  tff(c_63001, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_62996])).
% 20.16/11.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.16/11.21  
% 20.16/11.21  Inference rules
% 20.16/11.21  ----------------------
% 20.16/11.21  #Ref     : 0
% 20.16/11.21  #Sup     : 15257
% 20.16/11.21  #Fact    : 0
% 20.16/11.21  #Define  : 0
% 20.16/11.21  #Split   : 7
% 20.16/11.21  #Chain   : 0
% 20.16/11.21  #Close   : 0
% 20.16/11.21  
% 20.16/11.21  Ordering : KBO
% 20.16/11.21  
% 20.16/11.21  Simplification rules
% 20.16/11.21  ----------------------
% 20.16/11.21  #Subsume      : 2627
% 20.16/11.21  #Demod        : 18071
% 20.16/11.21  #Tautology    : 8392
% 20.16/11.21  #SimpNegUnit  : 309
% 20.16/11.21  #BackRed      : 107
% 20.16/11.21  
% 20.16/11.21  #Partial instantiations: 0
% 20.16/11.21  #Strategies tried      : 1
% 20.16/11.21  
% 20.16/11.21  Timing (in seconds)
% 20.16/11.21  ----------------------
% 20.16/11.21  Preprocessing        : 0.30
% 20.16/11.21  Parsing              : 0.17
% 20.16/11.21  CNF conversion       : 0.02
% 20.16/11.21  Main loop            : 10.13
% 20.16/11.21  Inferencing          : 1.27
% 20.16/11.21  Reduction            : 5.65
% 20.16/11.21  Demodulation         : 5.02
% 20.16/11.21  BG Simplification    : 0.14
% 20.16/11.21  Subsumption          : 2.66
% 20.16/11.21  Abstraction          : 0.21
% 20.16/11.21  MUC search           : 0.00
% 20.16/11.21  Cooper               : 0.00
% 20.16/11.21  Total                : 10.47
% 20.16/11.21  Index Insertion      : 0.00
% 20.16/11.21  Index Deletion       : 0.00
% 20.16/11.21  Index Matching       : 0.00
% 20.16/11.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
