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
% DateTime   : Thu Dec  3 09:48:25 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 102 expanded)
%              Number of equality atoms :   33 (  60 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_50,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_69,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    ! [B_39,A_40] : r2_hidden(B_39,k2_tarski(A_40,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_18])).

tff(c_90,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_87])).

tff(c_20,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    ! [A_37,B_38] : r2_hidden(A_37,k2_tarski(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_20])).

tff(c_44,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [A_20,B_21,C_22] : k2_enumset1(A_20,A_20,B_21,C_22) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_163,plain,(
    ! [A_65,B_66,C_67,D_68] : k2_xboole_0(k1_enumset1(A_65,B_66,C_67),k1_tarski(D_68)) = k2_enumset1(A_65,B_66,C_67,D_68) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_175,plain,(
    ! [A_18,B_19,D_68] : k2_xboole_0(k2_tarski(A_18,B_19),k1_tarski(D_68)) = k2_enumset1(A_18,A_18,B_19,D_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_163])).

tff(c_198,plain,(
    ! [A_73,B_74,D_75] : k2_xboole_0(k2_tarski(A_73,B_74),k1_tarski(D_75)) = k1_enumset1(A_73,B_74,D_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_175])).

tff(c_210,plain,(
    ! [A_17,D_75] : k2_xboole_0(k1_tarski(A_17),k1_tarski(D_75)) = k1_enumset1(A_17,A_17,D_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_198])).

tff(c_213,plain,(
    ! [A_17,D_75] : k2_xboole_0(k1_tarski(A_17),k1_tarski(D_75)) = k2_tarski(A_17,D_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_210])).

tff(c_52,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_1,C_3,B_2] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(A_1,B_2)
      | r2_hidden(A_1,k5_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_4,B_5] : k5_xboole_0(k5_xboole_0(A_4,B_5),k2_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_143,plain,(
    ! [A_59,C_60,B_61] :
      ( ~ r2_hidden(A_59,C_60)
      | ~ r2_hidden(A_59,B_61)
      | ~ r2_hidden(A_59,k5_xboole_0(B_61,C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_369,plain,(
    ! [A_100,A_101,B_102] :
      ( ~ r2_hidden(A_100,k2_xboole_0(A_101,B_102))
      | ~ r2_hidden(A_100,k5_xboole_0(A_101,B_102))
      | ~ r2_hidden(A_100,k3_xboole_0(A_101,B_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_143])).

tff(c_508,plain,(
    ! [A_119,B_120,C_121] :
      ( ~ r2_hidden(A_119,k2_xboole_0(B_120,C_121))
      | ~ r2_hidden(A_119,k3_xboole_0(B_120,C_121))
      | r2_hidden(A_119,C_121)
      | ~ r2_hidden(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_12,c_369])).

tff(c_520,plain,(
    ! [A_119] :
      ( ~ r2_hidden(A_119,k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
      | ~ r2_hidden(A_119,k1_tarski('#skF_3'))
      | r2_hidden(A_119,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_119,k1_tarski('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_508])).

tff(c_786,plain,(
    ! [A_145] :
      ( ~ r2_hidden(A_145,k2_tarski('#skF_3','#skF_4'))
      | ~ r2_hidden(A_145,k1_tarski('#skF_3'))
      | r2_hidden(A_145,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_145,k1_tarski('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_520])).

tff(c_800,plain,
    ( r2_hidden('#skF_3',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_786])).

tff(c_810,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_800])).

tff(c_179,plain,(
    ! [E_69,C_70,B_71,A_72] :
      ( E_69 = C_70
      | E_69 = B_71
      | E_69 = A_72
      | ~ r2_hidden(E_69,k1_enumset1(A_72,B_71,C_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_226,plain,(
    ! [E_78,B_79,A_80] :
      ( E_78 = B_79
      | E_78 = A_80
      | E_78 = A_80
      | ~ r2_hidden(E_78,k2_tarski(A_80,B_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_179])).

tff(c_235,plain,(
    ! [E_78,A_17] :
      ( E_78 = A_17
      | E_78 = A_17
      | E_78 = A_17
      | ~ r2_hidden(E_78,k1_tarski(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_226])).

tff(c_818,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_810,c_235])).

tff(c_826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_50,c_818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n014.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:45:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.42  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.78/1.42  
% 2.78/1.42  %Foreground sorts:
% 2.78/1.42  
% 2.78/1.42  
% 2.78/1.42  %Background operators:
% 2.78/1.42  
% 2.78/1.42  
% 2.78/1.42  %Foreground operators:
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.78/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.78/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.78/1.42  
% 3.05/1.43  tff(f_64, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.05/1.43  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.05/1.43  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.05/1.43  tff(f_49, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.05/1.43  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.05/1.43  tff(f_51, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.05/1.43  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.05/1.43  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.05/1.43  tff(c_50, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.05/1.43  tff(c_42, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.05/1.43  tff(c_69, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.05/1.43  tff(c_18, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.05/1.43  tff(c_87, plain, (![B_39, A_40]: (r2_hidden(B_39, k2_tarski(A_40, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_18])).
% 3.05/1.43  tff(c_90, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_87])).
% 3.05/1.43  tff(c_20, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.05/1.43  tff(c_78, plain, (![A_37, B_38]: (r2_hidden(A_37, k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_20])).
% 3.05/1.43  tff(c_44, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.05/1.43  tff(c_46, plain, (![A_20, B_21, C_22]: (k2_enumset1(A_20, A_20, B_21, C_22)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.05/1.43  tff(c_163, plain, (![A_65, B_66, C_67, D_68]: (k2_xboole_0(k1_enumset1(A_65, B_66, C_67), k1_tarski(D_68))=k2_enumset1(A_65, B_66, C_67, D_68))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.05/1.43  tff(c_175, plain, (![A_18, B_19, D_68]: (k2_xboole_0(k2_tarski(A_18, B_19), k1_tarski(D_68))=k2_enumset1(A_18, A_18, B_19, D_68))), inference(superposition, [status(thm), theory('equality')], [c_44, c_163])).
% 3.05/1.43  tff(c_198, plain, (![A_73, B_74, D_75]: (k2_xboole_0(k2_tarski(A_73, B_74), k1_tarski(D_75))=k1_enumset1(A_73, B_74, D_75))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_175])).
% 3.05/1.43  tff(c_210, plain, (![A_17, D_75]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(D_75))=k1_enumset1(A_17, A_17, D_75))), inference(superposition, [status(thm), theory('equality')], [c_42, c_198])).
% 3.05/1.43  tff(c_213, plain, (![A_17, D_75]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(D_75))=k2_tarski(A_17, D_75))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_210])).
% 3.05/1.43  tff(c_52, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.05/1.43  tff(c_12, plain, (![A_1, C_3, B_2]: (r2_hidden(A_1, C_3) | ~r2_hidden(A_1, B_2) | r2_hidden(A_1, k5_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.05/1.43  tff(c_14, plain, (![A_4, B_5]: (k5_xboole_0(k5_xboole_0(A_4, B_5), k2_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.05/1.43  tff(c_143, plain, (![A_59, C_60, B_61]: (~r2_hidden(A_59, C_60) | ~r2_hidden(A_59, B_61) | ~r2_hidden(A_59, k5_xboole_0(B_61, C_60)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.05/1.43  tff(c_369, plain, (![A_100, A_101, B_102]: (~r2_hidden(A_100, k2_xboole_0(A_101, B_102)) | ~r2_hidden(A_100, k5_xboole_0(A_101, B_102)) | ~r2_hidden(A_100, k3_xboole_0(A_101, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_143])).
% 3.05/1.43  tff(c_508, plain, (![A_119, B_120, C_121]: (~r2_hidden(A_119, k2_xboole_0(B_120, C_121)) | ~r2_hidden(A_119, k3_xboole_0(B_120, C_121)) | r2_hidden(A_119, C_121) | ~r2_hidden(A_119, B_120))), inference(resolution, [status(thm)], [c_12, c_369])).
% 3.05/1.43  tff(c_520, plain, (![A_119]: (~r2_hidden(A_119, k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | ~r2_hidden(A_119, k1_tarski('#skF_3')) | r2_hidden(A_119, k1_tarski('#skF_4')) | ~r2_hidden(A_119, k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_508])).
% 3.05/1.43  tff(c_786, plain, (![A_145]: (~r2_hidden(A_145, k2_tarski('#skF_3', '#skF_4')) | ~r2_hidden(A_145, k1_tarski('#skF_3')) | r2_hidden(A_145, k1_tarski('#skF_4')) | ~r2_hidden(A_145, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_520])).
% 3.05/1.43  tff(c_800, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_78, c_786])).
% 3.05/1.43  tff(c_810, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_800])).
% 3.05/1.43  tff(c_179, plain, (![E_69, C_70, B_71, A_72]: (E_69=C_70 | E_69=B_71 | E_69=A_72 | ~r2_hidden(E_69, k1_enumset1(A_72, B_71, C_70)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.05/1.43  tff(c_226, plain, (![E_78, B_79, A_80]: (E_78=B_79 | E_78=A_80 | E_78=A_80 | ~r2_hidden(E_78, k2_tarski(A_80, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_179])).
% 3.05/1.43  tff(c_235, plain, (![E_78, A_17]: (E_78=A_17 | E_78=A_17 | E_78=A_17 | ~r2_hidden(E_78, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_226])).
% 3.05/1.43  tff(c_818, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_810, c_235])).
% 3.05/1.43  tff(c_826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_50, c_818])).
% 3.05/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.43  
% 3.05/1.43  Inference rules
% 3.05/1.43  ----------------------
% 3.05/1.43  #Ref     : 0
% 3.05/1.43  #Sup     : 178
% 3.05/1.43  #Fact    : 0
% 3.05/1.43  #Define  : 0
% 3.05/1.43  #Split   : 0
% 3.05/1.43  #Chain   : 0
% 3.05/1.43  #Close   : 0
% 3.05/1.43  
% 3.05/1.43  Ordering : KBO
% 3.05/1.43  
% 3.05/1.43  Simplification rules
% 3.05/1.43  ----------------------
% 3.05/1.43  #Subsume      : 2
% 3.05/1.43  #Demod        : 20
% 3.05/1.43  #Tautology    : 69
% 3.05/1.43  #SimpNegUnit  : 3
% 3.05/1.43  #BackRed      : 0
% 3.05/1.43  
% 3.05/1.43  #Partial instantiations: 0
% 3.05/1.43  #Strategies tried      : 1
% 3.05/1.43  
% 3.05/1.43  Timing (in seconds)
% 3.05/1.43  ----------------------
% 3.05/1.44  Preprocessing        : 0.29
% 3.05/1.44  Parsing              : 0.15
% 3.05/1.44  CNF conversion       : 0.02
% 3.05/1.44  Main loop            : 0.38
% 3.05/1.44  Inferencing          : 0.15
% 3.05/1.44  Reduction            : 0.10
% 3.05/1.44  Demodulation         : 0.08
% 3.05/1.44  BG Simplification    : 0.02
% 3.05/1.44  Subsumption          : 0.08
% 3.05/1.44  Abstraction          : 0.02
% 3.05/1.44  MUC search           : 0.00
% 3.05/1.44  Cooper               : 0.00
% 3.05/1.44  Total                : 0.70
% 3.05/1.44  Index Insertion      : 0.00
% 3.05/1.44  Index Deletion       : 0.00
% 3.05/1.44  Index Matching       : 0.00
% 3.05/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
