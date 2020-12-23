%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:50 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 170 expanded)
%              Number of leaves         :   31 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 240 expanded)
%              Number of equality atoms :   37 ( 125 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_82,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_82,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,A_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_147,plain,(
    ! [B_62,A_63] : k2_xboole_0(B_62,A_63) = k2_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_287,plain,(
    ! [A_67,B_68] : r1_tarski(A_67,k2_xboole_0(B_68,A_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_40])).

tff(c_299,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_287])).

tff(c_866,plain,(
    ! [B_108,A_109] :
      ( k1_tarski(B_108) = A_109
      | k1_xboole_0 = A_109
      | ~ r1_tarski(A_109,k1_tarski(B_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_878,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_4')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_299,c_866])).

tff(c_884,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_878])).

tff(c_68,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_312,plain,(
    ! [A_69,B_70] : k1_enumset1(A_69,A_69,B_70) = k2_tarski(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ! [E_33,A_27,B_28] : r2_hidden(E_33,k1_enumset1(A_27,B_28,E_33)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_330,plain,(
    ! [B_71,A_72] : r2_hidden(B_71,k2_tarski(A_72,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_46])).

tff(c_333,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_330])).

tff(c_902,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_884,c_333])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_908,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_5',B_6)
      | ~ r1_tarski(k1_xboole_0,B_6) ) ),
    inference(resolution,[status(thm)],[c_902,c_6])).

tff(c_911,plain,(
    ! [B_6] : r2_hidden('#skF_5',B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_908])).

tff(c_1429,plain,(
    ! [A_159,C_160,B_161] :
      ( ~ r2_hidden(A_159,C_160)
      | ~ r2_hidden(A_159,B_161)
      | ~ r2_hidden(A_159,k5_xboole_0(B_161,C_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1439,plain,(
    ! [C_160,B_161] :
      ( ~ r2_hidden('#skF_5',C_160)
      | ~ r2_hidden('#skF_5',B_161) ) ),
    inference(resolution,[status(thm)],[c_911,c_1429])).

tff(c_1466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_911,c_1439])).

tff(c_1467,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_878])).

tff(c_620,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_631,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_299,c_620])).

tff(c_680,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_631])).

tff(c_1471,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_680])).

tff(c_1479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1471])).

tff(c_1480,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_631])).

tff(c_1493,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1480,c_333])).

tff(c_70,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2835,plain,(
    ! [E_277,C_278,B_279,A_280] :
      ( E_277 = C_278
      | E_277 = B_279
      | E_277 = A_280
      | ~ r2_hidden(E_277,k1_enumset1(A_280,B_279,C_278)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_9050,plain,(
    ! [E_14057,B_14058,A_14059] :
      ( E_14057 = B_14058
      | E_14057 = A_14059
      | E_14057 = A_14059
      | ~ r2_hidden(E_14057,k2_tarski(A_14059,B_14058)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2835])).

tff(c_9082,plain,(
    ! [E_14159,A_14160] :
      ( E_14159 = A_14160
      | E_14159 = A_14160
      | E_14159 = A_14160
      | ~ r2_hidden(E_14159,k1_tarski(A_14160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_9050])).

tff(c_9096,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1493,c_9082])).

tff(c_9112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_82,c_82,c_9096])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.41/2.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.67  
% 7.41/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.67  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.41/2.67  
% 7.41/2.67  %Foreground sorts:
% 7.41/2.67  
% 7.41/2.67  
% 7.41/2.67  %Background operators:
% 7.41/2.67  
% 7.41/2.67  
% 7.41/2.67  %Foreground operators:
% 7.41/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.41/2.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.41/2.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.41/2.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.41/2.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.41/2.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.41/2.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.41/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.41/2.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.41/2.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.41/2.67  tff('#skF_5', type, '#skF_5': $i).
% 7.41/2.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.41/2.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.41/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.41/2.67  tff('#skF_4', type, '#skF_4': $i).
% 7.41/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.41/2.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.41/2.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.41/2.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.41/2.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.41/2.67  
% 7.41/2.68  tff(f_99, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 7.41/2.68  tff(f_51, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.41/2.68  tff(f_61, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.41/2.68  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.41/2.68  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.41/2.68  tff(f_94, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 7.41/2.68  tff(f_82, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.41/2.68  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.41/2.68  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.41/2.68  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.41/2.68  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 7.41/2.68  tff(c_82, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.41/2.68  tff(c_30, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.41/2.68  tff(c_38, plain, (![A_22]: (r1_tarski(k1_xboole_0, A_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.41/2.68  tff(c_84, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.41/2.68  tff(c_147, plain, (![B_62, A_63]: (k2_xboole_0(B_62, A_63)=k2_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.41/2.68  tff(c_40, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.41/2.68  tff(c_287, plain, (![A_67, B_68]: (r1_tarski(A_67, k2_xboole_0(B_68, A_67)))), inference(superposition, [status(thm), theory('equality')], [c_147, c_40])).
% 7.41/2.68  tff(c_299, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_287])).
% 7.41/2.68  tff(c_866, plain, (![B_108, A_109]: (k1_tarski(B_108)=A_109 | k1_xboole_0=A_109 | ~r1_tarski(A_109, k1_tarski(B_108)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.41/2.68  tff(c_878, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_299, c_866])).
% 7.41/2.68  tff(c_884, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_878])).
% 7.41/2.68  tff(c_68, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.41/2.68  tff(c_312, plain, (![A_69, B_70]: (k1_enumset1(A_69, A_69, B_70)=k2_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.41/2.68  tff(c_46, plain, (![E_33, A_27, B_28]: (r2_hidden(E_33, k1_enumset1(A_27, B_28, E_33)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.41/2.68  tff(c_330, plain, (![B_71, A_72]: (r2_hidden(B_71, k2_tarski(A_72, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_312, c_46])).
% 7.41/2.68  tff(c_333, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_330])).
% 7.41/2.68  tff(c_902, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_884, c_333])).
% 7.41/2.68  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.41/2.68  tff(c_908, plain, (![B_6]: (r2_hidden('#skF_5', B_6) | ~r1_tarski(k1_xboole_0, B_6))), inference(resolution, [status(thm)], [c_902, c_6])).
% 7.41/2.68  tff(c_911, plain, (![B_6]: (r2_hidden('#skF_5', B_6))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_908])).
% 7.41/2.68  tff(c_1429, plain, (![A_159, C_160, B_161]: (~r2_hidden(A_159, C_160) | ~r2_hidden(A_159, B_161) | ~r2_hidden(A_159, k5_xboole_0(B_161, C_160)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.41/2.68  tff(c_1439, plain, (![C_160, B_161]: (~r2_hidden('#skF_5', C_160) | ~r2_hidden('#skF_5', B_161))), inference(resolution, [status(thm)], [c_911, c_1429])).
% 7.41/2.68  tff(c_1466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_911, c_911, c_1439])).
% 7.41/2.68  tff(c_1467, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_878])).
% 7.41/2.68  tff(c_620, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.41/2.68  tff(c_631, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_299, c_620])).
% 7.41/2.68  tff(c_680, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_631])).
% 7.41/2.68  tff(c_1471, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_680])).
% 7.41/2.68  tff(c_1479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1471])).
% 7.41/2.68  tff(c_1480, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_631])).
% 7.41/2.68  tff(c_1493, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1480, c_333])).
% 7.41/2.68  tff(c_70, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.41/2.68  tff(c_2835, plain, (![E_277, C_278, B_279, A_280]: (E_277=C_278 | E_277=B_279 | E_277=A_280 | ~r2_hidden(E_277, k1_enumset1(A_280, B_279, C_278)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.41/2.68  tff(c_9050, plain, (![E_14057, B_14058, A_14059]: (E_14057=B_14058 | E_14057=A_14059 | E_14057=A_14059 | ~r2_hidden(E_14057, k2_tarski(A_14059, B_14058)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2835])).
% 7.41/2.68  tff(c_9082, plain, (![E_14159, A_14160]: (E_14159=A_14160 | E_14159=A_14160 | E_14159=A_14160 | ~r2_hidden(E_14159, k1_tarski(A_14160)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_9050])).
% 7.41/2.68  tff(c_9096, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1493, c_9082])).
% 7.41/2.68  tff(c_9112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_82, c_82, c_9096])).
% 7.41/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.68  
% 7.41/2.68  Inference rules
% 7.41/2.68  ----------------------
% 7.41/2.68  #Ref     : 0
% 7.41/2.68  #Sup     : 1636
% 7.41/2.68  #Fact    : 18
% 7.41/2.68  #Define  : 0
% 7.41/2.68  #Split   : 2
% 7.41/2.68  #Chain   : 0
% 7.41/2.68  #Close   : 0
% 7.41/2.68  
% 7.41/2.68  Ordering : KBO
% 7.41/2.68  
% 7.41/2.68  Simplification rules
% 7.41/2.68  ----------------------
% 7.41/2.68  #Subsume      : 322
% 7.41/2.68  #Demod        : 937
% 7.41/2.68  #Tautology    : 821
% 7.41/2.68  #SimpNegUnit  : 1
% 7.41/2.68  #BackRed      : 17
% 7.41/2.68  
% 7.41/2.68  #Partial instantiations: 6255
% 7.41/2.68  #Strategies tried      : 1
% 7.41/2.68  
% 7.41/2.68  Timing (in seconds)
% 7.41/2.68  ----------------------
% 7.41/2.69  Preprocessing        : 0.37
% 7.41/2.69  Parsing              : 0.19
% 7.41/2.69  CNF conversion       : 0.03
% 7.41/2.69  Main loop            : 1.50
% 7.41/2.69  Inferencing          : 0.63
% 7.41/2.69  Reduction            : 0.54
% 7.41/2.69  Demodulation         : 0.45
% 7.41/2.69  BG Simplification    : 0.05
% 7.41/2.69  Subsumption          : 0.20
% 7.41/2.69  Abstraction          : 0.06
% 7.41/2.69  MUC search           : 0.00
% 7.41/2.69  Cooper               : 0.00
% 7.41/2.69  Total                : 1.90
% 7.41/2.69  Index Insertion      : 0.00
% 7.41/2.69  Index Deletion       : 0.00
% 7.41/2.69  Index Matching       : 0.00
% 7.41/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
