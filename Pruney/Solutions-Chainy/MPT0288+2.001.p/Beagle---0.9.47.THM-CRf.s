%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:31 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.49s
% Verified   : 
% Statistics : Number of formulae       :   65 (  84 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :   76 ( 105 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_52,plain,(
    ~ r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_3'(A_31,B_32),A_31)
      | r1_tarski(k3_tarski(A_31),B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_251,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_286,plain,(
    ! [B_57,A_58] : k3_tarski(k2_tarski(B_57,A_58)) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_251])).

tff(c_46,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_312,plain,(
    ! [B_59,A_60] : k2_xboole_0(B_59,A_60) = k2_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_46])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_269,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(k2_xboole_0(A_52,B_54),C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_279,plain,(
    ! [A_52,B_54] : r1_tarski(A_52,k2_xboole_0(A_52,B_54)) ),
    inference(resolution,[status(thm)],[c_26,c_269])).

tff(c_327,plain,(
    ! [A_60,B_59] : r1_tarski(A_60,k2_xboole_0(B_59,A_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_279])).

tff(c_827,plain,(
    ! [A_106,B_107,C_108] :
      ( r1_tarski(k4_xboole_0(A_106,B_107),C_108)
      | ~ r1_tarski(A_106,k2_xboole_0(B_107,C_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_852,plain,(
    ! [A_109,C_110] :
      ( r1_tarski(A_109,C_110)
      | ~ r1_tarski(A_109,k2_xboole_0(k1_xboole_0,C_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_827])).

tff(c_911,plain,(
    ! [C_111] : r1_tarski(k2_xboole_0(k1_xboole_0,C_111),C_111) ),
    inference(resolution,[status(thm)],[c_26,c_852])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_920,plain,(
    ! [C_111] :
      ( k2_xboole_0(k1_xboole_0,C_111) = C_111
      | ~ r1_tarski(C_111,k2_xboole_0(k1_xboole_0,C_111)) ) ),
    inference(resolution,[status(thm)],[c_911,c_22])).

tff(c_948,plain,(
    ! [C_112] : k2_xboole_0(k1_xboole_0,C_112) = C_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_920])).

tff(c_292,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_46])).

tff(c_983,plain,(
    ! [C_112] : k2_xboole_0(C_112,k1_xboole_0) = C_112 ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_292])).

tff(c_36,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_847,plain,(
    ! [A_106,B_107] :
      ( k4_xboole_0(A_106,B_107) = k1_xboole_0
      | ~ r1_tarski(A_106,k2_xboole_0(B_107,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_827,c_36])).

tff(c_1192,plain,(
    ! [A_123,B_124] :
      ( k4_xboole_0(A_123,B_124) = k1_xboole_0
      | ~ r1_tarski(A_123,B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_847])).

tff(c_1246,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_1192])).

tff(c_40,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1253,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1246,c_40])).

tff(c_1257,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1253])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1274,plain,(
    ! [D_8] :
      ( r2_hidden(D_8,'#skF_5')
      | ~ r2_hidden(D_8,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_6])).

tff(c_44,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,k3_tarski(B_28))
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_765,plain,(
    ! [A_98,B_99] :
      ( ~ r1_tarski('#skF_3'(A_98,B_99),B_99)
      | r1_tarski(k3_tarski(A_98),B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6558,plain,(
    ! [A_254,B_255] :
      ( r1_tarski(k3_tarski(A_254),k3_tarski(B_255))
      | ~ r2_hidden('#skF_3'(A_254,k3_tarski(B_255)),B_255) ) ),
    inference(resolution,[status(thm)],[c_44,c_765])).

tff(c_6596,plain,(
    ! [A_256] :
      ( r1_tarski(k3_tarski(A_256),k3_tarski('#skF_5'))
      | ~ r2_hidden('#skF_3'(A_256,k3_tarski('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1274,c_6558])).

tff(c_6600,plain,(
    r1_tarski(k3_tarski('#skF_4'),k3_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_6596])).

tff(c_6604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_6600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n022.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:19:55 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.09  
% 5.42/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/2.09  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 5.49/2.09  
% 5.49/2.09  %Foreground sorts:
% 5.49/2.09  
% 5.49/2.09  
% 5.49/2.09  %Background operators:
% 5.49/2.09  
% 5.49/2.09  
% 5.49/2.09  %Foreground operators:
% 5.49/2.09  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.49/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.49/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.49/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.49/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.49/2.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.49/2.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.49/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.49/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.49/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.49/2.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.49/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.49/2.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.49/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.49/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.49/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.49/2.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.49/2.09  
% 5.49/2.11  tff(f_82, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 5.49/2.11  tff(f_77, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 5.49/2.11  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.49/2.11  tff(f_64, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.49/2.11  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.49/2.11  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.49/2.11  tff(f_48, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.49/2.11  tff(f_60, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.49/2.11  tff(f_56, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.49/2.11  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.49/2.11  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.49/2.11  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 5.49/2.11  tff(c_52, plain, (~r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.49/2.11  tff(c_50, plain, (![A_31, B_32]: (r2_hidden('#skF_3'(A_31, B_32), A_31) | r1_tarski(k3_tarski(A_31), B_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.49/2.11  tff(c_34, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.49/2.11  tff(c_54, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.49/2.11  tff(c_42, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.49/2.11  tff(c_251, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.49/2.11  tff(c_286, plain, (![B_57, A_58]: (k3_tarski(k2_tarski(B_57, A_58))=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_42, c_251])).
% 5.49/2.11  tff(c_46, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.49/2.11  tff(c_312, plain, (![B_59, A_60]: (k2_xboole_0(B_59, A_60)=k2_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_286, c_46])).
% 5.49/2.11  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.49/2.11  tff(c_269, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(k2_xboole_0(A_52, B_54), C_53))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.49/2.11  tff(c_279, plain, (![A_52, B_54]: (r1_tarski(A_52, k2_xboole_0(A_52, B_54)))), inference(resolution, [status(thm)], [c_26, c_269])).
% 5.49/2.11  tff(c_327, plain, (![A_60, B_59]: (r1_tarski(A_60, k2_xboole_0(B_59, A_60)))), inference(superposition, [status(thm), theory('equality')], [c_312, c_279])).
% 5.49/2.11  tff(c_827, plain, (![A_106, B_107, C_108]: (r1_tarski(k4_xboole_0(A_106, B_107), C_108) | ~r1_tarski(A_106, k2_xboole_0(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.49/2.11  tff(c_852, plain, (![A_109, C_110]: (r1_tarski(A_109, C_110) | ~r1_tarski(A_109, k2_xboole_0(k1_xboole_0, C_110)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_827])).
% 5.49/2.11  tff(c_911, plain, (![C_111]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_111), C_111))), inference(resolution, [status(thm)], [c_26, c_852])).
% 5.49/2.11  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.49/2.11  tff(c_920, plain, (![C_111]: (k2_xboole_0(k1_xboole_0, C_111)=C_111 | ~r1_tarski(C_111, k2_xboole_0(k1_xboole_0, C_111)))), inference(resolution, [status(thm)], [c_911, c_22])).
% 5.49/2.11  tff(c_948, plain, (![C_112]: (k2_xboole_0(k1_xboole_0, C_112)=C_112)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_920])).
% 5.49/2.11  tff(c_292, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_286, c_46])).
% 5.49/2.11  tff(c_983, plain, (![C_112]: (k2_xboole_0(C_112, k1_xboole_0)=C_112)), inference(superposition, [status(thm), theory('equality')], [c_948, c_292])).
% 5.49/2.11  tff(c_36, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.49/2.11  tff(c_847, plain, (![A_106, B_107]: (k4_xboole_0(A_106, B_107)=k1_xboole_0 | ~r1_tarski(A_106, k2_xboole_0(B_107, k1_xboole_0)))), inference(resolution, [status(thm)], [c_827, c_36])).
% 5.49/2.11  tff(c_1192, plain, (![A_123, B_124]: (k4_xboole_0(A_123, B_124)=k1_xboole_0 | ~r1_tarski(A_123, B_124))), inference(demodulation, [status(thm), theory('equality')], [c_983, c_847])).
% 5.49/2.11  tff(c_1246, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_1192])).
% 5.49/2.11  tff(c_40, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.49/2.11  tff(c_1253, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1246, c_40])).
% 5.49/2.11  tff(c_1257, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1253])).
% 5.49/2.11  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.49/2.11  tff(c_1274, plain, (![D_8]: (r2_hidden(D_8, '#skF_5') | ~r2_hidden(D_8, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_6])).
% 5.49/2.11  tff(c_44, plain, (![A_27, B_28]: (r1_tarski(A_27, k3_tarski(B_28)) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.49/2.11  tff(c_765, plain, (![A_98, B_99]: (~r1_tarski('#skF_3'(A_98, B_99), B_99) | r1_tarski(k3_tarski(A_98), B_99))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.49/2.11  tff(c_6558, plain, (![A_254, B_255]: (r1_tarski(k3_tarski(A_254), k3_tarski(B_255)) | ~r2_hidden('#skF_3'(A_254, k3_tarski(B_255)), B_255))), inference(resolution, [status(thm)], [c_44, c_765])).
% 5.49/2.11  tff(c_6596, plain, (![A_256]: (r1_tarski(k3_tarski(A_256), k3_tarski('#skF_5')) | ~r2_hidden('#skF_3'(A_256, k3_tarski('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_1274, c_6558])).
% 5.49/2.11  tff(c_6600, plain, (r1_tarski(k3_tarski('#skF_4'), k3_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_6596])).
% 5.49/2.11  tff(c_6604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_52, c_6600])).
% 5.49/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.49/2.11  
% 5.49/2.11  Inference rules
% 5.49/2.11  ----------------------
% 5.49/2.11  #Ref     : 0
% 5.49/2.11  #Sup     : 1578
% 5.49/2.11  #Fact    : 0
% 5.49/2.11  #Define  : 0
% 5.49/2.11  #Split   : 1
% 5.49/2.11  #Chain   : 0
% 5.49/2.11  #Close   : 0
% 5.49/2.11  
% 5.49/2.11  Ordering : KBO
% 5.49/2.11  
% 5.49/2.11  Simplification rules
% 5.49/2.11  ----------------------
% 5.49/2.11  #Subsume      : 110
% 5.49/2.11  #Demod        : 1423
% 5.49/2.11  #Tautology    : 1147
% 5.49/2.11  #SimpNegUnit  : 1
% 5.49/2.11  #BackRed      : 1
% 5.49/2.11  
% 5.49/2.11  #Partial instantiations: 0
% 5.49/2.11  #Strategies tried      : 1
% 5.49/2.11  
% 5.49/2.11  Timing (in seconds)
% 5.49/2.11  ----------------------
% 5.49/2.11  Preprocessing        : 0.31
% 5.49/2.11  Parsing              : 0.17
% 5.49/2.11  CNF conversion       : 0.02
% 5.49/2.11  Main loop            : 1.03
% 5.49/2.11  Inferencing          : 0.32
% 5.49/2.11  Reduction            : 0.43
% 5.49/2.11  Demodulation         : 0.35
% 5.49/2.11  BG Simplification    : 0.03
% 5.49/2.11  Subsumption          : 0.18
% 5.49/2.11  Abstraction          : 0.05
% 5.49/2.11  MUC search           : 0.00
% 5.49/2.11  Cooper               : 0.00
% 5.49/2.11  Total                : 1.37
% 5.49/2.11  Index Insertion      : 0.00
% 5.49/2.11  Index Deletion       : 0.00
% 5.49/2.11  Index Matching       : 0.00
% 5.49/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
