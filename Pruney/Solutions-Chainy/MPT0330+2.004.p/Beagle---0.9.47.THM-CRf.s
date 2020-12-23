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
% DateTime   : Thu Dec  3 09:54:40 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 107 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 140 expanded)
%              Number of equality atoms :   20 (  51 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_83,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_40,plain,(
    ! [A_39,C_41,B_40] : k2_xboole_0(k2_zfmisc_1(A_39,C_41),k2_zfmisc_1(B_40,C_41)) = k2_zfmisc_1(k2_xboole_0(A_39,B_40),C_41) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1375,plain,(
    ! [A_155,C_156,B_157,D_158] :
      ( r1_tarski(k2_xboole_0(A_155,C_156),k2_xboole_0(B_157,D_158))
      | ~ r1_tarski(C_156,D_158)
      | ~ r1_tarski(A_155,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3262,plain,(
    ! [A_215,C_216,A_217] :
      ( r1_tarski(k2_xboole_0(A_215,C_216),A_217)
      | ~ r1_tarski(C_216,A_217)
      | ~ r1_tarski(A_215,A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1375])).

tff(c_28,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_220,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_239,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(k2_xboole_0(A_26,B_27),A_26) ) ),
    inference(resolution,[status(thm)],[c_28,c_220])).

tff(c_3276,plain,(
    ! [A_217,C_216] :
      ( k2_xboole_0(A_217,C_216) = A_217
      | ~ r1_tarski(C_216,A_217)
      | ~ r1_tarski(A_217,A_217) ) ),
    inference(resolution,[status(thm)],[c_3262,c_239])).

tff(c_3876,plain,(
    ! [A_224,C_225] :
      ( k2_xboole_0(A_224,C_225) = A_224
      | ~ r1_tarski(C_225,A_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3276])).

tff(c_3977,plain,(
    k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_1') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_3876])).

tff(c_34,plain,(
    ! [B_34,A_33] : k2_tarski(B_34,A_33) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_101,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_125,plain,(
    ! [B_57,A_58] : k3_tarski(k2_tarski(B_57,A_58)) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_101])).

tff(c_38,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_131,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_38])).

tff(c_384,plain,(
    ! [A_92,C_93,B_94] :
      ( r1_tarski(A_92,C_93)
      | ~ r1_tarski(k2_xboole_0(A_92,B_94),C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_410,plain,(
    ! [A_95,B_96,B_97] : r1_tarski(A_95,k2_xboole_0(k2_xboole_0(A_95,B_96),B_97)) ),
    inference(resolution,[status(thm)],[c_28,c_384])).

tff(c_426,plain,(
    ! [B_57,A_58,B_97] : r1_tarski(B_57,k2_xboole_0(k2_xboole_0(A_58,B_57),B_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_410])).

tff(c_4763,plain,(
    ! [B_245] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),B_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3977,c_426])).

tff(c_4793,plain,(
    ! [B_40] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_40),'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4763])).

tff(c_46,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3978,plain,(
    k2_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),'#skF_2') = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_3876])).

tff(c_4358,plain,(
    ! [B_236] : r1_tarski('#skF_2',k2_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),B_236)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3978,c_426])).

tff(c_4489,plain,(
    ! [B_239] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_5',B_239),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4358])).

tff(c_4517,plain,(
    ! [A_58] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0(A_58,'#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_4489])).

tff(c_42,plain,(
    ! [C_41,A_39,B_40] : k2_xboole_0(k2_zfmisc_1(C_41,A_39),k2_zfmisc_1(C_41,B_40)) = k2_zfmisc_1(C_41,k2_xboole_0(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8141,plain,(
    ! [C_296,B_293,C_294,A_295,A_292] :
      ( r1_tarski(k2_xboole_0(A_295,C_296),k2_zfmisc_1(C_294,k2_xboole_0(A_292,B_293)))
      | ~ r1_tarski(C_296,k2_zfmisc_1(C_294,B_293))
      | ~ r1_tarski(A_295,k2_zfmisc_1(C_294,A_292)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1375])).

tff(c_44,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8162,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6'))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_8141,c_44])).

tff(c_8292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4793,c_4517,c_8162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:49:44 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.98/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.23  
% 5.98/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.23  %$ r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.98/2.23  
% 5.98/2.23  %Foreground sorts:
% 5.98/2.23  
% 5.98/2.23  
% 5.98/2.23  %Background operators:
% 5.98/2.23  
% 5.98/2.23  
% 5.98/2.23  %Foreground operators:
% 5.98/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.98/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.98/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.98/2.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.98/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.98/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.98/2.23  tff('#skF_5', type, '#skF_5': $i).
% 5.98/2.23  tff('#skF_6', type, '#skF_6': $i).
% 5.98/2.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.98/2.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.98/2.23  tff('#skF_2', type, '#skF_2': $i).
% 5.98/2.23  tff('#skF_3', type, '#skF_3': $i).
% 5.98/2.23  tff('#skF_1', type, '#skF_1': $i).
% 5.98/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.98/2.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.98/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.98/2.23  tff('#skF_4', type, '#skF_4': $i).
% 5.98/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.98/2.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.98/2.23  
% 5.98/2.24  tff(f_87, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 5.98/2.24  tff(f_94, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 5.98/2.24  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.98/2.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.98/2.24  tff(f_53, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 5.98/2.24  tff(f_69, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.98/2.24  tff(f_79, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.98/2.24  tff(f_83, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.98/2.24  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.98/2.24  tff(c_40, plain, (![A_39, C_41, B_40]: (k2_xboole_0(k2_zfmisc_1(A_39, C_41), k2_zfmisc_1(B_40, C_41))=k2_zfmisc_1(k2_xboole_0(A_39, B_40), C_41))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.98/2.24  tff(c_48, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.98/2.24  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.98/2.24  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.98/2.24  tff(c_1375, plain, (![A_155, C_156, B_157, D_158]: (r1_tarski(k2_xboole_0(A_155, C_156), k2_xboole_0(B_157, D_158)) | ~r1_tarski(C_156, D_158) | ~r1_tarski(A_155, B_157))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.98/2.24  tff(c_3262, plain, (![A_215, C_216, A_217]: (r1_tarski(k2_xboole_0(A_215, C_216), A_217) | ~r1_tarski(C_216, A_217) | ~r1_tarski(A_215, A_217))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1375])).
% 5.98/2.24  tff(c_28, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.98/2.24  tff(c_220, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.98/2.24  tff(c_239, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(k2_xboole_0(A_26, B_27), A_26))), inference(resolution, [status(thm)], [c_28, c_220])).
% 5.98/2.24  tff(c_3276, plain, (![A_217, C_216]: (k2_xboole_0(A_217, C_216)=A_217 | ~r1_tarski(C_216, A_217) | ~r1_tarski(A_217, A_217))), inference(resolution, [status(thm)], [c_3262, c_239])).
% 5.98/2.24  tff(c_3876, plain, (![A_224, C_225]: (k2_xboole_0(A_224, C_225)=A_224 | ~r1_tarski(C_225, A_224))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3276])).
% 5.98/2.24  tff(c_3977, plain, (k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_1')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_3876])).
% 5.98/2.24  tff(c_34, plain, (![B_34, A_33]: (k2_tarski(B_34, A_33)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.98/2.24  tff(c_101, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.98/2.24  tff(c_125, plain, (![B_57, A_58]: (k3_tarski(k2_tarski(B_57, A_58))=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_34, c_101])).
% 5.98/2.24  tff(c_38, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.98/2.24  tff(c_131, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_125, c_38])).
% 5.98/2.24  tff(c_384, plain, (![A_92, C_93, B_94]: (r1_tarski(A_92, C_93) | ~r1_tarski(k2_xboole_0(A_92, B_94), C_93))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.24  tff(c_410, plain, (![A_95, B_96, B_97]: (r1_tarski(A_95, k2_xboole_0(k2_xboole_0(A_95, B_96), B_97)))), inference(resolution, [status(thm)], [c_28, c_384])).
% 5.98/2.24  tff(c_426, plain, (![B_57, A_58, B_97]: (r1_tarski(B_57, k2_xboole_0(k2_xboole_0(A_58, B_57), B_97)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_410])).
% 5.98/2.24  tff(c_4763, plain, (![B_245]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), B_245)))), inference(superposition, [status(thm), theory('equality')], [c_3977, c_426])).
% 5.98/2.24  tff(c_4793, plain, (![B_40]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_40), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4763])).
% 5.98/2.24  tff(c_46, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.98/2.24  tff(c_3978, plain, (k2_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), '#skF_2')=k2_zfmisc_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_3876])).
% 5.98/2.24  tff(c_4358, plain, (![B_236]: (r1_tarski('#skF_2', k2_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), B_236)))), inference(superposition, [status(thm), theory('equality')], [c_3978, c_426])).
% 5.98/2.24  tff(c_4489, plain, (![B_239]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_5', B_239), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4358])).
% 5.98/2.24  tff(c_4517, plain, (![A_58]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0(A_58, '#skF_5'), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_131, c_4489])).
% 5.98/2.24  tff(c_42, plain, (![C_41, A_39, B_40]: (k2_xboole_0(k2_zfmisc_1(C_41, A_39), k2_zfmisc_1(C_41, B_40))=k2_zfmisc_1(C_41, k2_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.98/2.24  tff(c_8141, plain, (![C_296, B_293, C_294, A_295, A_292]: (r1_tarski(k2_xboole_0(A_295, C_296), k2_zfmisc_1(C_294, k2_xboole_0(A_292, B_293))) | ~r1_tarski(C_296, k2_zfmisc_1(C_294, B_293)) | ~r1_tarski(A_295, k2_zfmisc_1(C_294, A_292)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1375])).
% 5.98/2.24  tff(c_44, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.98/2.24  tff(c_8162, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_8141, c_44])).
% 5.98/2.24  tff(c_8292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4793, c_4517, c_8162])).
% 5.98/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.24  
% 5.98/2.24  Inference rules
% 5.98/2.24  ----------------------
% 5.98/2.24  #Ref     : 0
% 5.98/2.24  #Sup     : 2018
% 5.98/2.24  #Fact    : 0
% 5.98/2.24  #Define  : 0
% 5.98/2.24  #Split   : 3
% 5.98/2.24  #Chain   : 0
% 5.98/2.24  #Close   : 0
% 5.98/2.24  
% 5.98/2.24  Ordering : KBO
% 5.98/2.24  
% 5.98/2.24  Simplification rules
% 5.98/2.24  ----------------------
% 5.98/2.24  #Subsume      : 167
% 5.98/2.24  #Demod        : 1441
% 5.98/2.24  #Tautology    : 1174
% 5.98/2.24  #SimpNegUnit  : 0
% 5.98/2.24  #BackRed      : 3
% 5.98/2.24  
% 5.98/2.24  #Partial instantiations: 0
% 5.98/2.24  #Strategies tried      : 1
% 5.98/2.24  
% 5.98/2.24  Timing (in seconds)
% 5.98/2.24  ----------------------
% 5.98/2.24  Preprocessing        : 0.31
% 5.98/2.24  Parsing              : 0.17
% 5.98/2.24  CNF conversion       : 0.02
% 5.98/2.24  Main loop            : 1.17
% 5.98/2.24  Inferencing          : 0.33
% 5.98/2.24  Reduction            : 0.53
% 5.98/2.24  Demodulation         : 0.44
% 5.98/2.24  BG Simplification    : 0.04
% 5.98/2.24  Subsumption          : 0.21
% 5.98/2.24  Abstraction          : 0.05
% 5.98/2.24  MUC search           : 0.00
% 5.98/2.24  Cooper               : 0.00
% 5.98/2.24  Total                : 1.52
% 5.98/2.24  Index Insertion      : 0.00
% 5.98/2.24  Index Deletion       : 0.00
% 5.98/2.25  Index Matching       : 0.00
% 5.98/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
