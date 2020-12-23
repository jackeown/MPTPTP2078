%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:40 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  80 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_495,plain,(
    ! [A_71,C_72,B_73] : k2_xboole_0(k2_zfmisc_1(A_71,C_72),k2_zfmisc_1(B_73,C_72)) = k2_zfmisc_1(k2_xboole_0(A_71,B_73),C_72) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_128,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_141,plain,(
    k3_xboole_0('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_194,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(k3_xboole_0(A_46,C_47),B_48)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_350,plain,(
    ! [B_60,A_61,B_62] :
      ( r1_tarski(k3_xboole_0(B_60,A_61),B_62)
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_194])).

tff(c_421,plain,(
    ! [B_68] :
      ( r1_tarski('#skF_1',B_68)
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_350])).

tff(c_451,plain,(
    ! [B_18] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),B_18)) ),
    inference(resolution,[status(thm)],[c_18,c_421])).

tff(c_506,plain,(
    ! [B_73] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_73),'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_451])).

tff(c_26,plain,(
    ! [A_25,C_27,B_26] : k2_xboole_0(k2_zfmisc_1(A_25,C_27),k2_zfmisc_1(B_26,C_27)) = k2_zfmisc_1(k2_xboole_0(A_25,B_26),C_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_104,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_171,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(B_45,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_104])).

tff(c_24,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_217,plain,(
    ! [B_49,A_50] : k2_xboole_0(B_49,A_50) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_24])).

tff(c_238,plain,(
    ! [A_50,B_49] : r1_tarski(A_50,k2_xboole_0(B_49,A_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_18])).

tff(c_32,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_143,plain,(
    k3_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_128])).

tff(c_936,plain,(
    ! [B_100] :
      ( r1_tarski('#skF_2',B_100)
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_350])).

tff(c_1016,plain,(
    ! [B_102] : r1_tarski('#skF_2',k2_xboole_0(B_102,k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_238,c_936])).

tff(c_1031,plain,(
    ! [A_25] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0(A_25,'#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1016])).

tff(c_28,plain,(
    ! [C_27,A_25,B_26] : k2_xboole_0(k2_zfmisc_1(C_27,A_25),k2_zfmisc_1(C_27,B_26)) = k2_zfmisc_1(C_27,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_850,plain,(
    ! [A_93,C_94,B_95,D_96] :
      ( r1_tarski(k2_xboole_0(A_93,C_94),k2_xboole_0(B_95,D_96))
      | ~ r1_tarski(C_94,D_96)
      | ~ r1_tarski(A_93,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3923,plain,(
    ! [B_200,C_197,C_198,A_196,A_199] :
      ( r1_tarski(k2_xboole_0(A_199,C_197),k2_zfmisc_1(C_198,k2_xboole_0(A_196,B_200)))
      | ~ r1_tarski(C_197,k2_zfmisc_1(C_198,B_200))
      | ~ r1_tarski(A_199,k2_zfmisc_1(C_198,A_196)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_850])).

tff(c_30,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3948,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6'))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_3923,c_30])).

tff(c_3994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_1031,c_3948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:59:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.92  
% 4.92/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.92  %$ r1_tarski > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.92/1.92  
% 4.92/1.92  %Foreground sorts:
% 4.92/1.92  
% 4.92/1.92  
% 4.92/1.92  %Background operators:
% 4.92/1.92  
% 4.92/1.92  
% 4.92/1.92  %Foreground operators:
% 4.92/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.92/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.92/1.92  tff('#skF_5', type, '#skF_5': $i).
% 4.92/1.92  tff('#skF_6', type, '#skF_6': $i).
% 4.92/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.92/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.92/1.92  tff('#skF_3', type, '#skF_3': $i).
% 4.92/1.92  tff('#skF_1', type, '#skF_1': $i).
% 4.92/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.92/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.92/1.92  tff('#skF_4', type, '#skF_4': $i).
% 4.92/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.92/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.92/1.92  
% 4.92/1.93  tff(f_65, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 4.92/1.93  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.92/1.93  tff(f_72, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 4.92/1.93  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.92/1.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.92/1.93  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 4.92/1.93  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.92/1.93  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.92/1.93  tff(f_43, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 4.92/1.93  tff(c_495, plain, (![A_71, C_72, B_73]: (k2_xboole_0(k2_zfmisc_1(A_71, C_72), k2_zfmisc_1(B_73, C_72))=k2_zfmisc_1(k2_xboole_0(A_71, B_73), C_72))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.92/1.93  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.92/1.93  tff(c_34, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.92/1.93  tff(c_128, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.92/1.93  tff(c_141, plain, (k3_xboole_0('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))='#skF_1'), inference(resolution, [status(thm)], [c_34, c_128])).
% 4.92/1.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.92/1.93  tff(c_194, plain, (![A_46, C_47, B_48]: (r1_tarski(k3_xboole_0(A_46, C_47), B_48) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.92/1.93  tff(c_350, plain, (![B_60, A_61, B_62]: (r1_tarski(k3_xboole_0(B_60, A_61), B_62) | ~r1_tarski(A_61, B_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_194])).
% 4.92/1.93  tff(c_421, plain, (![B_68]: (r1_tarski('#skF_1', B_68) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), B_68))), inference(superposition, [status(thm), theory('equality')], [c_141, c_350])).
% 4.92/1.93  tff(c_451, plain, (![B_18]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), B_18)))), inference(resolution, [status(thm)], [c_18, c_421])).
% 4.92/1.93  tff(c_506, plain, (![B_73]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_73), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_495, c_451])).
% 4.92/1.93  tff(c_26, plain, (![A_25, C_27, B_26]: (k2_xboole_0(k2_zfmisc_1(A_25, C_27), k2_zfmisc_1(B_26, C_27))=k2_zfmisc_1(k2_xboole_0(A_25, B_26), C_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.92/1.93  tff(c_20, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.92/1.93  tff(c_104, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.92/1.93  tff(c_171, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(B_45, A_44))), inference(superposition, [status(thm), theory('equality')], [c_20, c_104])).
% 4.92/1.93  tff(c_24, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.92/1.93  tff(c_217, plain, (![B_49, A_50]: (k2_xboole_0(B_49, A_50)=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_171, c_24])).
% 4.92/1.93  tff(c_238, plain, (![A_50, B_49]: (r1_tarski(A_50, k2_xboole_0(B_49, A_50)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_18])).
% 4.92/1.93  tff(c_32, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.92/1.93  tff(c_143, plain, (k3_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))='#skF_2'), inference(resolution, [status(thm)], [c_32, c_128])).
% 4.92/1.93  tff(c_936, plain, (![B_100]: (r1_tarski('#skF_2', B_100) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), B_100))), inference(superposition, [status(thm), theory('equality')], [c_143, c_350])).
% 4.92/1.93  tff(c_1016, plain, (![B_102]: (r1_tarski('#skF_2', k2_xboole_0(B_102, k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_238, c_936])).
% 4.92/1.93  tff(c_1031, plain, (![A_25]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0(A_25, '#skF_5'), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1016])).
% 4.92/1.93  tff(c_28, plain, (![C_27, A_25, B_26]: (k2_xboole_0(k2_zfmisc_1(C_27, A_25), k2_zfmisc_1(C_27, B_26))=k2_zfmisc_1(C_27, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.92/1.93  tff(c_850, plain, (![A_93, C_94, B_95, D_96]: (r1_tarski(k2_xboole_0(A_93, C_94), k2_xboole_0(B_95, D_96)) | ~r1_tarski(C_94, D_96) | ~r1_tarski(A_93, B_95))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.92/1.93  tff(c_3923, plain, (![B_200, C_197, C_198, A_196, A_199]: (r1_tarski(k2_xboole_0(A_199, C_197), k2_zfmisc_1(C_198, k2_xboole_0(A_196, B_200))) | ~r1_tarski(C_197, k2_zfmisc_1(C_198, B_200)) | ~r1_tarski(A_199, k2_zfmisc_1(C_198, A_196)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_850])).
% 4.92/1.93  tff(c_30, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.92/1.93  tff(c_3948, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_3923, c_30])).
% 4.92/1.93  tff(c_3994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_506, c_1031, c_3948])).
% 4.92/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.93  
% 4.92/1.93  Inference rules
% 4.92/1.93  ----------------------
% 4.92/1.93  #Ref     : 0
% 4.92/1.93  #Sup     : 1004
% 4.92/1.93  #Fact    : 0
% 4.92/1.93  #Define  : 0
% 4.92/1.93  #Split   : 4
% 4.92/1.93  #Chain   : 0
% 4.92/1.93  #Close   : 0
% 4.92/1.93  
% 4.92/1.93  Ordering : KBO
% 4.92/1.93  
% 4.92/1.93  Simplification rules
% 4.92/1.93  ----------------------
% 4.92/1.93  #Subsume      : 142
% 4.92/1.93  #Demod        : 226
% 4.92/1.93  #Tautology    : 393
% 4.92/1.93  #SimpNegUnit  : 0
% 4.92/1.93  #BackRed      : 0
% 4.92/1.93  
% 4.92/1.93  #Partial instantiations: 0
% 4.92/1.93  #Strategies tried      : 1
% 4.92/1.93  
% 4.92/1.93  Timing (in seconds)
% 4.92/1.93  ----------------------
% 4.92/1.94  Preprocessing        : 0.30
% 4.92/1.94  Parsing              : 0.16
% 4.92/1.94  CNF conversion       : 0.02
% 4.92/1.94  Main loop            : 0.86
% 4.92/1.94  Inferencing          : 0.27
% 4.92/1.94  Reduction            : 0.34
% 4.92/1.94  Demodulation         : 0.28
% 4.92/1.94  BG Simplification    : 0.03
% 4.92/1.94  Subsumption          : 0.16
% 4.92/1.94  Abstraction          : 0.04
% 4.92/1.94  MUC search           : 0.00
% 4.92/1.94  Cooper               : 0.00
% 4.92/1.94  Total                : 1.19
% 4.92/1.94  Index Insertion      : 0.00
% 4.92/1.94  Index Deletion       : 0.00
% 4.92/1.94  Index Matching       : 0.00
% 4.92/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
