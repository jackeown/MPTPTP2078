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
% DateTime   : Thu Dec  3 09:53:36 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   52 (  53 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  61 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_45,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(c_40,plain,(
    ! [A_30] : r1_tarski(k1_tarski(A_30),k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_110,plain,(
    ! [A_59,B_60,C_61] : k2_enumset1(A_59,A_59,B_60,C_61) = k1_enumset1(A_59,B_60,C_61) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_18,B_19] : k2_enumset1(A_18,A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_132,plain,(
    ! [B_64,C_65] : k1_enumset1(B_64,B_64,C_65) = k2_tarski(B_64,C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_18])).

tff(c_16,plain,(
    ! [A_17] : k1_enumset1(A_17,A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [C_66] : k2_tarski(C_66,C_66) = k1_tarski(C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_16])).

tff(c_36,plain,(
    ! [B_28,C_29,A_27] :
      ( r2_hidden(B_28,C_29)
      | ~ r1_tarski(k2_tarski(A_27,B_28),C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_170,plain,(
    ! [C_69,C_70] :
      ( r2_hidden(C_69,C_70)
      | ~ r1_tarski(k1_tarski(C_69),C_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_36])).

tff(c_179,plain,(
    ! [A_30] : r2_hidden(A_30,k1_zfmisc_1(A_30)) ),
    inference(resolution,[status(thm)],[c_40,c_170])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,k3_tarski(B_26))
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_126,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_3'(A_62,B_63),A_62)
      | r1_tarski(k3_tarski(A_62),B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [C_24,A_20] :
      ( r1_tarski(C_24,A_20)
      | ~ r2_hidden(C_24,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_889,plain,(
    ! [A_160,B_161] :
      ( r1_tarski('#skF_3'(k1_zfmisc_1(A_160),B_161),A_160)
      | r1_tarski(k3_tarski(k1_zfmisc_1(A_160)),B_161) ) ),
    inference(resolution,[status(thm)],[c_126,c_20])).

tff(c_42,plain,(
    ! [A_31,B_32] :
      ( ~ r1_tarski('#skF_3'(A_31,B_32),B_32)
      | r1_tarski(k3_tarski(A_31),B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_900,plain,(
    ! [A_162] : r1_tarski(k3_tarski(k1_zfmisc_1(A_162)),A_162) ),
    inference(resolution,[status(thm)],[c_889,c_42])).

tff(c_67,plain,(
    ! [A_47,B_48] :
      ( r2_xboole_0(A_47,B_48)
      | B_48 = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [B_48,A_47] :
      ( ~ r1_tarski(B_48,A_47)
      | B_48 = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_67,c_8])).

tff(c_904,plain,(
    ! [A_163] :
      ( k3_tarski(k1_zfmisc_1(A_163)) = A_163
      | ~ r1_tarski(A_163,k3_tarski(k1_zfmisc_1(A_163))) ) ),
    inference(resolution,[status(thm)],[c_900,c_78])).

tff(c_914,plain,(
    ! [A_25] :
      ( k3_tarski(k1_zfmisc_1(A_25)) = A_25
      | ~ r2_hidden(A_25,k1_zfmisc_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_32,c_904])).

tff(c_920,plain,(
    ! [A_25] : k3_tarski(k1_zfmisc_1(A_25)) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_914])).

tff(c_46,plain,(
    k3_tarski(k1_zfmisc_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.41  
% 2.82/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.41  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.82/1.41  
% 2.82/1.41  %Foreground sorts:
% 2.82/1.41  
% 2.82/1.41  
% 2.82/1.41  %Background operators:
% 2.82/1.41  
% 2.82/1.41  
% 2.82/1.41  %Foreground operators:
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.82/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.82/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.82/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.82/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.82/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.82/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.41  
% 2.82/1.42  tff(f_66, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 2.82/1.42  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.82/1.42  tff(f_47, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 2.82/1.42  tff(f_45, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 2.82/1.42  tff(f_64, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.82/1.42  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.82/1.42  tff(f_73, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.82/1.42  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.82/1.42  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.82/1.42  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.82/1.42  tff(f_76, negated_conjecture, ~(![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.82/1.42  tff(c_40, plain, (![A_30]: (r1_tarski(k1_tarski(A_30), k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.82/1.42  tff(c_110, plain, (![A_59, B_60, C_61]: (k2_enumset1(A_59, A_59, B_60, C_61)=k1_enumset1(A_59, B_60, C_61))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.82/1.42  tff(c_18, plain, (![A_18, B_19]: (k2_enumset1(A_18, A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.82/1.42  tff(c_132, plain, (![B_64, C_65]: (k1_enumset1(B_64, B_64, C_65)=k2_tarski(B_64, C_65))), inference(superposition, [status(thm), theory('equality')], [c_110, c_18])).
% 2.82/1.42  tff(c_16, plain, (![A_17]: (k1_enumset1(A_17, A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.82/1.42  tff(c_148, plain, (![C_66]: (k2_tarski(C_66, C_66)=k1_tarski(C_66))), inference(superposition, [status(thm), theory('equality')], [c_132, c_16])).
% 2.82/1.42  tff(c_36, plain, (![B_28, C_29, A_27]: (r2_hidden(B_28, C_29) | ~r1_tarski(k2_tarski(A_27, B_28), C_29))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.82/1.42  tff(c_170, plain, (![C_69, C_70]: (r2_hidden(C_69, C_70) | ~r1_tarski(k1_tarski(C_69), C_70))), inference(superposition, [status(thm), theory('equality')], [c_148, c_36])).
% 2.82/1.42  tff(c_179, plain, (![A_30]: (r2_hidden(A_30, k1_zfmisc_1(A_30)))), inference(resolution, [status(thm)], [c_40, c_170])).
% 2.82/1.42  tff(c_32, plain, (![A_25, B_26]: (r1_tarski(A_25, k3_tarski(B_26)) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.82/1.42  tff(c_126, plain, (![A_62, B_63]: (r2_hidden('#skF_3'(A_62, B_63), A_62) | r1_tarski(k3_tarski(A_62), B_63))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.82/1.42  tff(c_20, plain, (![C_24, A_20]: (r1_tarski(C_24, A_20) | ~r2_hidden(C_24, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.82/1.42  tff(c_889, plain, (![A_160, B_161]: (r1_tarski('#skF_3'(k1_zfmisc_1(A_160), B_161), A_160) | r1_tarski(k3_tarski(k1_zfmisc_1(A_160)), B_161))), inference(resolution, [status(thm)], [c_126, c_20])).
% 2.82/1.42  tff(c_42, plain, (![A_31, B_32]: (~r1_tarski('#skF_3'(A_31, B_32), B_32) | r1_tarski(k3_tarski(A_31), B_32))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.82/1.42  tff(c_900, plain, (![A_162]: (r1_tarski(k3_tarski(k1_zfmisc_1(A_162)), A_162))), inference(resolution, [status(thm)], [c_889, c_42])).
% 2.82/1.42  tff(c_67, plain, (![A_47, B_48]: (r2_xboole_0(A_47, B_48) | B_48=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.42  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.42  tff(c_78, plain, (![B_48, A_47]: (~r1_tarski(B_48, A_47) | B_48=A_47 | ~r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_67, c_8])).
% 2.82/1.42  tff(c_904, plain, (![A_163]: (k3_tarski(k1_zfmisc_1(A_163))=A_163 | ~r1_tarski(A_163, k3_tarski(k1_zfmisc_1(A_163))))), inference(resolution, [status(thm)], [c_900, c_78])).
% 2.82/1.42  tff(c_914, plain, (![A_25]: (k3_tarski(k1_zfmisc_1(A_25))=A_25 | ~r2_hidden(A_25, k1_zfmisc_1(A_25)))), inference(resolution, [status(thm)], [c_32, c_904])).
% 2.82/1.42  tff(c_920, plain, (![A_25]: (k3_tarski(k1_zfmisc_1(A_25))=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_914])).
% 2.82/1.42  tff(c_46, plain, (k3_tarski(k1_zfmisc_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.82/1.42  tff(c_945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_920, c_46])).
% 2.82/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.42  
% 2.82/1.42  Inference rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Ref     : 0
% 2.82/1.42  #Sup     : 175
% 2.82/1.42  #Fact    : 0
% 2.82/1.42  #Define  : 0
% 2.82/1.42  #Split   : 0
% 2.82/1.42  #Chain   : 0
% 2.82/1.42  #Close   : 0
% 2.82/1.42  
% 2.82/1.42  Ordering : KBO
% 2.82/1.42  
% 2.82/1.42  Simplification rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Subsume      : 6
% 2.82/1.42  #Demod        : 57
% 2.82/1.42  #Tautology    : 59
% 2.82/1.42  #SimpNegUnit  : 0
% 2.82/1.42  #BackRed      : 13
% 2.82/1.42  
% 2.82/1.42  #Partial instantiations: 0
% 2.82/1.42  #Strategies tried      : 1
% 2.82/1.42  
% 2.82/1.42  Timing (in seconds)
% 2.82/1.42  ----------------------
% 2.82/1.42  Preprocessing        : 0.30
% 2.82/1.42  Parsing              : 0.15
% 2.82/1.42  CNF conversion       : 0.02
% 2.82/1.42  Main loop            : 0.37
% 2.82/1.42  Inferencing          : 0.14
% 2.82/1.42  Reduction            : 0.11
% 2.82/1.42  Demodulation         : 0.09
% 2.82/1.42  BG Simplification    : 0.02
% 2.82/1.42  Subsumption          : 0.07
% 2.82/1.42  Abstraction          : 0.02
% 2.82/1.42  MUC search           : 0.00
% 2.82/1.42  Cooper               : 0.00
% 2.82/1.42  Total                : 0.69
% 2.82/1.43  Index Insertion      : 0.00
% 2.82/1.43  Index Deletion       : 0.00
% 2.82/1.43  Index Matching       : 0.00
% 2.82/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
