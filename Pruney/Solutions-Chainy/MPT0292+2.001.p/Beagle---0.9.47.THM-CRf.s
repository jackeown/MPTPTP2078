%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:34 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   57 (  92 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 113 expanded)
%              Number of equality atoms :   22 (  50 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_48,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_117,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(B_40,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_24,plain,(
    ! [A_16,B_17] : k3_tarski(k2_tarski(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_143,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_24])).

tff(c_181,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_143])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_3'(A_18,B_19),A_18)
      | r1_tarski(k3_tarski(A_18),B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,k3_tarski(B_15))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_209,plain,(
    ! [A_47,B_48] :
      ( ~ r1_tarski('#skF_3'(A_47,B_48),B_48)
      | r1_tarski(k3_tarski(A_47),B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_352,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k3_tarski(A_63),k3_tarski(B_64))
      | ~ r2_hidden('#skF_3'(A_63,k3_tarski(B_64)),B_64) ) ),
    inference(resolution,[status(thm)],[c_22,c_209])).

tff(c_371,plain,(
    ! [A_65] : r1_tarski(k3_tarski(A_65),k3_tarski(A_65)) ),
    inference(resolution,[status(thm)],[c_28,c_352])).

tff(c_386,plain,(
    ! [A_16,B_17] : r1_tarski(k3_tarski(k2_tarski(A_16,B_17)),k2_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_371])).

tff(c_435,plain,(
    ! [A_67,B_68] : r1_tarski(k2_xboole_0(A_67,B_68),k2_xboole_0(A_67,B_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_386])).

tff(c_459,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,k3_xboole_0(A_3,B_4))) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_435])).

tff(c_484,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_459])).

tff(c_12,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_200,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_3'(A_45,B_46),A_45)
      | r1_tarski(k3_tarski(A_45),B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_613,plain,(
    ! [A_77,B_78] :
      ( r1_tarski('#skF_3'(k1_zfmisc_1(A_77),B_78),A_77)
      | r1_tarski(k3_tarski(k1_zfmisc_1(A_77)),B_78) ) ),
    inference(resolution,[status(thm)],[c_200,c_10])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( ~ r1_tarski('#skF_3'(A_18,B_19),B_19)
      | r1_tarski(k3_tarski(A_18),B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_627,plain,(
    ! [A_79] : r1_tarski(k3_tarski(k1_zfmisc_1(A_79)),A_79) ),
    inference(resolution,[status(thm)],[c_613,c_26])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_632,plain,(
    ! [A_80] : k2_xboole_0(k3_tarski(k1_zfmisc_1(A_80)),A_80) = A_80 ),
    inference(resolution,[status(thm)],[c_627,c_2])).

tff(c_214,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(A_49,k3_tarski(B_50)) = k3_tarski(B_50)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_22,c_85])).

tff(c_126,plain,(
    ! [B_40,A_39] : k2_xboole_0(B_40,A_39) = k2_xboole_0(A_39,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_24])).

tff(c_220,plain,(
    ! [B_50,A_49] :
      ( k2_xboole_0(k3_tarski(B_50),A_49) = k3_tarski(B_50)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_126])).

tff(c_850,plain,(
    ! [A_86] :
      ( k3_tarski(k1_zfmisc_1(A_86)) = A_86
      | ~ r2_hidden(A_86,k1_zfmisc_1(A_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_220])).

tff(c_854,plain,(
    ! [A_9] :
      ( k3_tarski(k1_zfmisc_1(A_9)) = A_9
      | ~ r1_tarski(A_9,A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_850])).

tff(c_857,plain,(
    ! [A_9] : k3_tarski(k1_zfmisc_1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_854])).

tff(c_30,plain,(
    k3_tarski(k1_zfmisc_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:25:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.36  
% 2.66/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.36  %$ r2_hidden > r1_tarski > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.66/1.36  
% 2.66/1.36  %Foreground sorts:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Background operators:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Foreground operators:
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.66/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.66/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.36  
% 2.66/1.37  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.66/1.37  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.66/1.37  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.66/1.37  tff(f_48, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.66/1.37  tff(f_55, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.66/1.37  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.66/1.37  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.66/1.37  tff(f_58, negated_conjecture, ~(![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.66/1.37  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.37  tff(c_85, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.37  tff(c_93, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_85])).
% 2.66/1.37  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.66/1.37  tff(c_65, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.66/1.37  tff(c_117, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(B_40, A_39))), inference(superposition, [status(thm), theory('equality')], [c_6, c_65])).
% 2.66/1.37  tff(c_24, plain, (![A_16, B_17]: (k3_tarski(k2_tarski(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.66/1.37  tff(c_143, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_117, c_24])).
% 2.66/1.37  tff(c_181, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_93, c_143])).
% 2.66/1.37  tff(c_28, plain, (![A_18, B_19]: (r2_hidden('#skF_3'(A_18, B_19), A_18) | r1_tarski(k3_tarski(A_18), B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.37  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, k3_tarski(B_15)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.37  tff(c_209, plain, (![A_47, B_48]: (~r1_tarski('#skF_3'(A_47, B_48), B_48) | r1_tarski(k3_tarski(A_47), B_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.37  tff(c_352, plain, (![A_63, B_64]: (r1_tarski(k3_tarski(A_63), k3_tarski(B_64)) | ~r2_hidden('#skF_3'(A_63, k3_tarski(B_64)), B_64))), inference(resolution, [status(thm)], [c_22, c_209])).
% 2.66/1.37  tff(c_371, plain, (![A_65]: (r1_tarski(k3_tarski(A_65), k3_tarski(A_65)))), inference(resolution, [status(thm)], [c_28, c_352])).
% 2.66/1.37  tff(c_386, plain, (![A_16, B_17]: (r1_tarski(k3_tarski(k2_tarski(A_16, B_17)), k2_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_371])).
% 2.66/1.37  tff(c_435, plain, (![A_67, B_68]: (r1_tarski(k2_xboole_0(A_67, B_68), k2_xboole_0(A_67, B_68)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_386])).
% 2.66/1.37  tff(c_459, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))))), inference(superposition, [status(thm), theory('equality')], [c_181, c_435])).
% 2.66/1.37  tff(c_484, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_459])).
% 2.66/1.37  tff(c_12, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.66/1.37  tff(c_200, plain, (![A_45, B_46]: (r2_hidden('#skF_3'(A_45, B_46), A_45) | r1_tarski(k3_tarski(A_45), B_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.37  tff(c_10, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.66/1.37  tff(c_613, plain, (![A_77, B_78]: (r1_tarski('#skF_3'(k1_zfmisc_1(A_77), B_78), A_77) | r1_tarski(k3_tarski(k1_zfmisc_1(A_77)), B_78))), inference(resolution, [status(thm)], [c_200, c_10])).
% 2.66/1.37  tff(c_26, plain, (![A_18, B_19]: (~r1_tarski('#skF_3'(A_18, B_19), B_19) | r1_tarski(k3_tarski(A_18), B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.37  tff(c_627, plain, (![A_79]: (r1_tarski(k3_tarski(k1_zfmisc_1(A_79)), A_79))), inference(resolution, [status(thm)], [c_613, c_26])).
% 2.66/1.37  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.37  tff(c_632, plain, (![A_80]: (k2_xboole_0(k3_tarski(k1_zfmisc_1(A_80)), A_80)=A_80)), inference(resolution, [status(thm)], [c_627, c_2])).
% 2.66/1.37  tff(c_214, plain, (![A_49, B_50]: (k2_xboole_0(A_49, k3_tarski(B_50))=k3_tarski(B_50) | ~r2_hidden(A_49, B_50))), inference(resolution, [status(thm)], [c_22, c_85])).
% 2.66/1.37  tff(c_126, plain, (![B_40, A_39]: (k2_xboole_0(B_40, A_39)=k2_xboole_0(A_39, B_40))), inference(superposition, [status(thm), theory('equality')], [c_117, c_24])).
% 2.66/1.37  tff(c_220, plain, (![B_50, A_49]: (k2_xboole_0(k3_tarski(B_50), A_49)=k3_tarski(B_50) | ~r2_hidden(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_214, c_126])).
% 2.66/1.37  tff(c_850, plain, (![A_86]: (k3_tarski(k1_zfmisc_1(A_86))=A_86 | ~r2_hidden(A_86, k1_zfmisc_1(A_86)))), inference(superposition, [status(thm), theory('equality')], [c_632, c_220])).
% 2.66/1.37  tff(c_854, plain, (![A_9]: (k3_tarski(k1_zfmisc_1(A_9))=A_9 | ~r1_tarski(A_9, A_9))), inference(resolution, [status(thm)], [c_12, c_850])).
% 2.66/1.37  tff(c_857, plain, (![A_9]: (k3_tarski(k1_zfmisc_1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_484, c_854])).
% 2.66/1.37  tff(c_30, plain, (k3_tarski(k1_zfmisc_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.66/1.37  tff(c_868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_857, c_30])).
% 2.66/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  Inference rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Ref     : 0
% 2.66/1.37  #Sup     : 194
% 2.66/1.37  #Fact    : 0
% 2.66/1.38  #Define  : 0
% 2.66/1.38  #Split   : 0
% 2.66/1.38  #Chain   : 0
% 2.66/1.38  #Close   : 0
% 2.66/1.38  
% 2.66/1.38  Ordering : KBO
% 2.66/1.38  
% 2.66/1.38  Simplification rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Subsume      : 12
% 2.66/1.38  #Demod        : 135
% 2.66/1.38  #Tautology    : 119
% 2.66/1.38  #SimpNegUnit  : 0
% 2.66/1.38  #BackRed      : 5
% 2.66/1.38  
% 2.66/1.38  #Partial instantiations: 0
% 2.66/1.38  #Strategies tried      : 1
% 2.66/1.38  
% 2.66/1.38  Timing (in seconds)
% 2.66/1.38  ----------------------
% 2.66/1.38  Preprocessing        : 0.29
% 2.66/1.38  Parsing              : 0.15
% 2.66/1.38  CNF conversion       : 0.02
% 2.66/1.38  Main loop            : 0.34
% 2.66/1.38  Inferencing          : 0.12
% 2.66/1.38  Reduction            : 0.13
% 2.66/1.38  Demodulation         : 0.10
% 2.66/1.38  BG Simplification    : 0.02
% 2.66/1.38  Subsumption          : 0.05
% 2.66/1.38  Abstraction          : 0.02
% 2.66/1.38  MUC search           : 0.00
% 2.66/1.38  Cooper               : 0.00
% 2.66/1.38  Total                : 0.66
% 2.66/1.38  Index Insertion      : 0.00
% 2.66/1.38  Index Deletion       : 0.00
% 2.66/1.38  Index Matching       : 0.00
% 2.66/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
