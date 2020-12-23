%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:26 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 130 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 254 expanded)
%              Number of equality atoms :   12 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)) = k1_zfmisc_1(k2_xboole_0(A,B))
       => r3_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_51,plain,(
    ! [A_19,B_20] :
      ( ~ r1_tarski(A_19,B_20)
      | r3_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    ~ r3_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_55,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_51,c_46])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    k2_xboole_0(k1_zfmisc_1('#skF_5'),k1_zfmisc_1('#skF_6')) = k1_zfmisc_1(k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_109,plain,(
    ! [D_40,B_41,A_42] :
      ( r2_hidden(D_40,B_41)
      | r2_hidden(D_40,A_42)
      | ~ r2_hidden(D_40,k2_xboole_0(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_136,plain,(
    ! [D_46] :
      ( r2_hidden(D_46,k1_zfmisc_1('#skF_6'))
      | r2_hidden(D_46,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(D_46,k1_zfmisc_1(k2_xboole_0('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_109])).

tff(c_278,plain,(
    ! [C_59] :
      ( r2_hidden(C_59,k1_zfmisc_1('#skF_6'))
      | r2_hidden(C_59,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski(C_59,k2_xboole_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_34,c_136])).

tff(c_32,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_307,plain,(
    ! [C_61] :
      ( r1_tarski(C_61,'#skF_5')
      | r2_hidden(C_61,k1_zfmisc_1('#skF_6'))
      | ~ r1_tarski(C_61,k2_xboole_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_278,c_32])).

tff(c_325,plain,(
    ! [C_62] :
      ( r1_tarski(C_62,'#skF_6')
      | r1_tarski(C_62,'#skF_5')
      | ~ r1_tarski(C_62,k2_xboole_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_307,c_32])).

tff(c_348,plain,
    ( r1_tarski(k2_xboole_0('#skF_5','#skF_6'),'#skF_6')
    | r1_tarski(k2_xboole_0('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_325])).

tff(c_349,plain,(
    r1_tarski(k2_xboole_0('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_80,plain,(
    ! [D_29,A_30,B_31] :
      ( ~ r2_hidden(D_29,A_30)
      | r2_hidden(D_29,k2_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_131,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k1_zfmisc_1('#skF_5'))
      | r2_hidden(D_45,k1_zfmisc_1(k2_xboole_0('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_80])).

tff(c_150,plain,(
    ! [D_47] :
      ( r1_tarski(D_47,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(D_47,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_131,c_32])).

tff(c_156,plain,(
    ! [C_48] :
      ( r1_tarski(C_48,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r1_tarski(C_48,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_150])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_159,plain,(
    ! [C_48] :
      ( k2_xboole_0('#skF_5','#skF_6') = C_48
      | ~ r1_tarski(k2_xboole_0('#skF_5','#skF_6'),C_48)
      | ~ r1_tarski(C_48,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_156,c_20])).

tff(c_352,plain,
    ( k2_xboole_0('#skF_5','#skF_6') = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_349,c_159])).

tff(c_360,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_352])).

tff(c_84,plain,(
    ! [D_32,B_33,A_34] :
      ( ~ r2_hidden(D_32,B_33)
      | r2_hidden(D_32,k2_xboole_0(A_34,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_104,plain,(
    ! [D_39] :
      ( ~ r2_hidden(D_39,k1_zfmisc_1('#skF_6'))
      | r2_hidden(D_39,k1_zfmisc_1(k2_xboole_0('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_84])).

tff(c_121,plain,(
    ! [D_43] :
      ( r1_tarski(D_43,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(D_43,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_104,c_32])).

tff(c_126,plain,(
    ! [C_15] :
      ( r1_tarski(C_15,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r1_tarski(C_15,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_121])).

tff(c_405,plain,(
    ! [C_66] :
      ( r1_tarski(C_66,'#skF_5')
      | ~ r1_tarski(C_66,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_126])).

tff(c_56,plain,(
    ! [B_21,A_22] :
      ( ~ r1_tarski(B_21,A_22)
      | r3_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_46])).

tff(c_410,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_405,c_60])).

tff(c_415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_410])).

tff(c_416,plain,(
    r1_tarski(k2_xboole_0('#skF_5','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_127,plain,(
    ! [C_44] :
      ( r1_tarski(C_44,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r1_tarski(C_44,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_121])).

tff(c_130,plain,(
    ! [C_44] :
      ( k2_xboole_0('#skF_5','#skF_6') = C_44
      | ~ r1_tarski(k2_xboole_0('#skF_5','#skF_6'),C_44)
      | ~ r1_tarski(C_44,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_127,c_20])).

tff(c_423,plain,
    ( k2_xboole_0('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_416,c_130])).

tff(c_429,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_423])).

tff(c_155,plain,(
    ! [C_15] :
      ( r1_tarski(C_15,k2_xboole_0('#skF_5','#skF_6'))
      | ~ r1_tarski(C_15,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_150])).

tff(c_474,plain,(
    ! [C_67] :
      ( r1_tarski(C_67,'#skF_6')
      | ~ r1_tarski(C_67,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_155])).

tff(c_484,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_474])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:00:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.34  
% 2.43/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.34  %$ r3_xboole_0 > r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.43/1.34  
% 2.43/1.34  %Foreground sorts:
% 2.43/1.34  
% 2.43/1.34  
% 2.43/1.34  %Background operators:
% 2.43/1.34  
% 2.43/1.34  
% 2.43/1.34  %Foreground operators:
% 2.43/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.43/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.43/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.43/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.43/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.43/1.34  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 2.43/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.43/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.43/1.34  
% 2.43/1.35  tff(f_46, axiom, (![A, B]: (r3_xboole_0(A, B) <=> (r1_tarski(A, B) | r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_xboole_0)).
% 2.43/1.35  tff(f_60, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)) = k1_zfmisc_1(k2_xboole_0(A, B))) => r3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_zfmisc_1)).
% 2.43/1.35  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.43/1.35  tff(f_53, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.43/1.35  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.43/1.35  tff(c_51, plain, (![A_19, B_20]: (~r1_tarski(A_19, B_20) | r3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.43/1.35  tff(c_46, plain, (~r3_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.43/1.35  tff(c_55, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_51, c_46])).
% 2.43/1.35  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.43/1.35  tff(c_34, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.35  tff(c_48, plain, (k2_xboole_0(k1_zfmisc_1('#skF_5'), k1_zfmisc_1('#skF_6'))=k1_zfmisc_1(k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.43/1.35  tff(c_109, plain, (![D_40, B_41, A_42]: (r2_hidden(D_40, B_41) | r2_hidden(D_40, A_42) | ~r2_hidden(D_40, k2_xboole_0(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.43/1.35  tff(c_136, plain, (![D_46]: (r2_hidden(D_46, k1_zfmisc_1('#skF_6')) | r2_hidden(D_46, k1_zfmisc_1('#skF_5')) | ~r2_hidden(D_46, k1_zfmisc_1(k2_xboole_0('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_109])).
% 2.43/1.35  tff(c_278, plain, (![C_59]: (r2_hidden(C_59, k1_zfmisc_1('#skF_6')) | r2_hidden(C_59, k1_zfmisc_1('#skF_5')) | ~r1_tarski(C_59, k2_xboole_0('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_34, c_136])).
% 2.43/1.35  tff(c_32, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.35  tff(c_307, plain, (![C_61]: (r1_tarski(C_61, '#skF_5') | r2_hidden(C_61, k1_zfmisc_1('#skF_6')) | ~r1_tarski(C_61, k2_xboole_0('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_278, c_32])).
% 2.43/1.35  tff(c_325, plain, (![C_62]: (r1_tarski(C_62, '#skF_6') | r1_tarski(C_62, '#skF_5') | ~r1_tarski(C_62, k2_xboole_0('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_307, c_32])).
% 2.43/1.35  tff(c_348, plain, (r1_tarski(k2_xboole_0('#skF_5', '#skF_6'), '#skF_6') | r1_tarski(k2_xboole_0('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_24, c_325])).
% 2.43/1.35  tff(c_349, plain, (r1_tarski(k2_xboole_0('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_348])).
% 2.43/1.35  tff(c_80, plain, (![D_29, A_30, B_31]: (~r2_hidden(D_29, A_30) | r2_hidden(D_29, k2_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.43/1.35  tff(c_131, plain, (![D_45]: (~r2_hidden(D_45, k1_zfmisc_1('#skF_5')) | r2_hidden(D_45, k1_zfmisc_1(k2_xboole_0('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_80])).
% 2.43/1.35  tff(c_150, plain, (![D_47]: (r1_tarski(D_47, k2_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(D_47, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_131, c_32])).
% 2.43/1.35  tff(c_156, plain, (![C_48]: (r1_tarski(C_48, k2_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski(C_48, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_150])).
% 2.43/1.35  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.43/1.35  tff(c_159, plain, (![C_48]: (k2_xboole_0('#skF_5', '#skF_6')=C_48 | ~r1_tarski(k2_xboole_0('#skF_5', '#skF_6'), C_48) | ~r1_tarski(C_48, '#skF_5'))), inference(resolution, [status(thm)], [c_156, c_20])).
% 2.43/1.35  tff(c_352, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_5' | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_349, c_159])).
% 2.43/1.35  tff(c_360, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_352])).
% 2.43/1.35  tff(c_84, plain, (![D_32, B_33, A_34]: (~r2_hidden(D_32, B_33) | r2_hidden(D_32, k2_xboole_0(A_34, B_33)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.43/1.35  tff(c_104, plain, (![D_39]: (~r2_hidden(D_39, k1_zfmisc_1('#skF_6')) | r2_hidden(D_39, k1_zfmisc_1(k2_xboole_0('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_84])).
% 2.43/1.35  tff(c_121, plain, (![D_43]: (r1_tarski(D_43, k2_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(D_43, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_104, c_32])).
% 2.43/1.35  tff(c_126, plain, (![C_15]: (r1_tarski(C_15, k2_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski(C_15, '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_121])).
% 2.43/1.35  tff(c_405, plain, (![C_66]: (r1_tarski(C_66, '#skF_5') | ~r1_tarski(C_66, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_360, c_126])).
% 2.43/1.35  tff(c_56, plain, (![B_21, A_22]: (~r1_tarski(B_21, A_22) | r3_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.43/1.35  tff(c_60, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_46])).
% 2.43/1.35  tff(c_410, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_405, c_60])).
% 2.43/1.35  tff(c_415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_410])).
% 2.43/1.35  tff(c_416, plain, (r1_tarski(k2_xboole_0('#skF_5', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_348])).
% 2.43/1.35  tff(c_127, plain, (![C_44]: (r1_tarski(C_44, k2_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski(C_44, '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_121])).
% 2.43/1.35  tff(c_130, plain, (![C_44]: (k2_xboole_0('#skF_5', '#skF_6')=C_44 | ~r1_tarski(k2_xboole_0('#skF_5', '#skF_6'), C_44) | ~r1_tarski(C_44, '#skF_6'))), inference(resolution, [status(thm)], [c_127, c_20])).
% 2.43/1.35  tff(c_423, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_416, c_130])).
% 2.43/1.35  tff(c_429, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_423])).
% 2.43/1.35  tff(c_155, plain, (![C_15]: (r1_tarski(C_15, k2_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski(C_15, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_150])).
% 2.43/1.35  tff(c_474, plain, (![C_67]: (r1_tarski(C_67, '#skF_6') | ~r1_tarski(C_67, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_155])).
% 2.43/1.35  tff(c_484, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_474])).
% 2.43/1.35  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_484])).
% 2.43/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.35  
% 2.43/1.35  Inference rules
% 2.43/1.35  ----------------------
% 2.43/1.35  #Ref     : 0
% 2.43/1.35  #Sup     : 90
% 2.43/1.35  #Fact    : 0
% 2.43/1.35  #Define  : 0
% 2.43/1.35  #Split   : 1
% 2.43/1.35  #Chain   : 0
% 2.43/1.35  #Close   : 0
% 2.43/1.35  
% 2.43/1.35  Ordering : KBO
% 2.43/1.35  
% 2.43/1.35  Simplification rules
% 2.43/1.35  ----------------------
% 2.43/1.35  #Subsume      : 11
% 2.43/1.35  #Demod        : 46
% 2.43/1.35  #Tautology    : 48
% 2.43/1.35  #SimpNegUnit  : 1
% 2.43/1.35  #BackRed      : 21
% 2.43/1.35  
% 2.43/1.35  #Partial instantiations: 0
% 2.43/1.35  #Strategies tried      : 1
% 2.43/1.35  
% 2.43/1.35  Timing (in seconds)
% 2.43/1.35  ----------------------
% 2.43/1.36  Preprocessing        : 0.28
% 2.43/1.36  Parsing              : 0.15
% 2.43/1.36  CNF conversion       : 0.02
% 2.43/1.36  Main loop            : 0.30
% 2.43/1.36  Inferencing          : 0.11
% 2.43/1.36  Reduction            : 0.08
% 2.43/1.36  Demodulation         : 0.05
% 2.43/1.36  BG Simplification    : 0.02
% 2.43/1.36  Subsumption          : 0.08
% 2.43/1.36  Abstraction          : 0.01
% 2.43/1.36  MUC search           : 0.00
% 2.43/1.36  Cooper               : 0.00
% 2.43/1.36  Total                : 0.62
% 2.43/1.36  Index Insertion      : 0.00
% 2.43/1.36  Index Deletion       : 0.00
% 2.43/1.36  Index Matching       : 0.00
% 2.43/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
