%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:56 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   54 (  91 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 136 expanded)
%              Number of equality atoms :   26 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_46,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_61,plain,(
    ! [B_35,A_36] :
      ( ~ r2_hidden(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [C_18] : ~ v1_xboole_0(k1_tarski(C_18)) ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_73,plain,(
    ! [A_40] :
      ( v1_xboole_0(A_40)
      | r2_hidden('#skF_1'(A_40),A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,(
    ! [A_14] :
      ( '#skF_1'(k1_tarski(A_14)) = A_14
      | v1_xboole_0(k1_tarski(A_14)) ) ),
    inference(resolution,[status(thm)],[c_73,c_20])).

tff(c_83,plain,(
    ! [A_14] : '#skF_1'(k1_tarski(A_14)) = A_14 ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_77])).

tff(c_48,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_201,plain,(
    ! [B_72,A_73] :
      ( k1_tarski(B_72) = A_73
      | k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,k1_tarski(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_218,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_201])).

tff(c_221,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_44,plain,(
    ! [B_30] : r1_tarski(k1_xboole_0,k1_tarski(B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_106,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_122,plain,(
    ! [B_30] : k4_xboole_0(k1_xboole_0,k1_tarski(B_30)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_106])).

tff(c_237,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_122])).

tff(c_254,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_22])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_182,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,B_67)
      | ~ r2_hidden(C_68,A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_996,plain,(
    ! [C_1211,B_1212,A_1213] :
      ( ~ r2_hidden(C_1211,B_1212)
      | ~ r2_hidden(C_1211,A_1213)
      | k4_xboole_0(A_1213,B_1212) != A_1213 ) ),
    inference(resolution,[status(thm)],[c_18,c_182])).

tff(c_1012,plain,(
    ! [A_1238] :
      ( ~ r2_hidden('#skF_5',A_1238)
      | k4_xboole_0(A_1238,k1_xboole_0) != A_1238 ) ),
    inference(resolution,[status(thm)],[c_254,c_996])).

tff(c_1015,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_254,c_1012])).

tff(c_1023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_1015])).

tff(c_1024,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_1045,plain,(
    '#skF_1'(k1_tarski('#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_83])).

tff(c_1068,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1045])).

tff(c_1070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1068])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.47  
% 2.81/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.81/1.47  
% 2.81/1.47  %Foreground sorts:
% 2.81/1.47  
% 2.81/1.47  
% 2.81/1.47  %Background operators:
% 2.81/1.47  
% 2.81/1.47  
% 2.81/1.47  %Foreground operators:
% 2.81/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.81/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.81/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.81/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.81/1.47  
% 2.81/1.48  tff(f_83, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.81/1.48  tff(f_64, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.81/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.81/1.48  tff(f_78, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.81/1.48  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.81/1.48  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.81/1.48  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.81/1.48  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.48  tff(c_22, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.48  tff(c_61, plain, (![B_35, A_36]: (~r2_hidden(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.48  tff(c_65, plain, (![C_18]: (~v1_xboole_0(k1_tarski(C_18)))), inference(resolution, [status(thm)], [c_22, c_61])).
% 2.81/1.48  tff(c_73, plain, (![A_40]: (v1_xboole_0(A_40) | r2_hidden('#skF_1'(A_40), A_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.48  tff(c_20, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.48  tff(c_77, plain, (![A_14]: ('#skF_1'(k1_tarski(A_14))=A_14 | v1_xboole_0(k1_tarski(A_14)))), inference(resolution, [status(thm)], [c_73, c_20])).
% 2.81/1.48  tff(c_83, plain, (![A_14]: ('#skF_1'(k1_tarski(A_14))=A_14)), inference(negUnitSimplification, [status(thm)], [c_65, c_77])).
% 2.81/1.48  tff(c_48, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.48  tff(c_201, plain, (![B_72, A_73]: (k1_tarski(B_72)=A_73 | k1_xboole_0=A_73 | ~r1_tarski(A_73, k1_tarski(B_72)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.81/1.48  tff(c_218, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_201])).
% 2.81/1.48  tff(c_221, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_218])).
% 2.81/1.48  tff(c_44, plain, (![B_30]: (r1_tarski(k1_xboole_0, k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.81/1.48  tff(c_106, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=k1_xboole_0 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.81/1.48  tff(c_122, plain, (![B_30]: (k4_xboole_0(k1_xboole_0, k1_tarski(B_30))=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_106])).
% 2.81/1.48  tff(c_237, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_221, c_122])).
% 2.81/1.48  tff(c_254, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_221, c_22])).
% 2.81/1.48  tff(c_18, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.48  tff(c_182, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, B_67) | ~r2_hidden(C_68, A_66))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.81/1.48  tff(c_996, plain, (![C_1211, B_1212, A_1213]: (~r2_hidden(C_1211, B_1212) | ~r2_hidden(C_1211, A_1213) | k4_xboole_0(A_1213, B_1212)!=A_1213)), inference(resolution, [status(thm)], [c_18, c_182])).
% 2.81/1.48  tff(c_1012, plain, (![A_1238]: (~r2_hidden('#skF_5', A_1238) | k4_xboole_0(A_1238, k1_xboole_0)!=A_1238)), inference(resolution, [status(thm)], [c_254, c_996])).
% 2.81/1.48  tff(c_1015, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_254, c_1012])).
% 2.81/1.48  tff(c_1023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_237, c_1015])).
% 2.81/1.48  tff(c_1024, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_218])).
% 2.81/1.48  tff(c_1045, plain, ('#skF_1'(k1_tarski('#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1024, c_83])).
% 2.81/1.48  tff(c_1068, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1045])).
% 2.81/1.48  tff(c_1070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1068])).
% 2.81/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.48  
% 2.81/1.48  Inference rules
% 2.81/1.48  ----------------------
% 2.81/1.48  #Ref     : 0
% 2.81/1.48  #Sup     : 155
% 2.81/1.48  #Fact    : 0
% 2.81/1.48  #Define  : 0
% 2.81/1.48  #Split   : 2
% 2.81/1.48  #Chain   : 0
% 2.81/1.48  #Close   : 0
% 2.81/1.48  
% 2.81/1.48  Ordering : KBO
% 2.81/1.48  
% 2.81/1.48  Simplification rules
% 2.81/1.48  ----------------------
% 2.81/1.48  #Subsume      : 6
% 2.81/1.48  #Demod        : 34
% 2.81/1.48  #Tautology    : 67
% 2.81/1.48  #SimpNegUnit  : 5
% 2.81/1.48  #BackRed      : 5
% 2.81/1.48  
% 2.81/1.48  #Partial instantiations: 611
% 2.81/1.48  #Strategies tried      : 1
% 2.81/1.48  
% 2.81/1.48  Timing (in seconds)
% 2.81/1.48  ----------------------
% 2.81/1.48  Preprocessing        : 0.29
% 2.81/1.48  Parsing              : 0.15
% 2.81/1.48  CNF conversion       : 0.02
% 2.81/1.48  Main loop            : 0.39
% 2.81/1.48  Inferencing          : 0.21
% 2.81/1.49  Reduction            : 0.08
% 2.81/1.49  Demodulation         : 0.05
% 2.81/1.49  BG Simplification    : 0.02
% 2.81/1.49  Subsumption          : 0.04
% 2.81/1.49  Abstraction          : 0.02
% 2.81/1.49  MUC search           : 0.00
% 2.81/1.49  Cooper               : 0.00
% 2.81/1.49  Total                : 0.72
% 2.81/1.49  Index Insertion      : 0.00
% 2.81/1.49  Index Deletion       : 0.00
% 2.81/1.49  Index Matching       : 0.00
% 2.81/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
