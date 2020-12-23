%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:38 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   58 (  96 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 ( 131 expanded)
%              Number of equality atoms :   25 (  51 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_60,axiom,(
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

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_42,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [C_19] : r2_hidden(C_19,k1_tarski(C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_55,plain,(
    ! [B_32,A_33] :
      ( ~ r2_hidden(B_32,A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [C_19] : ~ v1_xboole_0(k1_tarski(C_19)) ),
    inference(resolution,[status(thm)],[c_20,c_55])).

tff(c_76,plain,(
    ! [A_38] :
      ( v1_xboole_0(A_38)
      | r2_hidden('#skF_1'(A_38),A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    ! [A_15] :
      ( '#skF_1'(k1_tarski(A_15)) = A_15
      | v1_xboole_0(k1_tarski(A_15)) ) ),
    inference(resolution,[status(thm)],[c_76,c_18])).

tff(c_86,plain,(
    ! [A_15] : '#skF_1'(k1_tarski(A_15)) = A_15 ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_80])).

tff(c_12,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_151,plain,(
    ! [B_53] : k3_xboole_0(k1_xboole_0,B_53) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_12])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_122,plain,(
    ! [A_46,B_47] :
      ( ~ r1_xboole_0(A_46,B_47)
      | v1_xboole_0(k3_xboole_0(A_46,B_47)) ) ),
    inference(resolution,[status(thm)],[c_4,c_117])).

tff(c_156,plain,(
    ! [B_53] :
      ( ~ r1_xboole_0(k1_xboole_0,B_53)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_122])).

tff(c_176,plain,(
    ! [B_57] : ~ r1_xboole_0(k1_xboole_0,B_57) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_180,plain,(
    ! [B_14] : k4_xboole_0(k1_xboole_0,B_14) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_176])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_180])).

tff(c_185,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_44,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_186,plain,(
    ! [B_58,A_59] :
      ( k1_tarski(B_58) = A_59
      | k1_xboole_0 = A_59
      | ~ r1_tarski(A_59,k1_tarski(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_198,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_186])).

tff(c_209,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_223,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_59])).

tff(c_240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_223])).

tff(c_241,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_252,plain,(
    '#skF_1'(k1_tarski('#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_86])).

tff(c_272,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_252])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.99/1.24  
% 1.99/1.24  %Foreground sorts:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Background operators:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Foreground operators:
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.99/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.99/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.24  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.99/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.99/1.24  
% 1.99/1.25  tff(f_77, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.99/1.25  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.99/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.99/1.25  tff(f_49, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.99/1.25  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.99/1.25  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.99/1.25  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.99/1.25  tff(f_72, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.99/1.25  tff(c_42, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.99/1.25  tff(c_20, plain, (![C_19]: (r2_hidden(C_19, k1_tarski(C_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.25  tff(c_55, plain, (![B_32, A_33]: (~r2_hidden(B_32, A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.25  tff(c_59, plain, (![C_19]: (~v1_xboole_0(k1_tarski(C_19)))), inference(resolution, [status(thm)], [c_20, c_55])).
% 1.99/1.25  tff(c_76, plain, (![A_38]: (v1_xboole_0(A_38) | r2_hidden('#skF_1'(A_38), A_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.25  tff(c_18, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.25  tff(c_80, plain, (![A_15]: ('#skF_1'(k1_tarski(A_15))=A_15 | v1_xboole_0(k1_tarski(A_15)))), inference(resolution, [status(thm)], [c_76, c_18])).
% 1.99/1.25  tff(c_86, plain, (![A_15]: ('#skF_1'(k1_tarski(A_15))=A_15)), inference(negUnitSimplification, [status(thm)], [c_59, c_80])).
% 1.99/1.25  tff(c_12, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.25  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k4_xboole_0(A_13, B_14)!=A_13)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.25  tff(c_124, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.25  tff(c_151, plain, (![B_53]: (k3_xboole_0(k1_xboole_0, B_53)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_124, c_12])).
% 1.99/1.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.25  tff(c_117, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.25  tff(c_122, plain, (![A_46, B_47]: (~r1_xboole_0(A_46, B_47) | v1_xboole_0(k3_xboole_0(A_46, B_47)))), inference(resolution, [status(thm)], [c_4, c_117])).
% 1.99/1.25  tff(c_156, plain, (![B_53]: (~r1_xboole_0(k1_xboole_0, B_53) | v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_151, c_122])).
% 1.99/1.25  tff(c_176, plain, (![B_57]: (~r1_xboole_0(k1_xboole_0, B_57))), inference(splitLeft, [status(thm)], [c_156])).
% 1.99/1.25  tff(c_180, plain, (![B_14]: (k4_xboole_0(k1_xboole_0, B_14)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_176])).
% 1.99/1.25  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_180])).
% 1.99/1.25  tff(c_185, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_156])).
% 1.99/1.25  tff(c_44, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.99/1.25  tff(c_186, plain, (![B_58, A_59]: (k1_tarski(B_58)=A_59 | k1_xboole_0=A_59 | ~r1_tarski(A_59, k1_tarski(B_58)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.25  tff(c_198, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_186])).
% 1.99/1.25  tff(c_209, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_198])).
% 1.99/1.25  tff(c_223, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_209, c_59])).
% 1.99/1.25  tff(c_240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_223])).
% 1.99/1.25  tff(c_241, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_198])).
% 1.99/1.25  tff(c_252, plain, ('#skF_1'(k1_tarski('#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_241, c_86])).
% 1.99/1.25  tff(c_272, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_252])).
% 1.99/1.25  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_272])).
% 1.99/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  Inference rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Ref     : 0
% 1.99/1.25  #Sup     : 53
% 1.99/1.25  #Fact    : 0
% 1.99/1.25  #Define  : 0
% 1.99/1.25  #Split   : 3
% 1.99/1.25  #Chain   : 0
% 1.99/1.25  #Close   : 0
% 1.99/1.25  
% 1.99/1.25  Ordering : KBO
% 1.99/1.25  
% 1.99/1.25  Simplification rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Subsume      : 2
% 1.99/1.25  #Demod        : 15
% 1.99/1.25  #Tautology    : 27
% 1.99/1.25  #SimpNegUnit  : 3
% 1.99/1.25  #BackRed      : 3
% 1.99/1.25  
% 1.99/1.25  #Partial instantiations: 0
% 1.99/1.25  #Strategies tried      : 1
% 1.99/1.25  
% 1.99/1.25  Timing (in seconds)
% 1.99/1.25  ----------------------
% 1.99/1.25  Preprocessing        : 0.29
% 1.99/1.25  Parsing              : 0.15
% 1.99/1.25  CNF conversion       : 0.02
% 1.99/1.25  Main loop            : 0.15
% 1.99/1.25  Inferencing          : 0.05
% 1.99/1.25  Reduction            : 0.05
% 1.99/1.25  Demodulation         : 0.03
% 1.99/1.25  BG Simplification    : 0.01
% 1.99/1.25  Subsumption          : 0.02
% 1.99/1.25  Abstraction          : 0.01
% 1.99/1.25  MUC search           : 0.00
% 1.99/1.25  Cooper               : 0.00
% 1.99/1.25  Total                : 0.47
% 1.99/1.25  Index Insertion      : 0.00
% 1.99/1.25  Index Deletion       : 0.00
% 1.99/1.25  Index Matching       : 0.00
% 1.99/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
