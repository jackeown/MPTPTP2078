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
% DateTime   : Thu Dec  3 09:48:42 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   60 (  94 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 ( 122 expanded)
%              Number of equality atoms :   23 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(c_80,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_56,plain,(
    ! [C_25] : r2_hidden(C_25,k1_tarski(C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_82,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_283,plain,(
    ! [D_103,A_104,B_105] :
      ( r2_hidden(D_103,k4_xboole_0(A_104,B_105))
      | r2_hidden(D_103,B_105)
      | ~ r2_hidden(D_103,A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_301,plain,(
    ! [D_106] :
      ( r2_hidden(D_106,k1_xboole_0)
      | r2_hidden(D_106,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_106,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_283])).

tff(c_306,plain,
    ( r2_hidden('#skF_7',k1_xboole_0)
    | r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_56,c_301])).

tff(c_307,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_54,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_310,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_307,c_54])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_310])).

tff(c_315,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_28,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_207,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_219,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_207])).

tff(c_239,plain,(
    ! [A_89] : k4_xboole_0(A_89,A_89) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_219])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_248,plain,(
    ! [D_6,A_89] :
      ( r2_hidden(D_6,A_89)
      | ~ r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_6])).

tff(c_330,plain,(
    ! [A_89] : r2_hidden('#skF_7',A_89) ),
    inference(resolution,[status(thm)],[c_315,c_248])).

tff(c_335,plain,(
    ! [A_109] : r2_hidden('#skF_7',A_109) ),
    inference(resolution,[status(thm)],[c_315,c_248])).

tff(c_26,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_216,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_207])).

tff(c_224,plain,(
    ! [A_88] : k4_xboole_0(A_88,k1_xboole_0) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_216])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_233,plain,(
    ! [D_6,A_88] :
      ( ~ r2_hidden(D_6,k1_xboole_0)
      | ~ r2_hidden(D_6,A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_4])).

tff(c_345,plain,(
    ! [A_88] : ~ r2_hidden('#skF_7',A_88) ),
    inference(resolution,[status(thm)],[c_335,c_233])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_345])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 2.19/1.28  
% 2.19/1.28  %Foreground sorts:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Background operators:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Foreground operators:
% 2.19/1.28  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.19/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.19/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.19/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.19/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.19/1.28  
% 2.19/1.29  tff(f_86, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.19/1.29  tff(f_67, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.19/1.29  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.19/1.29  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.19/1.29  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.19/1.29  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.19/1.29  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.19/1.29  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.19/1.29  tff(c_80, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.29  tff(c_56, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(C_25)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.19/1.29  tff(c_82, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.29  tff(c_283, plain, (![D_103, A_104, B_105]: (r2_hidden(D_103, k4_xboole_0(A_104, B_105)) | r2_hidden(D_103, B_105) | ~r2_hidden(D_103, A_104))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.29  tff(c_301, plain, (![D_106]: (r2_hidden(D_106, k1_xboole_0) | r2_hidden(D_106, k1_tarski('#skF_8')) | ~r2_hidden(D_106, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_82, c_283])).
% 2.19/1.29  tff(c_306, plain, (r2_hidden('#skF_7', k1_xboole_0) | r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_301])).
% 2.19/1.29  tff(c_307, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(splitLeft, [status(thm)], [c_306])).
% 2.19/1.29  tff(c_54, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.19/1.29  tff(c_310, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_307, c_54])).
% 2.19/1.29  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_310])).
% 2.19/1.29  tff(c_315, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_306])).
% 2.19/1.29  tff(c_28, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.19/1.29  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.29  tff(c_207, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.29  tff(c_219, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_207])).
% 2.19/1.29  tff(c_239, plain, (![A_89]: (k4_xboole_0(A_89, A_89)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_219])).
% 2.19/1.29  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.29  tff(c_248, plain, (![D_6, A_89]: (r2_hidden(D_6, A_89) | ~r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_239, c_6])).
% 2.19/1.29  tff(c_330, plain, (![A_89]: (r2_hidden('#skF_7', A_89))), inference(resolution, [status(thm)], [c_315, c_248])).
% 2.19/1.29  tff(c_335, plain, (![A_109]: (r2_hidden('#skF_7', A_109))), inference(resolution, [status(thm)], [c_315, c_248])).
% 2.19/1.29  tff(c_26, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.29  tff(c_24, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.29  tff(c_216, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_207])).
% 2.19/1.29  tff(c_224, plain, (![A_88]: (k4_xboole_0(A_88, k1_xboole_0)=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_216])).
% 2.19/1.29  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.29  tff(c_233, plain, (![D_6, A_88]: (~r2_hidden(D_6, k1_xboole_0) | ~r2_hidden(D_6, A_88))), inference(superposition, [status(thm), theory('equality')], [c_224, c_4])).
% 2.19/1.29  tff(c_345, plain, (![A_88]: (~r2_hidden('#skF_7', A_88))), inference(resolution, [status(thm)], [c_335, c_233])).
% 2.19/1.29  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_330, c_345])).
% 2.19/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  Inference rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Ref     : 0
% 2.19/1.29  #Sup     : 64
% 2.19/1.29  #Fact    : 0
% 2.19/1.29  #Define  : 0
% 2.19/1.29  #Split   : 1
% 2.19/1.29  #Chain   : 0
% 2.19/1.29  #Close   : 0
% 2.19/1.29  
% 2.19/1.29  Ordering : KBO
% 2.19/1.29  
% 2.19/1.29  Simplification rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Subsume      : 3
% 2.19/1.29  #Demod        : 10
% 2.19/1.29  #Tautology    : 43
% 2.19/1.29  #SimpNegUnit  : 1
% 2.19/1.29  #BackRed      : 0
% 2.19/1.29  
% 2.19/1.29  #Partial instantiations: 0
% 2.19/1.29  #Strategies tried      : 1
% 2.19/1.29  
% 2.19/1.29  Timing (in seconds)
% 2.19/1.29  ----------------------
% 2.19/1.30  Preprocessing        : 0.32
% 2.19/1.30  Parsing              : 0.16
% 2.19/1.30  CNF conversion       : 0.03
% 2.19/1.30  Main loop            : 0.21
% 2.19/1.30  Inferencing          : 0.07
% 2.19/1.30  Reduction            : 0.07
% 2.19/1.30  Demodulation         : 0.05
% 2.19/1.30  BG Simplification    : 0.02
% 2.19/1.30  Subsumption          : 0.04
% 2.19/1.30  Abstraction          : 0.01
% 2.19/1.30  MUC search           : 0.00
% 2.19/1.30  Cooper               : 0.00
% 2.19/1.30  Total                : 0.55
% 2.19/1.30  Index Insertion      : 0.00
% 2.19/1.30  Index Deletion       : 0.00
% 2.19/1.30  Index Matching       : 0.00
% 2.19/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
