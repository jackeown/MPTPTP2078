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
% DateTime   : Thu Dec  3 09:51:40 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 170 expanded)
%              Number of leaves         :   29 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :   59 ( 213 expanded)
%              Number of equality atoms :   12 (  74 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_62,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_43,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_2'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_42])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( ~ v1_xboole_0(k2_xboole_0(B_10,A_9))
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_59,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_18])).

tff(c_66,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_59])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_71,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_20,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_20])).

tff(c_24,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_62,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_24])).

tff(c_72,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_62])).

tff(c_256,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_260,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_tarski('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_256])).

tff(c_270,plain,(
    k2_tarski('#skF_3','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_260])).

tff(c_423,plain,(
    ! [B_67,C_68,A_69] :
      ( r2_hidden(B_67,C_68)
      | ~ r1_tarski(k2_tarski(A_69,B_67),C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_426,plain,(
    ! [C_68] :
      ( r2_hidden('#skF_2',C_68)
      | ~ r1_tarski('#skF_4',C_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_423])).

tff(c_446,plain,(
    ! [C_68] : r2_hidden('#skF_2',C_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_426])).

tff(c_22,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_22])).

tff(c_565,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r1_xboole_0(A_87,B_88)
      | ~ r2_hidden(C_89,B_88)
      | ~ r2_hidden(C_89,A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_569,plain,(
    ! [C_90,A_91] :
      ( ~ r2_hidden(C_90,'#skF_4')
      | ~ r2_hidden(C_90,A_91) ) ),
    inference(resolution,[status(thm)],[c_76,c_565])).

tff(c_575,plain,(
    ! [A_91] : ~ r2_hidden('#skF_2',A_91) ),
    inference(resolution,[status(thm)],[c_446,c_569])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_575])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.37  
% 2.45/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.45/1.37  
% 2.45/1.37  %Foreground sorts:
% 2.45/1.37  
% 2.45/1.37  
% 2.45/1.37  %Background operators:
% 2.45/1.37  
% 2.45/1.37  
% 2.45/1.37  %Foreground operators:
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.45/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.45/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.45/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.45/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.45/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.45/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.45/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.37  
% 2.67/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.67/1.39  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.67/1.39  tff(f_86, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.67/1.39  tff(f_60, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.67/1.39  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.67/1.39  tff(f_62, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.67/1.39  tff(f_66, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.67/1.39  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.67/1.39  tff(f_82, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.67/1.39  tff(f_64, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.67/1.39  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.67/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.67/1.39  tff(c_26, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.67/1.39  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.67/1.39  tff(c_43, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_2'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_42])).
% 2.67/1.39  tff(c_18, plain, (![B_10, A_9]: (~v1_xboole_0(k2_xboole_0(B_10, A_9)) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.39  tff(c_59, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_43, c_18])).
% 2.67/1.39  tff(c_66, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_59])).
% 2.67/1.39  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.67/1.39  tff(c_71, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_4])).
% 2.67/1.39  tff(c_20, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.67/1.39  tff(c_75, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_20])).
% 2.67/1.39  tff(c_24, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.67/1.39  tff(c_62, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_43, c_24])).
% 2.67/1.39  tff(c_72, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_62])).
% 2.67/1.39  tff(c_256, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.39  tff(c_260, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_4' | ~r1_tarski('#skF_4', k2_tarski('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_256])).
% 2.67/1.39  tff(c_270, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_260])).
% 2.67/1.39  tff(c_423, plain, (![B_67, C_68, A_69]: (r2_hidden(B_67, C_68) | ~r1_tarski(k2_tarski(A_69, B_67), C_68))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.39  tff(c_426, plain, (![C_68]: (r2_hidden('#skF_2', C_68) | ~r1_tarski('#skF_4', C_68))), inference(superposition, [status(thm), theory('equality')], [c_270, c_423])).
% 2.67/1.39  tff(c_446, plain, (![C_68]: (r2_hidden('#skF_2', C_68))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_426])).
% 2.67/1.39  tff(c_22, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.67/1.39  tff(c_76, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_22])).
% 2.67/1.39  tff(c_565, plain, (![A_87, B_88, C_89]: (~r1_xboole_0(A_87, B_88) | ~r2_hidden(C_89, B_88) | ~r2_hidden(C_89, A_87))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.39  tff(c_569, plain, (![C_90, A_91]: (~r2_hidden(C_90, '#skF_4') | ~r2_hidden(C_90, A_91))), inference(resolution, [status(thm)], [c_76, c_565])).
% 2.67/1.39  tff(c_575, plain, (![A_91]: (~r2_hidden('#skF_2', A_91))), inference(resolution, [status(thm)], [c_446, c_569])).
% 2.67/1.39  tff(c_586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_446, c_575])).
% 2.67/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.39  
% 2.67/1.39  Inference rules
% 2.67/1.39  ----------------------
% 2.67/1.39  #Ref     : 0
% 2.67/1.39  #Sup     : 132
% 2.67/1.39  #Fact    : 0
% 2.67/1.39  #Define  : 0
% 2.67/1.39  #Split   : 2
% 2.67/1.39  #Chain   : 0
% 2.67/1.39  #Close   : 0
% 2.67/1.39  
% 2.67/1.39  Ordering : KBO
% 2.67/1.39  
% 2.67/1.39  Simplification rules
% 2.67/1.39  ----------------------
% 2.67/1.39  #Subsume      : 9
% 2.67/1.39  #Demod        : 69
% 2.67/1.39  #Tautology    : 88
% 2.67/1.39  #SimpNegUnit  : 0
% 2.67/1.39  #BackRed      : 8
% 2.67/1.39  
% 2.67/1.39  #Partial instantiations: 0
% 2.67/1.39  #Strategies tried      : 1
% 2.67/1.39  
% 2.67/1.39  Timing (in seconds)
% 2.67/1.39  ----------------------
% 2.67/1.39  Preprocessing        : 0.31
% 2.67/1.39  Parsing              : 0.16
% 2.67/1.39  CNF conversion       : 0.02
% 2.67/1.39  Main loop            : 0.27
% 2.67/1.39  Inferencing          : 0.09
% 2.67/1.39  Reduction            : 0.10
% 2.67/1.39  Demodulation         : 0.08
% 2.67/1.39  BG Simplification    : 0.02
% 2.67/1.39  Subsumption          : 0.05
% 2.67/1.39  Abstraction          : 0.02
% 2.67/1.39  MUC search           : 0.00
% 2.67/1.39  Cooper               : 0.00
% 2.67/1.39  Total                : 0.60
% 2.67/1.39  Index Insertion      : 0.00
% 2.67/1.39  Index Deletion       : 0.00
% 2.67/1.39  Index Matching       : 0.00
% 2.67/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
