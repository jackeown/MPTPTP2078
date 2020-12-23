%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:44 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 154 expanded)
%              Number of leaves         :   29 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 ( 172 expanded)
%              Number of equality atoms :   23 (  89 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_18,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_152,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_206,plain,(
    ! [A_50] : k2_xboole_0(k1_xboole_0,A_50) = A_50 ),
    inference(resolution,[status(thm)],[c_18,c_152])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_219,plain,(
    ! [A_50] : k2_xboole_0(A_50,k1_xboole_0) = A_50 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2])).

tff(c_48,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_56,plain,(
    ! [B_40,A_41] : k2_xboole_0(B_40,A_41) = k2_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,(
    ! [A_41,B_40] : r1_tarski(A_41,k2_xboole_0(B_40,A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_22])).

tff(c_108,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_71])).

tff(c_172,plain,(
    k2_xboole_0('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108,c_152])).

tff(c_247,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_172])).

tff(c_20,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_311,plain,(
    ! [A_15] : r1_xboole_0(A_15,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_20])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_580,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_2'(A_67),A_67)
      | A_67 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_8])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_620,plain,(
    ! [A_68,B_69] :
      ( ~ r1_xboole_0(A_68,B_69)
      | k3_xboole_0(A_68,B_69) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_580,c_6])).

tff(c_634,plain,(
    ! [A_73] : k3_xboole_0(A_73,'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_311,c_620])).

tff(c_639,plain,(
    ! [A_73,C_7] :
      ( ~ r1_xboole_0(A_73,'#skF_7')
      | ~ r2_hidden(C_7,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_6])).

tff(c_644,plain,(
    ! [C_7] : ~ r2_hidden(C_7,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_639])).

tff(c_222,plain,(
    ! [A_50] : k2_xboole_0(A_50,k1_xboole_0) = A_50 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2])).

tff(c_332,plain,(
    ! [A_50] : k2_xboole_0(A_50,'#skF_7') = A_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_222])).

tff(c_309,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_48])).

tff(c_394,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_309])).

tff(c_28,plain,(
    ! [D_23,B_19] : r2_hidden(D_23,k2_tarski(D_23,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_476,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_28])).

tff(c_648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_644,c_476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.30  
% 2.10/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 2.10/1.31  
% 2.10/1.31  %Foreground sorts:
% 2.10/1.31  
% 2.10/1.31  
% 2.10/1.31  %Background operators:
% 2.10/1.31  
% 2.10/1.31  
% 2.10/1.31  %Foreground operators:
% 2.10/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.10/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.10/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.10/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.31  
% 2.10/1.32  tff(f_61, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.10/1.32  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.10/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.10/1.32  tff(f_84, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.10/1.32  tff(f_65, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.10/1.32  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.10/1.32  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.10/1.32  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.10/1.32  tff(f_74, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.10/1.32  tff(c_18, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.32  tff(c_152, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.32  tff(c_206, plain, (![A_50]: (k2_xboole_0(k1_xboole_0, A_50)=A_50)), inference(resolution, [status(thm)], [c_18, c_152])).
% 2.10/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.32  tff(c_219, plain, (![A_50]: (k2_xboole_0(A_50, k1_xboole_0)=A_50)), inference(superposition, [status(thm), theory('equality')], [c_206, c_2])).
% 2.10/1.32  tff(c_48, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.10/1.32  tff(c_56, plain, (![B_40, A_41]: (k2_xboole_0(B_40, A_41)=k2_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.32  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.10/1.32  tff(c_71, plain, (![A_41, B_40]: (r1_tarski(A_41, k2_xboole_0(B_40, A_41)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_22])).
% 2.10/1.32  tff(c_108, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_71])).
% 2.10/1.32  tff(c_172, plain, (k2_xboole_0('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_108, c_152])).
% 2.10/1.32  tff(c_247, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_219, c_172])).
% 2.10/1.32  tff(c_20, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.10/1.32  tff(c_311, plain, (![A_15]: (r1_xboole_0(A_15, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_20])).
% 2.10/1.32  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.32  tff(c_580, plain, (![A_67]: (r2_hidden('#skF_2'(A_67), A_67) | A_67='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_8])).
% 2.10/1.32  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.32  tff(c_620, plain, (![A_68, B_69]: (~r1_xboole_0(A_68, B_69) | k3_xboole_0(A_68, B_69)='#skF_7')), inference(resolution, [status(thm)], [c_580, c_6])).
% 2.10/1.32  tff(c_634, plain, (![A_73]: (k3_xboole_0(A_73, '#skF_7')='#skF_7')), inference(resolution, [status(thm)], [c_311, c_620])).
% 2.10/1.32  tff(c_639, plain, (![A_73, C_7]: (~r1_xboole_0(A_73, '#skF_7') | ~r2_hidden(C_7, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_634, c_6])).
% 2.10/1.32  tff(c_644, plain, (![C_7]: (~r2_hidden(C_7, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_639])).
% 2.10/1.32  tff(c_222, plain, (![A_50]: (k2_xboole_0(A_50, k1_xboole_0)=A_50)), inference(superposition, [status(thm), theory('equality')], [c_206, c_2])).
% 2.10/1.32  tff(c_332, plain, (![A_50]: (k2_xboole_0(A_50, '#skF_7')=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_247, c_222])).
% 2.10/1.32  tff(c_309, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_48])).
% 2.10/1.32  tff(c_394, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_332, c_309])).
% 2.10/1.32  tff(c_28, plain, (![D_23, B_19]: (r2_hidden(D_23, k2_tarski(D_23, B_19)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.10/1.32  tff(c_476, plain, (r2_hidden('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_394, c_28])).
% 2.10/1.32  tff(c_648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_644, c_476])).
% 2.10/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.32  
% 2.10/1.32  Inference rules
% 2.10/1.32  ----------------------
% 2.10/1.32  #Ref     : 0
% 2.10/1.32  #Sup     : 145
% 2.10/1.32  #Fact    : 0
% 2.10/1.32  #Define  : 0
% 2.10/1.32  #Split   : 0
% 2.10/1.32  #Chain   : 0
% 2.10/1.32  #Close   : 0
% 2.10/1.32  
% 2.10/1.32  Ordering : KBO
% 2.10/1.32  
% 2.10/1.32  Simplification rules
% 2.10/1.32  ----------------------
% 2.10/1.32  #Subsume      : 0
% 2.10/1.32  #Demod        : 85
% 2.10/1.32  #Tautology    : 121
% 2.10/1.32  #SimpNegUnit  : 2
% 2.10/1.32  #BackRed      : 13
% 2.10/1.32  
% 2.10/1.32  #Partial instantiations: 0
% 2.10/1.32  #Strategies tried      : 1
% 2.10/1.32  
% 2.10/1.32  Timing (in seconds)
% 2.10/1.32  ----------------------
% 2.10/1.32  Preprocessing        : 0.32
% 2.10/1.32  Parsing              : 0.17
% 2.10/1.32  CNF conversion       : 0.02
% 2.10/1.32  Main loop            : 0.25
% 2.10/1.32  Inferencing          : 0.08
% 2.10/1.32  Reduction            : 0.09
% 2.10/1.32  Demodulation         : 0.07
% 2.10/1.32  BG Simplification    : 0.01
% 2.10/1.32  Subsumption          : 0.04
% 2.10/1.32  Abstraction          : 0.02
% 2.10/1.32  MUC search           : 0.00
% 2.10/1.32  Cooper               : 0.00
% 2.10/1.32  Total                : 0.59
% 2.10/1.32  Index Insertion      : 0.00
% 2.10/1.32  Index Deletion       : 0.00
% 2.10/1.32  Index Matching       : 0.00
% 2.10/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
