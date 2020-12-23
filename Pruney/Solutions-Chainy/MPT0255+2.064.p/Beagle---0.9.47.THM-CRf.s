%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:47 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 373 expanded)
%              Number of leaves         :   27 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          :   71 ( 560 expanded)
%              Number of equality atoms :   34 ( 178 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_30,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_96,plain,(
    ! [B_40,A_41] :
      ( ~ v1_xboole_0(k2_xboole_0(B_40,A_41))
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_99,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_96])).

tff(c_104,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_99])).

tff(c_86,plain,(
    ! [B_37,A_38] :
      ( ~ v1_xboole_0(B_37)
      | B_37 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_89,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_110,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_104,c_89])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    ! [A_7] : r1_tarski('#skF_5',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_10])).

tff(c_113,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_46])).

tff(c_123,plain,(
    ! [B_42,A_43] : k2_xboole_0(B_42,A_43) = k2_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(k2_xboole_0(B_6,A_5))
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_217,plain,(
    ! [A_51,B_52] :
      ( ~ v1_xboole_0(k2_xboole_0(A_51,B_52))
      | v1_xboole_0(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_8])).

tff(c_220,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0(k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_217])).

tff(c_231,plain,(
    v1_xboole_0(k2_tarski('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_220])).

tff(c_112,plain,(
    ! [A_38] :
      ( A_38 = '#skF_5'
      | ~ v1_xboole_0(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_89])).

tff(c_246,plain,(
    k2_tarski('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_231,c_112])).

tff(c_340,plain,(
    ! [A_64,C_65,B_66] :
      ( r2_hidden(A_64,C_65)
      | ~ r1_tarski(k2_tarski(A_64,B_66),C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_343,plain,(
    ! [C_65] :
      ( r2_hidden('#skF_3',C_65)
      | ~ r1_tarski('#skF_5',C_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_340])).

tff(c_348,plain,(
    ! [C_65] : r2_hidden('#skF_3',C_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_343])).

tff(c_351,plain,(
    ! [D_68,B_69,A_70] :
      ( D_68 = B_69
      | D_68 = A_70
      | ~ r2_hidden(D_68,k2_tarski(A_70,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_372,plain,(
    ! [B_69,A_70] :
      ( B_69 = '#skF_3'
      | A_70 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_348,c_351])).

tff(c_378,plain,(
    ! [A_70] : A_70 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_379,plain,(
    ! [A_71] : A_71 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_70,plain,(
    ! [A_31,B_32] : k2_xboole_0(k1_tarski(A_31),B_32) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74,plain,(
    ! [A_31] : k1_tarski(A_31) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_114,plain,(
    ! [A_31] : k1_tarski(A_31) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_74])).

tff(c_436,plain,(
    '#skF_5' != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_114])).

tff(c_577,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_436])).

tff(c_578,plain,(
    ! [B_69] : B_69 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_592,plain,(
    ! [B_1156] : B_1156 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_191,plain,(
    ! [A_47,B_48] : k2_xboole_0(k1_tarski(A_47),B_48) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_44])).

tff(c_195,plain,(
    ! [B_2,A_47] : k2_xboole_0(B_2,k1_tarski(A_47)) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_641,plain,(
    '#skF_5' != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_592,c_195])).

tff(c_757,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_641])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.39  
% 2.68/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.39  %$ r2_hidden > r1_tarski > v1_xboole_0 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.68/1.39  
% 2.68/1.39  %Foreground sorts:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Background operators:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Foreground operators:
% 2.68/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.68/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.68/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.39  
% 2.68/1.40  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.68/1.40  tff(f_74, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.68/1.40  tff(f_36, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.68/1.40  tff(f_46, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.68/1.40  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.68/1.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.68/1.40  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.68/1.40  tff(f_55, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.68/1.40  tff(f_30, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.68/1.40  tff(f_70, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.68/1.40  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.68/1.40  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.68/1.40  tff(c_96, plain, (![B_40, A_41]: (~v1_xboole_0(k2_xboole_0(B_40, A_41)) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.68/1.40  tff(c_99, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_46, c_96])).
% 2.68/1.40  tff(c_104, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_99])).
% 2.68/1.40  tff(c_86, plain, (![B_37, A_38]: (~v1_xboole_0(B_37) | B_37=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.40  tff(c_89, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_4, c_86])).
% 2.68/1.40  tff(c_110, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_104, c_89])).
% 2.68/1.40  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.68/1.40  tff(c_116, plain, (![A_7]: (r1_tarski('#skF_5', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_10])).
% 2.68/1.40  tff(c_113, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_46])).
% 2.68/1.40  tff(c_123, plain, (![B_42, A_43]: (k2_xboole_0(B_42, A_43)=k2_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.40  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(k2_xboole_0(B_6, A_5)) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.68/1.40  tff(c_217, plain, (![A_51, B_52]: (~v1_xboole_0(k2_xboole_0(A_51, B_52)) | v1_xboole_0(A_51))), inference(superposition, [status(thm), theory('equality')], [c_123, c_8])).
% 2.68/1.40  tff(c_220, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0(k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_217])).
% 2.68/1.40  tff(c_231, plain, (v1_xboole_0(k2_tarski('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_220])).
% 2.68/1.40  tff(c_112, plain, (![A_38]: (A_38='#skF_5' | ~v1_xboole_0(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_89])).
% 2.68/1.40  tff(c_246, plain, (k2_tarski('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_231, c_112])).
% 2.68/1.40  tff(c_340, plain, (![A_64, C_65, B_66]: (r2_hidden(A_64, C_65) | ~r1_tarski(k2_tarski(A_64, B_66), C_65))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.40  tff(c_343, plain, (![C_65]: (r2_hidden('#skF_3', C_65) | ~r1_tarski('#skF_5', C_65))), inference(superposition, [status(thm), theory('equality')], [c_246, c_340])).
% 2.68/1.40  tff(c_348, plain, (![C_65]: (r2_hidden('#skF_3', C_65))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_343])).
% 2.68/1.40  tff(c_351, plain, (![D_68, B_69, A_70]: (D_68=B_69 | D_68=A_70 | ~r2_hidden(D_68, k2_tarski(A_70, B_69)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.40  tff(c_372, plain, (![B_69, A_70]: (B_69='#skF_3' | A_70='#skF_3')), inference(resolution, [status(thm)], [c_348, c_351])).
% 2.68/1.40  tff(c_378, plain, (![A_70]: (A_70='#skF_3')), inference(splitLeft, [status(thm)], [c_372])).
% 2.68/1.40  tff(c_379, plain, (![A_71]: (A_71='#skF_3')), inference(splitLeft, [status(thm)], [c_372])).
% 2.68/1.40  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.68/1.40  tff(c_70, plain, (![A_31, B_32]: (k2_xboole_0(k1_tarski(A_31), B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.68/1.40  tff(c_74, plain, (![A_31]: (k1_tarski(A_31)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_70])).
% 2.68/1.40  tff(c_114, plain, (![A_31]: (k1_tarski(A_31)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_74])).
% 2.68/1.40  tff(c_436, plain, ('#skF_5'!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_379, c_114])).
% 2.68/1.40  tff(c_577, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_378, c_436])).
% 2.68/1.40  tff(c_578, plain, (![B_69]: (B_69='#skF_3')), inference(splitRight, [status(thm)], [c_372])).
% 2.68/1.40  tff(c_592, plain, (![B_1156]: (B_1156='#skF_3')), inference(splitRight, [status(thm)], [c_372])).
% 2.68/1.40  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.40  tff(c_44, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.68/1.40  tff(c_191, plain, (![A_47, B_48]: (k2_xboole_0(k1_tarski(A_47), B_48)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_44])).
% 2.68/1.40  tff(c_195, plain, (![B_2, A_47]: (k2_xboole_0(B_2, k1_tarski(A_47))!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2, c_191])).
% 2.68/1.40  tff(c_641, plain, ('#skF_5'!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_592, c_195])).
% 2.68/1.40  tff(c_757, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_578, c_641])).
% 2.68/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.40  
% 2.68/1.40  Inference rules
% 2.68/1.40  ----------------------
% 2.68/1.40  #Ref     : 0
% 2.68/1.40  #Sup     : 243
% 2.68/1.40  #Fact    : 0
% 2.68/1.40  #Define  : 0
% 2.68/1.40  #Split   : 2
% 2.68/1.40  #Chain   : 0
% 2.68/1.40  #Close   : 0
% 2.68/1.40  
% 2.68/1.40  Ordering : KBO
% 2.68/1.40  
% 2.68/1.40  Simplification rules
% 2.68/1.40  ----------------------
% 2.68/1.40  #Subsume      : 69
% 2.68/1.40  #Demod        : 48
% 2.68/1.40  #Tautology    : 59
% 2.68/1.40  #SimpNegUnit  : 0
% 2.68/1.40  #BackRed      : 8
% 2.68/1.40  
% 2.68/1.40  #Partial instantiations: 68
% 2.68/1.40  #Strategies tried      : 1
% 2.68/1.40  
% 2.68/1.40  Timing (in seconds)
% 2.68/1.40  ----------------------
% 2.68/1.41  Preprocessing        : 0.29
% 2.68/1.41  Parsing              : 0.14
% 2.68/1.41  CNF conversion       : 0.02
% 2.68/1.41  Main loop            : 0.32
% 2.68/1.41  Inferencing          : 0.13
% 2.68/1.41  Reduction            : 0.10
% 2.68/1.41  Demodulation         : 0.08
% 2.68/1.41  BG Simplification    : 0.02
% 2.68/1.41  Subsumption          : 0.05
% 2.68/1.41  Abstraction          : 0.02
% 2.68/1.41  MUC search           : 0.00
% 2.68/1.41  Cooper               : 0.00
% 2.68/1.41  Total                : 0.64
% 2.68/1.41  Index Insertion      : 0.00
% 2.68/1.41  Index Deletion       : 0.00
% 2.68/1.41  Index Matching       : 0.00
% 2.68/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
