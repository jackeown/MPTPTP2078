%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:30 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 125 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 241 expanded)
%              Number of equality atoms :   28 (  67 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3'))
    | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_69,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_70,plain,(
    ! [A_23,C_24,B_25,D_26] :
      ( r1_tarski(A_23,C_24)
      | k2_zfmisc_1(A_23,B_25) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_23,B_25),k2_zfmisc_1(C_24,D_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_86,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_70])).

tff(c_91,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_8])).

tff(c_135,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [B_20,A_21] :
      ( ~ r1_xboole_0(B_20,A_21)
      | ~ r1_tarski(B_20,A_21)
      | v1_xboole_0(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_22] :
      ( ~ r1_tarski(A_22,k1_xboole_0)
      | v1_xboole_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_63])).

tff(c_139,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_68])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_139])).

tff(c_148,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_176,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_18])).

tff(c_186,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_187,plain,(
    ! [B_33,D_34,A_35,C_36] :
      ( r1_tarski(B_33,D_34)
      | k2_zfmisc_1(A_35,B_33) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_35,B_33),k2_zfmisc_1(C_36,D_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_190,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_187])).

tff(c_205,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_190])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_205])).

tff(c_211,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_213,plain,(
    ! [B_37,D_38,A_39,C_40] :
      ( r1_tarski(B_37,D_38)
      | k2_zfmisc_1(A_39,B_37) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_39,B_37),k2_zfmisc_1(C_40,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_229,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_211,c_213])).

tff(c_234,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_251,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_8])).

tff(c_253,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_287,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_2])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_18])).

tff(c_305,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_310,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_68])).

tff(c_318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_310])).

tff(c_320,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_321,plain,(
    ! [A_46,C_47,B_48,D_49] :
      ( r1_tarski(A_46,C_47)
      | k2_zfmisc_1(A_46,B_48) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_46,B_48),k2_zfmisc_1(C_47,D_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_324,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_211,c_321])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_18,c_324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.14  
% 1.76/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.14  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.76/1.14  
% 1.76/1.14  %Foreground sorts:
% 1.76/1.14  
% 1.76/1.14  
% 1.76/1.14  %Background operators:
% 1.76/1.14  
% 1.76/1.14  
% 1.76/1.14  %Foreground operators:
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.76/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.76/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.76/1.14  
% 1.97/1.15  tff(f_62, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 1.97/1.15  tff(f_51, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 1.97/1.15  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.97/1.15  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.97/1.15  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.97/1.15  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.97/1.15  tff(c_22, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.97/1.15  tff(c_20, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.97/1.15  tff(c_69, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_20])).
% 1.97/1.15  tff(c_70, plain, (![A_23, C_24, B_25, D_26]: (r1_tarski(A_23, C_24) | k2_zfmisc_1(A_23, B_25)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_23, B_25), k2_zfmisc_1(C_24, D_26)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.15  tff(c_86, plain, (r1_tarski('#skF_1', '#skF_3') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_70])).
% 1.97/1.15  tff(c_91, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_86])).
% 1.97/1.15  tff(c_8, plain, (![B_6, A_5]: (k1_xboole_0=B_6 | k1_xboole_0=A_5 | k2_zfmisc_1(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.15  tff(c_108, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_91, c_8])).
% 1.97/1.15  tff(c_135, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_108])).
% 1.97/1.15  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.15  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.15  tff(c_58, plain, (![B_20, A_21]: (~r1_xboole_0(B_20, A_21) | ~r1_tarski(B_20, A_21) | v1_xboole_0(B_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.15  tff(c_63, plain, (![A_22]: (~r1_tarski(A_22, k1_xboole_0) | v1_xboole_0(A_22))), inference(resolution, [status(thm)], [c_4, c_58])).
% 1.97/1.15  tff(c_68, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_63])).
% 1.97/1.15  tff(c_139, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_68])).
% 1.97/1.15  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_139])).
% 1.97/1.15  tff(c_148, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_108])).
% 1.97/1.15  tff(c_176, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2])).
% 1.97/1.15  tff(c_18, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.97/1.15  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_18])).
% 1.97/1.15  tff(c_186, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_86])).
% 1.97/1.15  tff(c_187, plain, (![B_33, D_34, A_35, C_36]: (r1_tarski(B_33, D_34) | k2_zfmisc_1(A_35, B_33)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_35, B_33), k2_zfmisc_1(C_36, D_34)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.15  tff(c_190, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_187])).
% 1.97/1.15  tff(c_205, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_190])).
% 1.97/1.15  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_205])).
% 1.97/1.15  tff(c_211, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_20])).
% 1.97/1.15  tff(c_213, plain, (![B_37, D_38, A_39, C_40]: (r1_tarski(B_37, D_38) | k2_zfmisc_1(A_39, B_37)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_39, B_37), k2_zfmisc_1(C_40, D_38)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.15  tff(c_229, plain, (r1_tarski('#skF_1', '#skF_3') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_211, c_213])).
% 1.97/1.15  tff(c_234, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_229])).
% 1.97/1.15  tff(c_251, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_234, c_8])).
% 1.97/1.15  tff(c_253, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_251])).
% 1.97/1.15  tff(c_287, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_2])).
% 1.97/1.15  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_287, c_18])).
% 1.97/1.15  tff(c_305, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_251])).
% 1.97/1.15  tff(c_310, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_68])).
% 1.97/1.15  tff(c_318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_310])).
% 1.97/1.15  tff(c_320, plain, (k2_zfmisc_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_229])).
% 1.97/1.15  tff(c_321, plain, (![A_46, C_47, B_48, D_49]: (r1_tarski(A_46, C_47) | k2_zfmisc_1(A_46, B_48)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_46, B_48), k2_zfmisc_1(C_47, D_49)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.15  tff(c_324, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_211, c_321])).
% 1.97/1.15  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_18, c_324])).
% 1.97/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.15  
% 1.97/1.15  Inference rules
% 1.97/1.15  ----------------------
% 1.97/1.15  #Ref     : 0
% 1.97/1.15  #Sup     : 62
% 1.97/1.15  #Fact    : 0
% 1.97/1.15  #Define  : 0
% 1.97/1.15  #Split   : 5
% 1.97/1.15  #Chain   : 0
% 1.97/1.15  #Close   : 0
% 1.97/1.15  
% 1.97/1.15  Ordering : KBO
% 1.97/1.15  
% 1.97/1.15  Simplification rules
% 1.97/1.15  ----------------------
% 1.97/1.15  #Subsume      : 0
% 1.97/1.15  #Demod        : 105
% 1.97/1.15  #Tautology    : 37
% 1.97/1.15  #SimpNegUnit  : 5
% 1.97/1.15  #BackRed      : 46
% 1.97/1.15  
% 1.97/1.15  #Partial instantiations: 0
% 1.97/1.15  #Strategies tried      : 1
% 1.97/1.15  
% 1.97/1.15  Timing (in seconds)
% 1.97/1.15  ----------------------
% 1.97/1.16  Preprocessing        : 0.25
% 1.97/1.16  Parsing              : 0.14
% 1.97/1.16  CNF conversion       : 0.02
% 1.97/1.16  Main loop            : 0.21
% 1.97/1.16  Inferencing          : 0.07
% 1.97/1.16  Reduction            : 0.07
% 1.97/1.16  Demodulation         : 0.05
% 1.97/1.16  BG Simplification    : 0.01
% 1.97/1.16  Subsumption          : 0.04
% 1.97/1.16  Abstraction          : 0.01
% 1.97/1.16  MUC search           : 0.00
% 1.97/1.16  Cooper               : 0.00
% 1.97/1.16  Total                : 0.49
% 1.97/1.16  Index Insertion      : 0.00
% 1.97/1.16  Index Deletion       : 0.00
% 1.97/1.16  Index Matching       : 0.00
% 1.97/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
