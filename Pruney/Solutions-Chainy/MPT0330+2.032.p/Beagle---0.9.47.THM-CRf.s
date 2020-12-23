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
% DateTime   : Thu Dec  3 09:54:44 EST 2020

% Result     : Theorem 4.75s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 100 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   79 ( 188 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(k2_xboole_0(A_36,C_37),B_38)
      | ~ r1_tarski(C_37,B_38)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_27,plain,(
    ! [B_24,A_25] :
      ( B_24 = A_25
      | ~ r1_tarski(B_24,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(k2_xboole_0(A_9,B_10),A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_27])).

tff(c_110,plain,(
    ! [B_38,C_37] :
      ( k2_xboole_0(B_38,C_37) = B_38
      | ~ r1_tarski(C_37,B_38)
      | ~ r1_tarski(B_38,B_38) ) ),
    inference(resolution,[status(thm)],[c_106,c_39])).

tff(c_124,plain,(
    ! [B_39,C_40] :
      ( k2_xboole_0(B_39,C_40) = B_39
      | ~ r1_tarski(C_40,B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_110])).

tff(c_160,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_tarski(A_26,C_27)
      | ~ r1_tarski(B_28,C_27)
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_279,plain,(
    ! [A_44,C_45,B_46,A_47] :
      ( r1_tarski(A_44,k2_xboole_0(C_45,B_46))
      | ~ r1_tarski(A_44,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_307,plain,(
    ! [A_48,C_49,B_50,B_51] :
      ( r1_tarski(A_48,k2_xboole_0(C_49,B_50))
      | ~ r1_tarski(k2_xboole_0(A_48,B_51),B_50) ) ),
    inference(resolution,[status(thm)],[c_12,c_279])).

tff(c_343,plain,(
    ! [A_52,C_53,B_54] : r1_tarski(A_52,k2_xboole_0(C_53,k2_xboole_0(A_52,B_54))) ),
    inference(resolution,[status(thm)],[c_6,c_307])).

tff(c_371,plain,(
    ! [B_2,C_53] : r1_tarski(B_2,k2_xboole_0(C_53,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_343])).

tff(c_20,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_382,plain,(
    ! [A_55,C_56,B_57,D_58] :
      ( r1_tarski(k2_zfmisc_1(A_55,C_56),k2_zfmisc_1(B_57,D_58))
      | ~ r1_tarski(C_56,D_58)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3120,plain,(
    ! [A_152,D_151,B_149,A_153,C_150] :
      ( r1_tarski(A_153,k2_zfmisc_1(B_149,D_151))
      | ~ r1_tarski(A_153,k2_zfmisc_1(A_152,C_150))
      | ~ r1_tarski(C_150,D_151)
      | ~ r1_tarski(A_152,B_149) ) ),
    inference(resolution,[status(thm)],[c_382,c_10])).

tff(c_3956,plain,(
    ! [B_184,D_185] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(B_184,D_185))
      | ~ r1_tarski('#skF_6',D_185)
      | ~ r1_tarski('#skF_5',B_184) ) ),
    inference(resolution,[status(thm)],[c_20,c_3120])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2481,plain,(
    ! [C_125,A_127,D_126,A_128,B_124] :
      ( r1_tarski(A_128,k2_zfmisc_1(B_124,D_126))
      | ~ r1_tarski(A_128,k2_zfmisc_1(A_127,C_125))
      | ~ r1_tarski(C_125,D_126)
      | ~ r1_tarski(A_127,B_124) ) ),
    inference(resolution,[status(thm)],[c_382,c_10])).

tff(c_2821,plain,(
    ! [B_139,D_140] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(B_139,D_140))
      | ~ r1_tarski('#skF_4',D_140)
      | ~ r1_tarski('#skF_3',B_139) ) ),
    inference(resolution,[status(thm)],[c_22,c_2481])).

tff(c_18,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_121,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_106,c_18])).

tff(c_2155,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_2826,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2821,c_2155])).

tff(c_2843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_2826])).

tff(c_2844,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_3961,plain,
    ( ~ r1_tarski('#skF_6',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_3956,c_2844])).

tff(c_3978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_371,c_3961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.75/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.91  
% 4.75/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.91  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.75/1.91  
% 4.75/1.91  %Foreground sorts:
% 4.75/1.91  
% 4.75/1.91  
% 4.75/1.91  %Background operators:
% 4.75/1.91  
% 4.75/1.91  
% 4.75/1.91  %Foreground operators:
% 4.75/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.75/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.75/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.75/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.75/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.75/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.75/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.75/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.75/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.75/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.75/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.75/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.75/1.91  
% 5.14/1.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.14/1.92  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.14/1.92  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.14/1.92  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.14/1.92  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.14/1.92  tff(f_62, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 5.14/1.92  tff(f_55, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 5.14/1.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/1.92  tff(c_106, plain, (![A_36, C_37, B_38]: (r1_tarski(k2_xboole_0(A_36, C_37), B_38) | ~r1_tarski(C_37, B_38) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.14/1.92  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.14/1.92  tff(c_27, plain, (![B_24, A_25]: (B_24=A_25 | ~r1_tarski(B_24, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/1.92  tff(c_39, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(k2_xboole_0(A_9, B_10), A_9))), inference(resolution, [status(thm)], [c_12, c_27])).
% 5.14/1.92  tff(c_110, plain, (![B_38, C_37]: (k2_xboole_0(B_38, C_37)=B_38 | ~r1_tarski(C_37, B_38) | ~r1_tarski(B_38, B_38))), inference(resolution, [status(thm)], [c_106, c_39])).
% 5.14/1.92  tff(c_124, plain, (![B_39, C_40]: (k2_xboole_0(B_39, C_40)=B_39 | ~r1_tarski(C_40, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_110])).
% 5.14/1.92  tff(c_160, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_124])).
% 5.14/1.92  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.14/1.92  tff(c_46, plain, (![A_26, C_27, B_28]: (r1_tarski(A_26, C_27) | ~r1_tarski(B_28, C_27) | ~r1_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.14/1.92  tff(c_279, plain, (![A_44, C_45, B_46, A_47]: (r1_tarski(A_44, k2_xboole_0(C_45, B_46)) | ~r1_tarski(A_44, A_47) | ~r1_tarski(A_47, B_46))), inference(resolution, [status(thm)], [c_8, c_46])).
% 5.14/1.92  tff(c_307, plain, (![A_48, C_49, B_50, B_51]: (r1_tarski(A_48, k2_xboole_0(C_49, B_50)) | ~r1_tarski(k2_xboole_0(A_48, B_51), B_50))), inference(resolution, [status(thm)], [c_12, c_279])).
% 5.14/1.92  tff(c_343, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, k2_xboole_0(C_53, k2_xboole_0(A_52, B_54))))), inference(resolution, [status(thm)], [c_6, c_307])).
% 5.14/1.92  tff(c_371, plain, (![B_2, C_53]: (r1_tarski(B_2, k2_xboole_0(C_53, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_343])).
% 5.14/1.92  tff(c_20, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.14/1.92  tff(c_382, plain, (![A_55, C_56, B_57, D_58]: (r1_tarski(k2_zfmisc_1(A_55, C_56), k2_zfmisc_1(B_57, D_58)) | ~r1_tarski(C_56, D_58) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.14/1.92  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.14/1.92  tff(c_3120, plain, (![A_152, D_151, B_149, A_153, C_150]: (r1_tarski(A_153, k2_zfmisc_1(B_149, D_151)) | ~r1_tarski(A_153, k2_zfmisc_1(A_152, C_150)) | ~r1_tarski(C_150, D_151) | ~r1_tarski(A_152, B_149))), inference(resolution, [status(thm)], [c_382, c_10])).
% 5.14/1.92  tff(c_3956, plain, (![B_184, D_185]: (r1_tarski('#skF_2', k2_zfmisc_1(B_184, D_185)) | ~r1_tarski('#skF_6', D_185) | ~r1_tarski('#skF_5', B_184))), inference(resolution, [status(thm)], [c_20, c_3120])).
% 5.14/1.92  tff(c_22, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.14/1.92  tff(c_2481, plain, (![C_125, A_127, D_126, A_128, B_124]: (r1_tarski(A_128, k2_zfmisc_1(B_124, D_126)) | ~r1_tarski(A_128, k2_zfmisc_1(A_127, C_125)) | ~r1_tarski(C_125, D_126) | ~r1_tarski(A_127, B_124))), inference(resolution, [status(thm)], [c_382, c_10])).
% 5.14/1.92  tff(c_2821, plain, (![B_139, D_140]: (r1_tarski('#skF_1', k2_zfmisc_1(B_139, D_140)) | ~r1_tarski('#skF_4', D_140) | ~r1_tarski('#skF_3', B_139))), inference(resolution, [status(thm)], [c_22, c_2481])).
% 5.14/1.92  tff(c_18, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.14/1.92  tff(c_121, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_106, c_18])).
% 5.14/1.92  tff(c_2155, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_121])).
% 5.14/1.92  tff(c_2826, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_2821, c_2155])).
% 5.14/1.92  tff(c_2843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_2826])).
% 5.14/1.92  tff(c_2844, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_121])).
% 5.14/1.92  tff(c_3961, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_3956, c_2844])).
% 5.14/1.92  tff(c_3978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_371, c_371, c_3961])).
% 5.14/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.92  
% 5.14/1.92  Inference rules
% 5.14/1.92  ----------------------
% 5.14/1.92  #Ref     : 0
% 5.14/1.92  #Sup     : 981
% 5.14/1.92  #Fact    : 0
% 5.14/1.92  #Define  : 0
% 5.14/1.92  #Split   : 3
% 5.14/1.92  #Chain   : 0
% 5.14/1.92  #Close   : 0
% 5.14/1.92  
% 5.14/1.92  Ordering : KBO
% 5.14/1.92  
% 5.14/1.92  Simplification rules
% 5.14/1.92  ----------------------
% 5.14/1.92  #Subsume      : 64
% 5.14/1.92  #Demod        : 524
% 5.14/1.92  #Tautology    : 475
% 5.14/1.92  #SimpNegUnit  : 0
% 5.14/1.92  #BackRed      : 0
% 5.14/1.92  
% 5.14/1.92  #Partial instantiations: 0
% 5.14/1.92  #Strategies tried      : 1
% 5.14/1.92  
% 5.14/1.92  Timing (in seconds)
% 5.14/1.92  ----------------------
% 5.14/1.93  Preprocessing        : 0.27
% 5.14/1.93  Parsing              : 0.15
% 5.14/1.93  CNF conversion       : 0.02
% 5.14/1.93  Main loop            : 0.90
% 5.14/1.93  Inferencing          : 0.26
% 5.14/1.93  Reduction            : 0.32
% 5.14/1.93  Demodulation         : 0.26
% 5.14/1.93  BG Simplification    : 0.03
% 5.14/1.93  Subsumption          : 0.21
% 5.14/1.93  Abstraction          : 0.05
% 5.14/1.93  MUC search           : 0.00
% 5.14/1.93  Cooper               : 0.00
% 5.14/1.93  Total                : 1.20
% 5.14/1.93  Index Insertion      : 0.00
% 5.14/1.93  Index Deletion       : 0.00
% 5.14/1.93  Index Matching       : 0.00
% 5.14/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
