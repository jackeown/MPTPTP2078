%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:37 EST 2020

% Result     : Theorem 6.58s
% Output     : CNFRefutation 6.58s
% Verified   : 
% Statistics : Number of formulae       :   58 (  90 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 159 expanded)
%              Number of equality atoms :   19 (  42 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
          & r2_hidden(D,A)
          & ! [E,F] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_14,plain,(
    ! [A_8,B_9,D_35] :
      ( r2_hidden('#skF_5'(A_8,B_9,k2_zfmisc_1(A_8,B_9),D_35),A_8)
      | ~ r2_hidden(D_35,k2_zfmisc_1(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_8,B_9,D_35] :
      ( r2_hidden('#skF_6'(A_8,B_9,k2_zfmisc_1(A_8,B_9),D_35),B_9)
      | ~ r2_hidden(D_35,k2_zfmisc_1(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1785,plain,(
    ! [A_153,B_154,D_155] :
      ( k4_tarski('#skF_5'(A_153,B_154,k2_zfmisc_1(A_153,B_154),D_155),'#skF_6'(A_153,B_154,k2_zfmisc_1(A_153,B_154),D_155)) = D_155
      | ~ r2_hidden(D_155,k2_zfmisc_1(A_153,B_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    ! [E_46,F_47] :
      ( k4_tarski(E_46,F_47) != '#skF_10'
      | ~ r2_hidden(F_47,'#skF_9')
      | ~ r2_hidden(E_46,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1825,plain,(
    ! [D_158,A_159,B_160] :
      ( D_158 != '#skF_10'
      | ~ r2_hidden('#skF_6'(A_159,B_160,k2_zfmisc_1(A_159,B_160),D_158),'#skF_9')
      | ~ r2_hidden('#skF_5'(A_159,B_160,k2_zfmisc_1(A_159,B_160),D_158),'#skF_8')
      | ~ r2_hidden(D_158,k2_zfmisc_1(A_159,B_160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1785,c_36])).

tff(c_5023,plain,(
    ! [D_390,A_391] :
      ( D_390 != '#skF_10'
      | ~ r2_hidden('#skF_5'(A_391,'#skF_9',k2_zfmisc_1(A_391,'#skF_9'),D_390),'#skF_8')
      | ~ r2_hidden(D_390,k2_zfmisc_1(A_391,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1825])).

tff(c_5029,plain,(
    ~ r2_hidden('#skF_10',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_14,c_5023])).

tff(c_40,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_75,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(A_52,B_53) = B_53
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    k2_xboole_0('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(A_56,k2_xboole_0(C_57,B_58))
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_248,plain,(
    ! [A_86,C_87,B_88] :
      ( k2_xboole_0(A_86,k2_xboole_0(C_87,B_88)) = k2_xboole_0(C_87,B_88)
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(resolution,[status(thm)],[c_89,c_6])).

tff(c_425,plain,(
    ! [C_98,B_99,B_100] :
      ( k2_xboole_0(k2_xboole_0(C_98,B_99),B_100) = k2_xboole_0(C_98,B_99)
      | ~ r1_tarski(B_100,B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_248])).

tff(c_500,plain,(
    ! [B_100] :
      ( k2_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),B_100) = k2_xboole_0('#skF_7',k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r1_tarski(B_100,k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_425])).

tff(c_3156,plain,(
    ! [B_265] :
      ( k2_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),B_265) = k2_zfmisc_1('#skF_8','#skF_9')
      | ~ r1_tarski(B_265,k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_500])).

tff(c_3173,plain,(
    k2_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),'#skF_7') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_3156])).

tff(c_38,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_tarski(A_42),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_112,plain,(
    ! [A_59,B_60,A_61] :
      ( r1_tarski(A_59,k2_xboole_0(B_60,A_61))
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_315,plain,(
    ! [A_89,B_90,A_91] :
      ( k2_xboole_0(A_89,k2_xboole_0(B_90,A_91)) = k2_xboole_0(B_90,A_91)
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_112,c_6])).

tff(c_32,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | ~ r1_tarski(k1_tarski(A_42),B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_129,plain,(
    ! [A_42,B_60,A_61] :
      ( r2_hidden(A_42,k2_xboole_0(B_60,A_61))
      | ~ r1_tarski(k1_tarski(A_42),B_60) ) ),
    inference(resolution,[status(thm)],[c_112,c_32])).

tff(c_2176,plain,(
    ! [A_193,B_194,A_195,A_196] :
      ( r2_hidden(A_193,k2_xboole_0(B_194,A_195))
      | ~ r1_tarski(k1_tarski(A_193),A_196)
      | ~ r1_tarski(A_196,B_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_129])).

tff(c_2201,plain,(
    ! [A_197,B_198,A_199,B_200] :
      ( r2_hidden(A_197,k2_xboole_0(B_198,A_199))
      | ~ r1_tarski(B_200,B_198)
      | ~ r2_hidden(A_197,B_200) ) ),
    inference(resolution,[status(thm)],[c_34,c_2176])).

tff(c_3897,plain,(
    ! [C_334,A_336,A_333,A_332,B_335] :
      ( r2_hidden(A_336,k2_xboole_0(k2_xboole_0(C_334,B_335),A_332))
      | ~ r2_hidden(A_336,A_333)
      | ~ r1_tarski(A_333,B_335) ) ),
    inference(resolution,[status(thm)],[c_4,c_2201])).

tff(c_3956,plain,(
    ! [C_343,B_344,A_345] :
      ( r2_hidden('#skF_10',k2_xboole_0(k2_xboole_0(C_343,B_344),A_345))
      | ~ r1_tarski('#skF_7',B_344) ) ),
    inference(resolution,[status(thm)],[c_38,c_3897])).

tff(c_4050,plain,(
    ! [A_345] :
      ( r2_hidden('#skF_10',k2_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),A_345))
      | ~ r1_tarski('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_3956])).

tff(c_4076,plain,(
    ! [A_346] : r2_hidden('#skF_10',k2_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),A_346)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4050])).

tff(c_4088,plain,(
    r2_hidden('#skF_10',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3173,c_4076])).

tff(c_5031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5029,c_4088])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.58/2.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.33  
% 6.58/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.33  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 6.58/2.33  
% 6.58/2.33  %Foreground sorts:
% 6.58/2.33  
% 6.58/2.33  
% 6.58/2.33  %Background operators:
% 6.58/2.33  
% 6.58/2.33  
% 6.58/2.33  %Foreground operators:
% 6.58/2.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.58/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.58/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.58/2.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.58/2.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.58/2.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.58/2.33  tff('#skF_7', type, '#skF_7': $i).
% 6.58/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.58/2.33  tff('#skF_10', type, '#skF_10': $i).
% 6.58/2.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.58/2.33  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.58/2.33  tff('#skF_9', type, '#skF_9': $i).
% 6.58/2.33  tff('#skF_8', type, '#skF_8': $i).
% 6.58/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.58/2.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.58/2.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.58/2.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.58/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.58/2.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.58/2.33  
% 6.58/2.35  tff(f_47, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.58/2.35  tff(f_65, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 6.58/2.35  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.58/2.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.58/2.35  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 6.58/2.35  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.58/2.35  tff(c_14, plain, (![A_8, B_9, D_35]: (r2_hidden('#skF_5'(A_8, B_9, k2_zfmisc_1(A_8, B_9), D_35), A_8) | ~r2_hidden(D_35, k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.58/2.35  tff(c_12, plain, (![A_8, B_9, D_35]: (r2_hidden('#skF_6'(A_8, B_9, k2_zfmisc_1(A_8, B_9), D_35), B_9) | ~r2_hidden(D_35, k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.58/2.35  tff(c_1785, plain, (![A_153, B_154, D_155]: (k4_tarski('#skF_5'(A_153, B_154, k2_zfmisc_1(A_153, B_154), D_155), '#skF_6'(A_153, B_154, k2_zfmisc_1(A_153, B_154), D_155))=D_155 | ~r2_hidden(D_155, k2_zfmisc_1(A_153, B_154)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.58/2.35  tff(c_36, plain, (![E_46, F_47]: (k4_tarski(E_46, F_47)!='#skF_10' | ~r2_hidden(F_47, '#skF_9') | ~r2_hidden(E_46, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.58/2.35  tff(c_1825, plain, (![D_158, A_159, B_160]: (D_158!='#skF_10' | ~r2_hidden('#skF_6'(A_159, B_160, k2_zfmisc_1(A_159, B_160), D_158), '#skF_9') | ~r2_hidden('#skF_5'(A_159, B_160, k2_zfmisc_1(A_159, B_160), D_158), '#skF_8') | ~r2_hidden(D_158, k2_zfmisc_1(A_159, B_160)))), inference(superposition, [status(thm), theory('equality')], [c_1785, c_36])).
% 6.58/2.35  tff(c_5023, plain, (![D_390, A_391]: (D_390!='#skF_10' | ~r2_hidden('#skF_5'(A_391, '#skF_9', k2_zfmisc_1(A_391, '#skF_9'), D_390), '#skF_8') | ~r2_hidden(D_390, k2_zfmisc_1(A_391, '#skF_9')))), inference(resolution, [status(thm)], [c_12, c_1825])).
% 6.58/2.35  tff(c_5029, plain, (~r2_hidden('#skF_10', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_14, c_5023])).
% 6.58/2.35  tff(c_40, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.58/2.35  tff(c_75, plain, (![A_52, B_53]: (k2_xboole_0(A_52, B_53)=B_53 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.58/2.35  tff(c_83, plain, (k2_xboole_0('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))=k2_zfmisc_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_40, c_75])).
% 6.58/2.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.58/2.35  tff(c_89, plain, (![A_56, C_57, B_58]: (r1_tarski(A_56, k2_xboole_0(C_57, B_58)) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.58/2.35  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.58/2.35  tff(c_248, plain, (![A_86, C_87, B_88]: (k2_xboole_0(A_86, k2_xboole_0(C_87, B_88))=k2_xboole_0(C_87, B_88) | ~r1_tarski(A_86, B_88))), inference(resolution, [status(thm)], [c_89, c_6])).
% 6.58/2.35  tff(c_425, plain, (![C_98, B_99, B_100]: (k2_xboole_0(k2_xboole_0(C_98, B_99), B_100)=k2_xboole_0(C_98, B_99) | ~r1_tarski(B_100, B_99))), inference(superposition, [status(thm), theory('equality')], [c_2, c_248])).
% 6.58/2.35  tff(c_500, plain, (![B_100]: (k2_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), B_100)=k2_xboole_0('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9')) | ~r1_tarski(B_100, k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_83, c_425])).
% 6.58/2.35  tff(c_3156, plain, (![B_265]: (k2_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), B_265)=k2_zfmisc_1('#skF_8', '#skF_9') | ~r1_tarski(B_265, k2_zfmisc_1('#skF_8', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_500])).
% 6.58/2.35  tff(c_3173, plain, (k2_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), '#skF_7')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_40, c_3156])).
% 6.58/2.35  tff(c_38, plain, (r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.58/2.35  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.58/2.35  tff(c_34, plain, (![A_42, B_43]: (r1_tarski(k1_tarski(A_42), B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.58/2.35  tff(c_112, plain, (![A_59, B_60, A_61]: (r1_tarski(A_59, k2_xboole_0(B_60, A_61)) | ~r1_tarski(A_59, B_60))), inference(superposition, [status(thm), theory('equality')], [c_2, c_89])).
% 6.58/2.35  tff(c_315, plain, (![A_89, B_90, A_91]: (k2_xboole_0(A_89, k2_xboole_0(B_90, A_91))=k2_xboole_0(B_90, A_91) | ~r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_112, c_6])).
% 6.58/2.35  tff(c_32, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | ~r1_tarski(k1_tarski(A_42), B_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.58/2.35  tff(c_129, plain, (![A_42, B_60, A_61]: (r2_hidden(A_42, k2_xboole_0(B_60, A_61)) | ~r1_tarski(k1_tarski(A_42), B_60))), inference(resolution, [status(thm)], [c_112, c_32])).
% 6.58/2.35  tff(c_2176, plain, (![A_193, B_194, A_195, A_196]: (r2_hidden(A_193, k2_xboole_0(B_194, A_195)) | ~r1_tarski(k1_tarski(A_193), A_196) | ~r1_tarski(A_196, B_194))), inference(superposition, [status(thm), theory('equality')], [c_315, c_129])).
% 6.58/2.35  tff(c_2201, plain, (![A_197, B_198, A_199, B_200]: (r2_hidden(A_197, k2_xboole_0(B_198, A_199)) | ~r1_tarski(B_200, B_198) | ~r2_hidden(A_197, B_200))), inference(resolution, [status(thm)], [c_34, c_2176])).
% 6.58/2.35  tff(c_3897, plain, (![C_334, A_336, A_333, A_332, B_335]: (r2_hidden(A_336, k2_xboole_0(k2_xboole_0(C_334, B_335), A_332)) | ~r2_hidden(A_336, A_333) | ~r1_tarski(A_333, B_335))), inference(resolution, [status(thm)], [c_4, c_2201])).
% 6.58/2.35  tff(c_3956, plain, (![C_343, B_344, A_345]: (r2_hidden('#skF_10', k2_xboole_0(k2_xboole_0(C_343, B_344), A_345)) | ~r1_tarski('#skF_7', B_344))), inference(resolution, [status(thm)], [c_38, c_3897])).
% 6.58/2.35  tff(c_4050, plain, (![A_345]: (r2_hidden('#skF_10', k2_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), A_345)) | ~r1_tarski('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_83, c_3956])).
% 6.58/2.35  tff(c_4076, plain, (![A_346]: (r2_hidden('#skF_10', k2_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), A_346)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4050])).
% 6.58/2.35  tff(c_4088, plain, (r2_hidden('#skF_10', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3173, c_4076])).
% 6.58/2.35  tff(c_5031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5029, c_4088])).
% 6.58/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.35  
% 6.58/2.35  Inference rules
% 6.58/2.35  ----------------------
% 6.58/2.35  #Ref     : 3
% 6.58/2.35  #Sup     : 1464
% 6.58/2.35  #Fact    : 0
% 6.58/2.35  #Define  : 0
% 6.58/2.35  #Split   : 2
% 6.58/2.35  #Chain   : 0
% 6.58/2.35  #Close   : 0
% 6.58/2.35  
% 6.58/2.35  Ordering : KBO
% 6.58/2.35  
% 6.58/2.35  Simplification rules
% 6.58/2.35  ----------------------
% 6.58/2.35  #Subsume      : 394
% 6.58/2.35  #Demod        : 139
% 6.58/2.35  #Tautology    : 163
% 6.58/2.35  #SimpNegUnit  : 1
% 6.58/2.35  #BackRed      : 1
% 6.58/2.35  
% 6.58/2.35  #Partial instantiations: 0
% 6.58/2.35  #Strategies tried      : 1
% 6.58/2.35  
% 6.58/2.35  Timing (in seconds)
% 6.58/2.35  ----------------------
% 6.58/2.35  Preprocessing        : 0.28
% 6.58/2.35  Parsing              : 0.14
% 6.58/2.35  CNF conversion       : 0.02
% 6.58/2.35  Main loop            : 1.28
% 6.58/2.35  Inferencing          : 0.37
% 6.58/2.35  Reduction            : 0.38
% 6.58/2.35  Demodulation         : 0.29
% 6.58/2.35  BG Simplification    : 0.06
% 6.58/2.35  Subsumption          : 0.38
% 6.58/2.35  Abstraction          : 0.06
% 6.58/2.35  MUC search           : 0.00
% 6.58/2.35  Cooper               : 0.00
% 6.58/2.35  Total                : 1.59
% 6.58/2.35  Index Insertion      : 0.00
% 6.58/2.35  Index Deletion       : 0.00
% 6.58/2.35  Index Matching       : 0.00
% 6.58/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
