%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:37 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   46 (  51 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  79 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
          & r2_hidden(D,A)
          & ! [E,F] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_40,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_75,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    k3_xboole_0('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_34,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_tarski(A_42),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_93,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,B_57)
      | ~ r1_tarski(A_56,k3_xboole_0(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_59,A_60,B_61] :
      ( r1_tarski(A_59,A_60)
      | ~ r1_tarski(A_59,k3_xboole_0(B_61,A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_93])).

tff(c_217,plain,(
    ! [A_76,A_77,B_78] :
      ( r1_tarski(k1_tarski(A_76),A_77)
      | ~ r2_hidden(A_76,k3_xboole_0(B_78,A_77)) ) ),
    inference(resolution,[status(thm)],[c_34,c_108])).

tff(c_233,plain,(
    ! [A_79] :
      ( r1_tarski(k1_tarski(A_79),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(A_79,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_217])).

tff(c_32,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | ~ r1_tarski(k1_tarski(A_42),B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_240,plain,(
    ! [A_79] :
      ( r2_hidden(A_79,k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(A_79,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_233,c_32])).

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

tff(c_697,plain,(
    ! [A_135,B_136,D_137] :
      ( k4_tarski('#skF_5'(A_135,B_136,k2_zfmisc_1(A_135,B_136),D_137),'#skF_6'(A_135,B_136,k2_zfmisc_1(A_135,B_136),D_137)) = D_137
      | ~ r2_hidden(D_137,k2_zfmisc_1(A_135,B_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    ! [E_46,F_47] :
      ( k4_tarski(E_46,F_47) != '#skF_10'
      | ~ r2_hidden(F_47,'#skF_9')
      | ~ r2_hidden(E_46,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_812,plain,(
    ! [D_144,A_145,B_146] :
      ( D_144 != '#skF_10'
      | ~ r2_hidden('#skF_6'(A_145,B_146,k2_zfmisc_1(A_145,B_146),D_144),'#skF_9')
      | ~ r2_hidden('#skF_5'(A_145,B_146,k2_zfmisc_1(A_145,B_146),D_144),'#skF_8')
      | ~ r2_hidden(D_144,k2_zfmisc_1(A_145,B_146)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_36])).

tff(c_819,plain,(
    ! [D_147,A_148] :
      ( D_147 != '#skF_10'
      | ~ r2_hidden('#skF_5'(A_148,'#skF_9',k2_zfmisc_1(A_148,'#skF_9'),D_147),'#skF_8')
      | ~ r2_hidden(D_147,k2_zfmisc_1(A_148,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_12,c_812])).

tff(c_826,plain,(
    ! [D_149] :
      ( D_149 != '#skF_10'
      | ~ r2_hidden(D_149,k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_14,c_819])).

tff(c_882,plain,(
    ~ r2_hidden('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_240,c_826])).

tff(c_38,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_882,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:30:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.45  
% 2.97/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.45  %$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 2.97/1.45  
% 2.97/1.45  %Foreground sorts:
% 2.97/1.45  
% 2.97/1.45  
% 2.97/1.45  %Background operators:
% 2.97/1.45  
% 2.97/1.45  
% 2.97/1.45  %Foreground operators:
% 2.97/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.97/1.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.97/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.97/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.45  tff('#skF_10', type, '#skF_10': $i).
% 2.97/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.97/1.45  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.97/1.45  tff('#skF_9', type, '#skF_9': $i).
% 2.97/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.97/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.45  
% 2.97/1.46  tff(f_65, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.97/1.46  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.97/1.46  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.97/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.97/1.46  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.97/1.46  tff(f_47, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.97/1.46  tff(c_40, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.97/1.46  tff(c_75, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.46  tff(c_83, plain, (k3_xboole_0('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))='#skF_7'), inference(resolution, [status(thm)], [c_40, c_75])).
% 2.97/1.46  tff(c_34, plain, (![A_42, B_43]: (r1_tarski(k1_tarski(A_42), B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.97/1.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.97/1.46  tff(c_93, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, B_57) | ~r1_tarski(A_56, k3_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.46  tff(c_108, plain, (![A_59, A_60, B_61]: (r1_tarski(A_59, A_60) | ~r1_tarski(A_59, k3_xboole_0(B_61, A_60)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_93])).
% 2.97/1.46  tff(c_217, plain, (![A_76, A_77, B_78]: (r1_tarski(k1_tarski(A_76), A_77) | ~r2_hidden(A_76, k3_xboole_0(B_78, A_77)))), inference(resolution, [status(thm)], [c_34, c_108])).
% 2.97/1.46  tff(c_233, plain, (![A_79]: (r1_tarski(k1_tarski(A_79), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(A_79, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_217])).
% 2.97/1.46  tff(c_32, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | ~r1_tarski(k1_tarski(A_42), B_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.97/1.46  tff(c_240, plain, (![A_79]: (r2_hidden(A_79, k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(A_79, '#skF_7'))), inference(resolution, [status(thm)], [c_233, c_32])).
% 2.97/1.46  tff(c_14, plain, (![A_8, B_9, D_35]: (r2_hidden('#skF_5'(A_8, B_9, k2_zfmisc_1(A_8, B_9), D_35), A_8) | ~r2_hidden(D_35, k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.97/1.46  tff(c_12, plain, (![A_8, B_9, D_35]: (r2_hidden('#skF_6'(A_8, B_9, k2_zfmisc_1(A_8, B_9), D_35), B_9) | ~r2_hidden(D_35, k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.97/1.46  tff(c_697, plain, (![A_135, B_136, D_137]: (k4_tarski('#skF_5'(A_135, B_136, k2_zfmisc_1(A_135, B_136), D_137), '#skF_6'(A_135, B_136, k2_zfmisc_1(A_135, B_136), D_137))=D_137 | ~r2_hidden(D_137, k2_zfmisc_1(A_135, B_136)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.97/1.46  tff(c_36, plain, (![E_46, F_47]: (k4_tarski(E_46, F_47)!='#skF_10' | ~r2_hidden(F_47, '#skF_9') | ~r2_hidden(E_46, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.97/1.46  tff(c_812, plain, (![D_144, A_145, B_146]: (D_144!='#skF_10' | ~r2_hidden('#skF_6'(A_145, B_146, k2_zfmisc_1(A_145, B_146), D_144), '#skF_9') | ~r2_hidden('#skF_5'(A_145, B_146, k2_zfmisc_1(A_145, B_146), D_144), '#skF_8') | ~r2_hidden(D_144, k2_zfmisc_1(A_145, B_146)))), inference(superposition, [status(thm), theory('equality')], [c_697, c_36])).
% 2.97/1.46  tff(c_819, plain, (![D_147, A_148]: (D_147!='#skF_10' | ~r2_hidden('#skF_5'(A_148, '#skF_9', k2_zfmisc_1(A_148, '#skF_9'), D_147), '#skF_8') | ~r2_hidden(D_147, k2_zfmisc_1(A_148, '#skF_9')))), inference(resolution, [status(thm)], [c_12, c_812])).
% 2.97/1.46  tff(c_826, plain, (![D_149]: (D_149!='#skF_10' | ~r2_hidden(D_149, k2_zfmisc_1('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_14, c_819])).
% 2.97/1.46  tff(c_882, plain, (~r2_hidden('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_240, c_826])).
% 2.97/1.46  tff(c_38, plain, (r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.97/1.46  tff(c_884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_882, c_38])).
% 2.97/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.46  
% 2.97/1.46  Inference rules
% 2.97/1.46  ----------------------
% 2.97/1.46  #Ref     : 0
% 2.97/1.46  #Sup     : 212
% 2.97/1.46  #Fact    : 0
% 2.97/1.46  #Define  : 0
% 2.97/1.46  #Split   : 1
% 2.97/1.46  #Chain   : 0
% 2.97/1.46  #Close   : 0
% 2.97/1.46  
% 2.97/1.46  Ordering : KBO
% 2.97/1.46  
% 2.97/1.46  Simplification rules
% 2.97/1.46  ----------------------
% 2.97/1.46  #Subsume      : 57
% 2.97/1.46  #Demod        : 9
% 2.97/1.46  #Tautology    : 49
% 2.97/1.46  #SimpNegUnit  : 1
% 2.97/1.46  #BackRed      : 1
% 2.97/1.46  
% 2.97/1.46  #Partial instantiations: 0
% 2.97/1.46  #Strategies tried      : 1
% 2.97/1.46  
% 2.97/1.46  Timing (in seconds)
% 2.97/1.46  ----------------------
% 2.97/1.46  Preprocessing        : 0.29
% 2.97/1.46  Parsing              : 0.16
% 2.97/1.46  CNF conversion       : 0.03
% 2.97/1.46  Main loop            : 0.41
% 2.97/1.46  Inferencing          : 0.15
% 2.97/1.46  Reduction            : 0.11
% 2.97/1.46  Demodulation         : 0.08
% 2.97/1.46  BG Simplification    : 0.03
% 2.97/1.47  Subsumption          : 0.10
% 2.97/1.47  Abstraction          : 0.02
% 3.12/1.47  MUC search           : 0.00
% 3.12/1.47  Cooper               : 0.00
% 3.12/1.47  Total                : 0.73
% 3.12/1.47  Index Insertion      : 0.00
% 3.12/1.47  Index Deletion       : 0.00
% 3.12/1.47  Index Matching       : 0.00
% 3.12/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
