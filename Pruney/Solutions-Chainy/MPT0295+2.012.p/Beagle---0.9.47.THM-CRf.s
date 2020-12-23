%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:38 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 132 expanded)
%              Number of equality atoms :   11 (  22 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
          & r2_hidden(D,A)
          & ! [E,F] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_42,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(k2_tarski(A_65,B_66),C_67)
      | ~ r2_hidden(B_66,C_67)
      | ~ r2_hidden(A_65,C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_xboole_0(k2_tarski(A_68,B_69),C_70) = C_70
      | ~ r2_hidden(B_69,C_70)
      | ~ r2_hidden(A_68,C_70) ) ),
    inference(resolution,[status(thm)],[c_69,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_84,B_85,C_86,C_87] :
      ( r1_tarski(k2_tarski(A_84,B_85),C_86)
      | ~ r1_tarski(C_87,C_86)
      | ~ r2_hidden(B_85,C_87)
      | ~ r2_hidden(A_84,C_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2])).

tff(c_105,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k2_tarski(A_88,B_89),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_89,'#skF_7')
      | ~ r2_hidden(A_88,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_98])).

tff(c_34,plain,(
    ! [B_43,C_44,A_42] :
      ( r2_hidden(B_43,C_44)
      | ~ r1_tarski(k2_tarski(A_42,B_43),C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_118,plain,(
    ! [B_89,A_88] :
      ( r2_hidden(B_89,k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_89,'#skF_7')
      | ~ r2_hidden(A_88,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_105,c_34])).

tff(c_121,plain,(
    ! [A_88] : ~ r2_hidden(A_88,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_40,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_40])).

tff(c_125,plain,(
    ! [B_89] :
      ( r2_hidden(B_89,k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_89,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_12,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_5'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),A_6)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_6'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),B_7)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_134,plain,(
    ! [A_97,B_98,D_99] :
      ( k4_tarski('#skF_5'(A_97,B_98,k2_zfmisc_1(A_97,B_98),D_99),'#skF_6'(A_97,B_98,k2_zfmisc_1(A_97,B_98),D_99)) = D_99
      | ~ r2_hidden(D_99,k2_zfmisc_1(A_97,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    ! [E_47,F_48] :
      ( k4_tarski(E_47,F_48) != '#skF_10'
      | ~ r2_hidden(F_48,'#skF_9')
      | ~ r2_hidden(E_47,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_196,plain,(
    ! [D_110,A_111,B_112] :
      ( D_110 != '#skF_10'
      | ~ r2_hidden('#skF_6'(A_111,B_112,k2_zfmisc_1(A_111,B_112),D_110),'#skF_9')
      | ~ r2_hidden('#skF_5'(A_111,B_112,k2_zfmisc_1(A_111,B_112),D_110),'#skF_8')
      | ~ r2_hidden(D_110,k2_zfmisc_1(A_111,B_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_38])).

tff(c_203,plain,(
    ! [D_113,A_114] :
      ( D_113 != '#skF_10'
      | ~ r2_hidden('#skF_5'(A_114,'#skF_9',k2_zfmisc_1(A_114,'#skF_9'),D_113),'#skF_8')
      | ~ r2_hidden(D_113,k2_zfmisc_1(A_114,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_10,c_196])).

tff(c_210,plain,(
    ! [D_115] :
      ( D_115 != '#skF_10'
      | ~ r2_hidden(D_115,k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_12,c_203])).

tff(c_250,plain,(
    ~ r2_hidden('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_125,c_210])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:14:07 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.36  
% 2.17/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.36  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 2.17/1.36  
% 2.17/1.36  %Foreground sorts:
% 2.17/1.36  
% 2.17/1.36  
% 2.17/1.36  %Background operators:
% 2.17/1.36  
% 2.17/1.36  
% 2.17/1.36  %Foreground operators:
% 2.17/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.17/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.17/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.36  tff('#skF_10', type, '#skF_10': $i).
% 2.17/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.36  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.17/1.36  tff('#skF_9', type, '#skF_9': $i).
% 2.17/1.36  tff('#skF_8', type, '#skF_8': $i).
% 2.17/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.17/1.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.17/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.17/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.36  
% 2.17/1.37  tff(f_67, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 2.17/1.37  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.17/1.37  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.17/1.37  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.17/1.37  tff(f_45, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.17/1.37  tff(c_42, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.17/1.37  tff(c_69, plain, (![A_65, B_66, C_67]: (r1_tarski(k2_tarski(A_65, B_66), C_67) | ~r2_hidden(B_66, C_67) | ~r2_hidden(A_65, C_67))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.37  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.37  tff(c_82, plain, (![A_68, B_69, C_70]: (k2_xboole_0(k2_tarski(A_68, B_69), C_70)=C_70 | ~r2_hidden(B_69, C_70) | ~r2_hidden(A_68, C_70))), inference(resolution, [status(thm)], [c_69, c_4])).
% 2.17/1.37  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.37  tff(c_98, plain, (![A_84, B_85, C_86, C_87]: (r1_tarski(k2_tarski(A_84, B_85), C_86) | ~r1_tarski(C_87, C_86) | ~r2_hidden(B_85, C_87) | ~r2_hidden(A_84, C_87))), inference(superposition, [status(thm), theory('equality')], [c_82, c_2])).
% 2.17/1.37  tff(c_105, plain, (![A_88, B_89]: (r1_tarski(k2_tarski(A_88, B_89), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_89, '#skF_7') | ~r2_hidden(A_88, '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_98])).
% 2.17/1.37  tff(c_34, plain, (![B_43, C_44, A_42]: (r2_hidden(B_43, C_44) | ~r1_tarski(k2_tarski(A_42, B_43), C_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.37  tff(c_118, plain, (![B_89, A_88]: (r2_hidden(B_89, k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_89, '#skF_7') | ~r2_hidden(A_88, '#skF_7'))), inference(resolution, [status(thm)], [c_105, c_34])).
% 2.17/1.37  tff(c_121, plain, (![A_88]: (~r2_hidden(A_88, '#skF_7'))), inference(splitLeft, [status(thm)], [c_118])).
% 2.17/1.37  tff(c_40, plain, (r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.17/1.37  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_40])).
% 2.17/1.37  tff(c_125, plain, (![B_89]: (r2_hidden(B_89, k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_89, '#skF_7'))), inference(splitRight, [status(thm)], [c_118])).
% 2.17/1.37  tff(c_12, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_5'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), A_6) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.37  tff(c_10, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_6'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), B_7) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.37  tff(c_134, plain, (![A_97, B_98, D_99]: (k4_tarski('#skF_5'(A_97, B_98, k2_zfmisc_1(A_97, B_98), D_99), '#skF_6'(A_97, B_98, k2_zfmisc_1(A_97, B_98), D_99))=D_99 | ~r2_hidden(D_99, k2_zfmisc_1(A_97, B_98)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.37  tff(c_38, plain, (![E_47, F_48]: (k4_tarski(E_47, F_48)!='#skF_10' | ~r2_hidden(F_48, '#skF_9') | ~r2_hidden(E_47, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.17/1.37  tff(c_196, plain, (![D_110, A_111, B_112]: (D_110!='#skF_10' | ~r2_hidden('#skF_6'(A_111, B_112, k2_zfmisc_1(A_111, B_112), D_110), '#skF_9') | ~r2_hidden('#skF_5'(A_111, B_112, k2_zfmisc_1(A_111, B_112), D_110), '#skF_8') | ~r2_hidden(D_110, k2_zfmisc_1(A_111, B_112)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_38])).
% 2.17/1.37  tff(c_203, plain, (![D_113, A_114]: (D_113!='#skF_10' | ~r2_hidden('#skF_5'(A_114, '#skF_9', k2_zfmisc_1(A_114, '#skF_9'), D_113), '#skF_8') | ~r2_hidden(D_113, k2_zfmisc_1(A_114, '#skF_9')))), inference(resolution, [status(thm)], [c_10, c_196])).
% 2.17/1.37  tff(c_210, plain, (![D_115]: (D_115!='#skF_10' | ~r2_hidden(D_115, k2_zfmisc_1('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_12, c_203])).
% 2.17/1.37  tff(c_250, plain, (~r2_hidden('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_125, c_210])).
% 2.17/1.37  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_250, c_40])).
% 2.17/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.37  
% 2.17/1.37  Inference rules
% 2.17/1.37  ----------------------
% 2.17/1.37  #Ref     : 0
% 2.17/1.37  #Sup     : 44
% 2.17/1.37  #Fact    : 0
% 2.17/1.37  #Define  : 0
% 2.17/1.37  #Split   : 2
% 2.17/1.37  #Chain   : 0
% 2.17/1.37  #Close   : 0
% 2.17/1.37  
% 2.17/1.37  Ordering : KBO
% 2.17/1.37  
% 2.17/1.37  Simplification rules
% 2.17/1.37  ----------------------
% 2.17/1.37  #Subsume      : 3
% 2.17/1.37  #Demod        : 0
% 2.17/1.37  #Tautology    : 14
% 2.17/1.37  #SimpNegUnit  : 2
% 2.17/1.37  #BackRed      : 2
% 2.17/1.37  
% 2.17/1.37  #Partial instantiations: 0
% 2.17/1.37  #Strategies tried      : 1
% 2.17/1.37  
% 2.17/1.37  Timing (in seconds)
% 2.17/1.37  ----------------------
% 2.17/1.38  Preprocessing        : 0.30
% 2.17/1.38  Parsing              : 0.16
% 2.17/1.38  CNF conversion       : 0.02
% 2.17/1.38  Main loop            : 0.27
% 2.17/1.38  Inferencing          : 0.11
% 2.17/1.38  Reduction            : 0.06
% 2.17/1.38  Demodulation         : 0.04
% 2.17/1.38  BG Simplification    : 0.02
% 2.17/1.38  Subsumption          : 0.05
% 2.17/1.38  Abstraction          : 0.01
% 2.17/1.38  MUC search           : 0.00
% 2.17/1.38  Cooper               : 0.00
% 2.17/1.38  Total                : 0.60
% 2.17/1.38  Index Insertion      : 0.00
% 2.17/1.38  Index Deletion       : 0.00
% 2.17/1.38  Index Matching       : 0.00
% 2.17/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
