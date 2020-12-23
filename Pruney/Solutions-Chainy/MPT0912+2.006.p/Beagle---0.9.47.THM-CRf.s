%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:08 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 138 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 237 expanded)
%              Number of equality atoms :   25 (  81 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(A,k3_zfmisc_1(B,C,D))
          & ! [E,F,G] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & r2_hidden(G,D)
                & A = k3_mcart_1(E,F,G) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

tff(f_36,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_18,plain,(
    r2_hidden('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11] : k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k3_zfmisc_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(k1_mcart_1(A_33),B_34)
      | ~ r2_hidden(A_33,k2_zfmisc_1(B_34,C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_140,plain,(
    ! [A_60,A_61,B_62,C_63] :
      ( r2_hidden(k1_mcart_1(A_60),k2_zfmisc_1(A_61,B_62))
      | ~ r2_hidden(A_60,k3_zfmisc_1(A_61,B_62,C_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_73])).

tff(c_146,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_18,c_140])).

tff(c_147,plain,(
    ! [A_64,B_65,C_66] :
      ( k4_tarski('#skF_1'(A_64,B_65,C_66),'#skF_2'(A_64,B_65,C_66)) = A_64
      | ~ r2_hidden(A_64,k2_zfmisc_1(B_65,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_15,B_16] : k2_mcart_1(k4_tarski(A_15,B_16)) = B_16 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_178,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_mcart_1(A_71) = '#skF_2'(A_71,B_72,C_73)
      | ~ r2_hidden(A_71,k2_zfmisc_1(B_72,C_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_14])).

tff(c_185,plain,(
    k2_mcart_1(k1_mcart_1('#skF_3')) = '#skF_2'(k1_mcart_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_146,c_178])).

tff(c_8,plain,(
    ! [A_12,C_14,B_13] :
      ( r2_hidden(k2_mcart_1(A_12),C_14)
      | ~ r2_hidden(A_12,k2_zfmisc_1(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_172,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_146,c_8])).

tff(c_186,plain,(
    r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),'#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_172])).

tff(c_12,plain,(
    ! [A_15,B_16] : k1_mcart_1(k4_tarski(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_191,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_mcart_1(A_74) = '#skF_1'(A_74,B_75,C_76)
      | ~ r2_hidden(A_74,k2_zfmisc_1(B_75,C_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_12])).

tff(c_198,plain,(
    k1_mcart_1(k1_mcart_1('#skF_3')) = '#skF_1'(k1_mcart_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_146,c_191])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden(k1_mcart_1(A_12),B_13)
      | ~ r2_hidden(A_12,k2_zfmisc_1(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_173,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_10])).

tff(c_199,plain,(
    r2_hidden('#skF_1'(k1_mcart_1('#skF_3'),'#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_173])).

tff(c_94,plain,(
    ! [A_42,C_43,B_44] :
      ( r2_hidden(k2_mcart_1(A_42),C_43)
      | ~ r2_hidden(A_42,k2_zfmisc_1(B_44,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_98,plain,(
    ! [A_48,C_49,A_50,B_51] :
      ( r2_hidden(k2_mcart_1(A_48),C_49)
      | ~ r2_hidden(A_48,k3_zfmisc_1(A_50,B_51,C_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_94])).

tff(c_101,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_98])).

tff(c_206,plain,(
    ! [A_77,A_78,B_79,C_80] :
      ( '#skF_1'(A_77,k2_zfmisc_1(A_78,B_79),C_80) = k1_mcart_1(A_77)
      | ~ r2_hidden(A_77,k3_zfmisc_1(A_78,B_79,C_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_191])).

tff(c_214,plain,(
    '#skF_1'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k1_mcart_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_206])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_tarski('#skF_1'(A_1,B_2,C_3),'#skF_2'(A_1,B_2,C_3)) = A_1
      | ~ r2_hidden(A_1,k2_zfmisc_1(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_218,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_2'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k2_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_2])).

tff(c_222,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),'#skF_2'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6,c_218])).

tff(c_236,plain,(
    '#skF_2'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k2_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_14])).

tff(c_241,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_222])).

tff(c_4,plain,(
    ! [A_6,B_7,C_8] : k4_tarski(k4_tarski(A_6,B_7),C_8) = k3_mcart_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_292,plain,(
    ! [A_82,B_83,C_84,C_85] :
      ( k3_mcart_1('#skF_1'(A_82,B_83,C_84),'#skF_2'(A_82,B_83,C_84),C_85) = k4_tarski(A_82,C_85)
      | ~ r2_hidden(A_82,k2_zfmisc_1(B_83,C_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_4])).

tff(c_16,plain,(
    ! [E_20,F_21,G_22] :
      ( k3_mcart_1(E_20,F_21,G_22) != '#skF_3'
      | ~ r2_hidden(G_22,'#skF_6')
      | ~ r2_hidden(F_21,'#skF_5')
      | ~ r2_hidden(E_20,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_377,plain,(
    ! [A_95,C_96,B_97,C_98] :
      ( k4_tarski(A_95,C_96) != '#skF_3'
      | ~ r2_hidden(C_96,'#skF_6')
      | ~ r2_hidden('#skF_2'(A_95,B_97,C_98),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_95,B_97,C_98),'#skF_4')
      | ~ r2_hidden(A_95,k2_zfmisc_1(B_97,C_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_16])).

tff(c_381,plain,(
    ! [B_97,C_98] :
      ( ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6')
      | ~ r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),B_97,C_98),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1('#skF_3'),B_97,C_98),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(B_97,C_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_377])).

tff(c_389,plain,(
    ! [B_99,C_100] :
      ( ~ r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),B_99,C_100),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1('#skF_3'),B_99,C_100),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(B_99,C_100)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_381])).

tff(c_392,plain,
    ( ~ r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),'#skF_4','#skF_5'),'#skF_5')
    | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_199,c_389])).

tff(c_396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_186,c_392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:18:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.34  %$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.23/1.34  
% 2.23/1.34  %Foreground sorts:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Background operators:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Foreground operators:
% 2.23/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.23/1.34  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.23/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.23/1.34  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.23/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.23/1.34  
% 2.23/1.36  tff(f_60, negated_conjecture, ~(![A, B, C, D]: ~(r2_hidden(A, k3_zfmisc_1(B, C, D)) & (![E, F, G]: ~(((r2_hidden(E, B) & r2_hidden(F, C)) & r2_hidden(G, D)) & (A = k3_mcart_1(E, F, G)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_mcart_1)).
% 2.23/1.36  tff(f_36, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.23/1.36  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.23/1.36  tff(f_32, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.23/1.36  tff(f_46, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.23/1.36  tff(f_34, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.23/1.36  tff(c_18, plain, (r2_hidden('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.36  tff(c_6, plain, (![A_9, B_10, C_11]: (k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k3_zfmisc_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.36  tff(c_73, plain, (![A_33, B_34, C_35]: (r2_hidden(k1_mcart_1(A_33), B_34) | ~r2_hidden(A_33, k2_zfmisc_1(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.36  tff(c_140, plain, (![A_60, A_61, B_62, C_63]: (r2_hidden(k1_mcart_1(A_60), k2_zfmisc_1(A_61, B_62)) | ~r2_hidden(A_60, k3_zfmisc_1(A_61, B_62, C_63)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_73])).
% 2.23/1.36  tff(c_146, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_18, c_140])).
% 2.23/1.36  tff(c_147, plain, (![A_64, B_65, C_66]: (k4_tarski('#skF_1'(A_64, B_65, C_66), '#skF_2'(A_64, B_65, C_66))=A_64 | ~r2_hidden(A_64, k2_zfmisc_1(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.36  tff(c_14, plain, (![A_15, B_16]: (k2_mcart_1(k4_tarski(A_15, B_16))=B_16)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.36  tff(c_178, plain, (![A_71, B_72, C_73]: (k2_mcart_1(A_71)='#skF_2'(A_71, B_72, C_73) | ~r2_hidden(A_71, k2_zfmisc_1(B_72, C_73)))), inference(superposition, [status(thm), theory('equality')], [c_147, c_14])).
% 2.23/1.36  tff(c_185, plain, (k2_mcart_1(k1_mcart_1('#skF_3'))='#skF_2'(k1_mcart_1('#skF_3'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_146, c_178])).
% 2.23/1.36  tff(c_8, plain, (![A_12, C_14, B_13]: (r2_hidden(k2_mcart_1(A_12), C_14) | ~r2_hidden(A_12, k2_zfmisc_1(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.36  tff(c_172, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')), '#skF_5')), inference(resolution, [status(thm)], [c_146, c_8])).
% 2.23/1.36  tff(c_186, plain, (r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), '#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_172])).
% 2.23/1.36  tff(c_12, plain, (![A_15, B_16]: (k1_mcart_1(k4_tarski(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.36  tff(c_191, plain, (![A_74, B_75, C_76]: (k1_mcart_1(A_74)='#skF_1'(A_74, B_75, C_76) | ~r2_hidden(A_74, k2_zfmisc_1(B_75, C_76)))), inference(superposition, [status(thm), theory('equality')], [c_147, c_12])).
% 2.23/1.36  tff(c_198, plain, (k1_mcart_1(k1_mcart_1('#skF_3'))='#skF_1'(k1_mcart_1('#skF_3'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_146, c_191])).
% 2.23/1.36  tff(c_10, plain, (![A_12, B_13, C_14]: (r2_hidden(k1_mcart_1(A_12), B_13) | ~r2_hidden(A_12, k2_zfmisc_1(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.36  tff(c_173, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4')), inference(resolution, [status(thm)], [c_146, c_10])).
% 2.23/1.36  tff(c_199, plain, (r2_hidden('#skF_1'(k1_mcart_1('#skF_3'), '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_173])).
% 2.23/1.36  tff(c_94, plain, (![A_42, C_43, B_44]: (r2_hidden(k2_mcart_1(A_42), C_43) | ~r2_hidden(A_42, k2_zfmisc_1(B_44, C_43)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.36  tff(c_98, plain, (![A_48, C_49, A_50, B_51]: (r2_hidden(k2_mcart_1(A_48), C_49) | ~r2_hidden(A_48, k3_zfmisc_1(A_50, B_51, C_49)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_94])).
% 2.23/1.36  tff(c_101, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_18, c_98])).
% 2.23/1.36  tff(c_206, plain, (![A_77, A_78, B_79, C_80]: ('#skF_1'(A_77, k2_zfmisc_1(A_78, B_79), C_80)=k1_mcart_1(A_77) | ~r2_hidden(A_77, k3_zfmisc_1(A_78, B_79, C_80)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_191])).
% 2.23/1.36  tff(c_214, plain, ('#skF_1'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k1_mcart_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_206])).
% 2.23/1.36  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski('#skF_1'(A_1, B_2, C_3), '#skF_2'(A_1, B_2, C_3))=A_1 | ~r2_hidden(A_1, k2_zfmisc_1(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.36  tff(c_218, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_2'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'))='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_2])).
% 2.23/1.36  tff(c_222, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_2'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6, c_218])).
% 2.23/1.36  tff(c_236, plain, ('#skF_2'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k2_mcart_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_222, c_14])).
% 2.23/1.36  tff(c_241, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_222])).
% 2.23/1.36  tff(c_4, plain, (![A_6, B_7, C_8]: (k4_tarski(k4_tarski(A_6, B_7), C_8)=k3_mcart_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.36  tff(c_292, plain, (![A_82, B_83, C_84, C_85]: (k3_mcart_1('#skF_1'(A_82, B_83, C_84), '#skF_2'(A_82, B_83, C_84), C_85)=k4_tarski(A_82, C_85) | ~r2_hidden(A_82, k2_zfmisc_1(B_83, C_84)))), inference(superposition, [status(thm), theory('equality')], [c_147, c_4])).
% 2.23/1.36  tff(c_16, plain, (![E_20, F_21, G_22]: (k3_mcart_1(E_20, F_21, G_22)!='#skF_3' | ~r2_hidden(G_22, '#skF_6') | ~r2_hidden(F_21, '#skF_5') | ~r2_hidden(E_20, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.36  tff(c_377, plain, (![A_95, C_96, B_97, C_98]: (k4_tarski(A_95, C_96)!='#skF_3' | ~r2_hidden(C_96, '#skF_6') | ~r2_hidden('#skF_2'(A_95, B_97, C_98), '#skF_5') | ~r2_hidden('#skF_1'(A_95, B_97, C_98), '#skF_4') | ~r2_hidden(A_95, k2_zfmisc_1(B_97, C_98)))), inference(superposition, [status(thm), theory('equality')], [c_292, c_16])).
% 2.23/1.36  tff(c_381, plain, (![B_97, C_98]: (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6') | ~r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), B_97, C_98), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1('#skF_3'), B_97, C_98), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(B_97, C_98)))), inference(superposition, [status(thm), theory('equality')], [c_241, c_377])).
% 2.23/1.36  tff(c_389, plain, (![B_99, C_100]: (~r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), B_99, C_100), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1('#skF_3'), B_99, C_100), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(B_99, C_100)))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_381])).
% 2.23/1.36  tff(c_392, plain, (~r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), '#skF_4', '#skF_5'), '#skF_5') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_199, c_389])).
% 2.23/1.36  tff(c_396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_186, c_392])).
% 2.23/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.36  
% 2.23/1.36  Inference rules
% 2.23/1.36  ----------------------
% 2.23/1.36  #Ref     : 0
% 2.23/1.36  #Sup     : 101
% 2.23/1.36  #Fact    : 0
% 2.23/1.36  #Define  : 0
% 2.23/1.36  #Split   : 1
% 2.23/1.36  #Chain   : 0
% 2.23/1.36  #Close   : 0
% 2.23/1.36  
% 2.23/1.36  Ordering : KBO
% 2.23/1.36  
% 2.23/1.36  Simplification rules
% 2.23/1.36  ----------------------
% 2.23/1.36  #Subsume      : 8
% 2.23/1.36  #Demod        : 63
% 2.23/1.36  #Tautology    : 59
% 2.23/1.36  #SimpNegUnit  : 0
% 2.23/1.36  #BackRed      : 3
% 2.23/1.36  
% 2.23/1.36  #Partial instantiations: 0
% 2.23/1.36  #Strategies tried      : 1
% 2.23/1.36  
% 2.23/1.36  Timing (in seconds)
% 2.23/1.36  ----------------------
% 2.23/1.36  Preprocessing        : 0.26
% 2.23/1.36  Parsing              : 0.15
% 2.23/1.36  CNF conversion       : 0.02
% 2.23/1.36  Main loop            : 0.33
% 2.23/1.36  Inferencing          : 0.14
% 2.23/1.36  Reduction            : 0.10
% 2.23/1.36  Demodulation         : 0.08
% 2.23/1.36  BG Simplification    : 0.01
% 2.23/1.36  Subsumption          : 0.05
% 2.23/1.36  Abstraction          : 0.02
% 2.23/1.36  MUC search           : 0.00
% 2.23/1.36  Cooper               : 0.00
% 2.23/1.36  Total                : 0.63
% 2.23/1.36  Index Insertion      : 0.00
% 2.23/1.36  Index Deletion       : 0.00
% 2.23/1.36  Index Matching       : 0.00
% 2.23/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
