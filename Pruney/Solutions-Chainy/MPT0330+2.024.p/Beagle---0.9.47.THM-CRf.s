%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:43 EST 2020

% Result     : Theorem 6.70s
% Output     : CNFRefutation 6.86s
% Verified   : 
% Statistics : Number of formulae       :   58 (  84 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 125 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_44,plain,(
    ! [C_29,A_27,B_28] : k2_xboole_0(k2_zfmisc_1(C_29,A_27),k2_zfmisc_1(C_29,B_28)) = k2_zfmisc_1(C_29,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_tarski(A_14,k2_xboole_0(C_16,B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_103,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(A_50,C_51)
      | ~ r1_tarski(B_52,C_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_506,plain,(
    ! [A_85,C_86,B_87,A_88] :
      ( r1_tarski(A_85,k2_xboole_0(C_86,B_87))
      | ~ r1_tarski(A_85,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(resolution,[status(thm)],[c_32,c_103])).

tff(c_634,plain,(
    ! [C_95,B_96] :
      ( r1_tarski('#skF_5',k2_xboole_0(C_95,B_96))
      | ~ r1_tarski(k2_zfmisc_1('#skF_8','#skF_9'),B_96) ) ),
    inference(resolution,[status(thm)],[c_48,c_506])).

tff(c_667,plain,(
    ! [C_97] : r1_tarski('#skF_5',k2_xboole_0(C_97,k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(resolution,[status(thm)],[c_30,c_634])).

tff(c_680,plain,(
    ! [A_27] : r1_tarski('#skF_5',k2_zfmisc_1('#skF_8',k2_xboole_0(A_27,'#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_667])).

tff(c_242,plain,(
    ! [A_71,C_72,B_73] : k2_xboole_0(k2_zfmisc_1(A_71,C_72),k2_zfmisc_1(B_73,C_72)) = k2_zfmisc_1(k2_xboole_0(A_71,B_73),C_72) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6745,plain,(
    ! [A_316,A_317,B_318,C_319] :
      ( r1_tarski(A_316,k2_zfmisc_1(k2_xboole_0(A_317,B_318),C_319))
      | ~ r1_tarski(A_316,k2_zfmisc_1(B_318,C_319)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_32])).

tff(c_36,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_187,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_tarski(k2_xboole_0(A_66,C_67),B_68)
      | ~ r1_tarski(C_67,B_68)
      | ~ r1_tarski(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_64,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_74,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(k2_xboole_0(A_20,B_21),A_20) ) ),
    inference(resolution,[status(thm)],[c_36,c_64])).

tff(c_191,plain,(
    ! [B_68,C_67] :
      ( k2_xboole_0(B_68,C_67) = B_68
      | ~ r1_tarski(C_67,B_68)
      | ~ r1_tarski(B_68,B_68) ) ),
    inference(resolution,[status(thm)],[c_187,c_74])).

tff(c_205,plain,(
    ! [B_69,C_70] :
      ( k2_xboole_0(B_69,C_70) = B_69
      | ~ r1_tarski(C_70,B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_191])).

tff(c_239,plain,(
    ! [A_20,B_21] : k2_xboole_0(k2_xboole_0(A_20,B_21),A_20) = k2_xboole_0(A_20,B_21) ),
    inference(resolution,[status(thm)],[c_36,c_205])).

tff(c_42,plain,(
    ! [A_27,C_29,B_28] : k2_xboole_0(k2_zfmisc_1(A_27,C_29),k2_zfmisc_1(B_28,C_29)) = k2_zfmisc_1(k2_xboole_0(A_27,B_28),C_29) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_537,plain,(
    ! [C_89,A_90,B_91] : k2_xboole_0(k2_zfmisc_1(C_89,A_90),k2_zfmisc_1(C_89,B_91)) = k2_zfmisc_1(C_89,k2_xboole_0(A_90,B_91)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_578,plain,(
    ! [C_89,A_90,B_91] : r1_tarski(k2_zfmisc_1(C_89,A_90),k2_zfmisc_1(C_89,k2_xboole_0(A_90,B_91))) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_36])).

tff(c_50,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_698,plain,(
    ! [C_98,B_99] :
      ( r1_tarski('#skF_4',k2_xboole_0(C_98,B_99))
      | ~ r1_tarski(k2_zfmisc_1('#skF_6','#skF_7'),B_99) ) ),
    inference(resolution,[status(thm)],[c_50,c_506])).

tff(c_1065,plain,(
    ! [C_119,B_120] : r1_tarski('#skF_4',k2_xboole_0(C_119,k2_zfmisc_1('#skF_6',k2_xboole_0('#skF_7',B_120)))) ),
    inference(resolution,[status(thm)],[c_578,c_698])).

tff(c_1860,plain,(
    ! [A_161,B_162] : r1_tarski('#skF_4',k2_zfmisc_1(k2_xboole_0(A_161,'#skF_6'),k2_xboole_0('#skF_7',B_162))) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1065])).

tff(c_1875,plain,(
    ! [B_21,B_162] : r1_tarski('#skF_4',k2_zfmisc_1(k2_xboole_0('#skF_6',B_21),k2_xboole_0('#skF_7',B_162))) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_1860])).

tff(c_46,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_4','#skF_5'),k2_zfmisc_1(k2_xboole_0('#skF_6','#skF_8'),k2_xboole_0('#skF_7','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_203,plain,
    ( ~ r1_tarski('#skF_5',k2_zfmisc_1(k2_xboole_0('#skF_6','#skF_8'),k2_xboole_0('#skF_7','#skF_9')))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(k2_xboole_0('#skF_6','#skF_8'),k2_xboole_0('#skF_7','#skF_9'))) ),
    inference(resolution,[status(thm)],[c_187,c_46])).

tff(c_950,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1(k2_xboole_0('#skF_6','#skF_8'),k2_xboole_0('#skF_7','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_2012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1875,c_950])).

tff(c_2013,plain,(
    ~ r1_tarski('#skF_5',k2_zfmisc_1(k2_xboole_0('#skF_6','#skF_8'),k2_xboole_0('#skF_7','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_6772,plain,(
    ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_8',k2_xboole_0('#skF_7','#skF_9'))) ),
    inference(resolution,[status(thm)],[c_6745,c_2013])).

tff(c_6842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_6772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:44:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.70/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.86/2.34  
% 6.86/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.86/2.35  %$ r2_hidden > r1_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 6.86/2.35  
% 6.86/2.35  %Foreground sorts:
% 6.86/2.35  
% 6.86/2.35  
% 6.86/2.35  %Background operators:
% 6.86/2.35  
% 6.86/2.35  
% 6.86/2.35  %Foreground operators:
% 6.86/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.86/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.86/2.35  tff('#skF_7', type, '#skF_7': $i).
% 6.86/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.86/2.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.86/2.35  tff('#skF_5', type, '#skF_5': $i).
% 6.86/2.35  tff('#skF_6', type, '#skF_6': $i).
% 6.86/2.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.86/2.35  tff('#skF_9', type, '#skF_9': $i).
% 6.86/2.35  tff('#skF_8', type, '#skF_8': $i).
% 6.86/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.86/2.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.86/2.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.86/2.35  tff('#skF_4', type, '#skF_4': $i).
% 6.86/2.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.86/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.86/2.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.86/2.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.86/2.35  
% 6.86/2.36  tff(f_71, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 6.86/2.36  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.86/2.36  tff(f_78, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 6.86/2.36  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 6.86/2.36  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.86/2.36  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.86/2.36  tff(f_65, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.86/2.36  tff(c_44, plain, (![C_29, A_27, B_28]: (k2_xboole_0(k2_zfmisc_1(C_29, A_27), k2_zfmisc_1(C_29, B_28))=k2_zfmisc_1(C_29, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.86/2.36  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.86/2.36  tff(c_48, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.86/2.36  tff(c_32, plain, (![A_14, C_16, B_15]: (r1_tarski(A_14, k2_xboole_0(C_16, B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.86/2.36  tff(c_103, plain, (![A_50, C_51, B_52]: (r1_tarski(A_50, C_51) | ~r1_tarski(B_52, C_51) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.86/2.36  tff(c_506, plain, (![A_85, C_86, B_87, A_88]: (r1_tarski(A_85, k2_xboole_0(C_86, B_87)) | ~r1_tarski(A_85, A_88) | ~r1_tarski(A_88, B_87))), inference(resolution, [status(thm)], [c_32, c_103])).
% 6.86/2.36  tff(c_634, plain, (![C_95, B_96]: (r1_tarski('#skF_5', k2_xboole_0(C_95, B_96)) | ~r1_tarski(k2_zfmisc_1('#skF_8', '#skF_9'), B_96))), inference(resolution, [status(thm)], [c_48, c_506])).
% 6.86/2.36  tff(c_667, plain, (![C_97]: (r1_tarski('#skF_5', k2_xboole_0(C_97, k2_zfmisc_1('#skF_8', '#skF_9'))))), inference(resolution, [status(thm)], [c_30, c_634])).
% 6.86/2.36  tff(c_680, plain, (![A_27]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_8', k2_xboole_0(A_27, '#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_44, c_667])).
% 6.86/2.36  tff(c_242, plain, (![A_71, C_72, B_73]: (k2_xboole_0(k2_zfmisc_1(A_71, C_72), k2_zfmisc_1(B_73, C_72))=k2_zfmisc_1(k2_xboole_0(A_71, B_73), C_72))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.86/2.36  tff(c_6745, plain, (![A_316, A_317, B_318, C_319]: (r1_tarski(A_316, k2_zfmisc_1(k2_xboole_0(A_317, B_318), C_319)) | ~r1_tarski(A_316, k2_zfmisc_1(B_318, C_319)))), inference(superposition, [status(thm), theory('equality')], [c_242, c_32])).
% 6.86/2.36  tff(c_36, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.86/2.36  tff(c_187, plain, (![A_66, C_67, B_68]: (r1_tarski(k2_xboole_0(A_66, C_67), B_68) | ~r1_tarski(C_67, B_68) | ~r1_tarski(A_66, B_68))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.86/2.36  tff(c_64, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.86/2.36  tff(c_74, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(k2_xboole_0(A_20, B_21), A_20))), inference(resolution, [status(thm)], [c_36, c_64])).
% 6.86/2.36  tff(c_191, plain, (![B_68, C_67]: (k2_xboole_0(B_68, C_67)=B_68 | ~r1_tarski(C_67, B_68) | ~r1_tarski(B_68, B_68))), inference(resolution, [status(thm)], [c_187, c_74])).
% 6.86/2.36  tff(c_205, plain, (![B_69, C_70]: (k2_xboole_0(B_69, C_70)=B_69 | ~r1_tarski(C_70, B_69))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_191])).
% 6.86/2.36  tff(c_239, plain, (![A_20, B_21]: (k2_xboole_0(k2_xboole_0(A_20, B_21), A_20)=k2_xboole_0(A_20, B_21))), inference(resolution, [status(thm)], [c_36, c_205])).
% 6.86/2.36  tff(c_42, plain, (![A_27, C_29, B_28]: (k2_xboole_0(k2_zfmisc_1(A_27, C_29), k2_zfmisc_1(B_28, C_29))=k2_zfmisc_1(k2_xboole_0(A_27, B_28), C_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.86/2.36  tff(c_537, plain, (![C_89, A_90, B_91]: (k2_xboole_0(k2_zfmisc_1(C_89, A_90), k2_zfmisc_1(C_89, B_91))=k2_zfmisc_1(C_89, k2_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.86/2.36  tff(c_578, plain, (![C_89, A_90, B_91]: (r1_tarski(k2_zfmisc_1(C_89, A_90), k2_zfmisc_1(C_89, k2_xboole_0(A_90, B_91))))), inference(superposition, [status(thm), theory('equality')], [c_537, c_36])).
% 6.86/2.36  tff(c_50, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.86/2.36  tff(c_698, plain, (![C_98, B_99]: (r1_tarski('#skF_4', k2_xboole_0(C_98, B_99)) | ~r1_tarski(k2_zfmisc_1('#skF_6', '#skF_7'), B_99))), inference(resolution, [status(thm)], [c_50, c_506])).
% 6.86/2.36  tff(c_1065, plain, (![C_119, B_120]: (r1_tarski('#skF_4', k2_xboole_0(C_119, k2_zfmisc_1('#skF_6', k2_xboole_0('#skF_7', B_120)))))), inference(resolution, [status(thm)], [c_578, c_698])).
% 6.86/2.36  tff(c_1860, plain, (![A_161, B_162]: (r1_tarski('#skF_4', k2_zfmisc_1(k2_xboole_0(A_161, '#skF_6'), k2_xboole_0('#skF_7', B_162))))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1065])).
% 6.86/2.36  tff(c_1875, plain, (![B_21, B_162]: (r1_tarski('#skF_4', k2_zfmisc_1(k2_xboole_0('#skF_6', B_21), k2_xboole_0('#skF_7', B_162))))), inference(superposition, [status(thm), theory('equality')], [c_239, c_1860])).
% 6.86/2.36  tff(c_46, plain, (~r1_tarski(k2_xboole_0('#skF_4', '#skF_5'), k2_zfmisc_1(k2_xboole_0('#skF_6', '#skF_8'), k2_xboole_0('#skF_7', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.86/2.36  tff(c_203, plain, (~r1_tarski('#skF_5', k2_zfmisc_1(k2_xboole_0('#skF_6', '#skF_8'), k2_xboole_0('#skF_7', '#skF_9'))) | ~r1_tarski('#skF_4', k2_zfmisc_1(k2_xboole_0('#skF_6', '#skF_8'), k2_xboole_0('#skF_7', '#skF_9')))), inference(resolution, [status(thm)], [c_187, c_46])).
% 6.86/2.36  tff(c_950, plain, (~r1_tarski('#skF_4', k2_zfmisc_1(k2_xboole_0('#skF_6', '#skF_8'), k2_xboole_0('#skF_7', '#skF_9')))), inference(splitLeft, [status(thm)], [c_203])).
% 6.86/2.36  tff(c_2012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1875, c_950])).
% 6.86/2.36  tff(c_2013, plain, (~r1_tarski('#skF_5', k2_zfmisc_1(k2_xboole_0('#skF_6', '#skF_8'), k2_xboole_0('#skF_7', '#skF_9')))), inference(splitRight, [status(thm)], [c_203])).
% 6.86/2.36  tff(c_6772, plain, (~r1_tarski('#skF_5', k2_zfmisc_1('#skF_8', k2_xboole_0('#skF_7', '#skF_9')))), inference(resolution, [status(thm)], [c_6745, c_2013])).
% 6.86/2.36  tff(c_6842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_680, c_6772])).
% 6.86/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.86/2.36  
% 6.86/2.36  Inference rules
% 6.86/2.36  ----------------------
% 6.86/2.36  #Ref     : 0
% 6.86/2.36  #Sup     : 1705
% 6.86/2.36  #Fact    : 10
% 6.86/2.36  #Define  : 0
% 6.86/2.36  #Split   : 6
% 6.86/2.36  #Chain   : 0
% 6.86/2.36  #Close   : 0
% 6.86/2.36  
% 6.86/2.36  Ordering : KBO
% 6.86/2.36  
% 6.86/2.36  Simplification rules
% 6.86/2.36  ----------------------
% 6.86/2.36  #Subsume      : 92
% 6.86/2.36  #Demod        : 683
% 6.86/2.36  #Tautology    : 658
% 6.86/2.36  #SimpNegUnit  : 0
% 6.86/2.36  #BackRed      : 1
% 6.86/2.36  
% 6.86/2.36  #Partial instantiations: 0
% 6.86/2.36  #Strategies tried      : 1
% 6.86/2.36  
% 6.86/2.36  Timing (in seconds)
% 6.86/2.36  ----------------------
% 6.86/2.36  Preprocessing        : 0.32
% 6.86/2.36  Parsing              : 0.17
% 6.86/2.36  CNF conversion       : 0.03
% 6.86/2.36  Main loop            : 1.29
% 6.86/2.36  Inferencing          : 0.36
% 6.86/2.36  Reduction            : 0.50
% 6.86/2.36  Demodulation         : 0.39
% 6.86/2.36  BG Simplification    : 0.05
% 6.86/2.36  Subsumption          : 0.30
% 6.86/2.36  Abstraction          : 0.06
% 6.86/2.36  MUC search           : 0.00
% 6.86/2.36  Cooper               : 0.00
% 6.86/2.36  Total                : 1.64
% 6.86/2.36  Index Insertion      : 0.00
% 6.86/2.36  Index Deletion       : 0.00
% 6.86/2.36  Index Matching       : 0.00
% 6.86/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
