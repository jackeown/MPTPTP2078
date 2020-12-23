%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:53 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 141 expanded)
%              Number of leaves         :   28 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 ( 168 expanded)
%              Number of equality atoms :   15 (  84 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,D) )
       => m1_subset_1(k1_tarski(k4_tarski(A,C)),k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    ! [A_43,B_44,C_45,D_46] : k3_enumset1(A_43,A_43,B_44,C_45,D_46) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : k3_enumset1(A_6,A_6,A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [C_50,D_51] : k2_enumset1(C_50,C_50,C_50,D_51) = k2_tarski(C_50,D_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_6])).

tff(c_4,plain,(
    ! [A_5] : k2_enumset1(A_5,A_5,A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    ! [D_52] : k2_tarski(D_52,D_52) = k1_tarski(D_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_4])).

tff(c_24,plain,(
    ! [A_21,B_22,C_23] :
      ( r1_tarski(k2_tarski(A_21,B_22),C_23)
      | ~ r2_hidden(B_22,C_23)
      | ~ r2_hidden(A_21,C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_128,plain,(
    ! [D_52,C_23] :
      ( r1_tarski(k1_tarski(D_52),C_23)
      | ~ r2_hidden(D_52,C_23)
      | ~ r2_hidden(D_52,C_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_24])).

tff(c_36,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_113,plain,(
    ! [D_51] : k2_tarski(D_51,D_51) = k1_tarski(D_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_4])).

tff(c_179,plain,(
    ! [A_69,C_70,D_71,B_72] : k2_enumset1(k4_tarski(A_69,C_70),k4_tarski(A_69,D_71),k4_tarski(B_72,C_70),k4_tarski(B_72,D_71)) = k2_zfmisc_1(k2_tarski(A_69,B_72),k2_tarski(C_70,D_71)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    ! [C_45,D_46] : k2_enumset1(C_45,C_45,C_45,D_46) = k2_tarski(C_45,D_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_6])).

tff(c_186,plain,(
    ! [B_72,D_71] : k2_zfmisc_1(k2_tarski(B_72,B_72),k2_tarski(D_71,D_71)) = k2_tarski(k4_tarski(B_72,D_71),k4_tarski(B_72,D_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_88])).

tff(c_208,plain,(
    ! [B_73,D_74] : k2_zfmisc_1(k1_tarski(B_73),k1_tarski(D_74)) = k1_tarski(k4_tarski(B_73,D_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_113,c_186])).

tff(c_20,plain,(
    ! [A_13,C_15,B_14,D_16] :
      ( r1_tarski(k2_zfmisc_1(A_13,C_15),k2_zfmisc_1(B_14,D_16))
      | ~ r1_tarski(C_15,D_16)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_246,plain,(
    ! [B_83,D_84,B_85,D_86] :
      ( r1_tarski(k1_tarski(k4_tarski(B_83,D_84)),k2_zfmisc_1(B_85,D_86))
      | ~ r1_tarski(k1_tarski(D_84),D_86)
      | ~ r1_tarski(k1_tarski(B_83),B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_20])).

tff(c_56,plain,(
    ! [C_31,A_32] :
      ( r2_hidden(C_31,k1_zfmisc_1(A_32))
      | ~ r1_tarski(C_31,A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    ! [C_31,A_32] :
      ( m1_subset_1(C_31,k1_zfmisc_1(A_32))
      | ~ r1_tarski(C_31,A_32) ) ),
    inference(resolution,[status(thm)],[c_56,c_30])).

tff(c_32,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_3','#skF_5')),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_69,plain,(
    ~ r1_tarski(k1_tarski(k4_tarski('#skF_3','#skF_5')),k2_zfmisc_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_32])).

tff(c_257,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_246,c_69])).

tff(c_258,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_261,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_258])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_261])).

tff(c_266,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_270,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_128,c_266])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:41:10 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.32  
% 2.28/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.28/1.32  
% 2.28/1.32  %Foreground sorts:
% 2.28/1.32  
% 2.28/1.32  
% 2.28/1.32  %Background operators:
% 2.28/1.32  
% 2.28/1.32  
% 2.28/1.32  %Foreground operators:
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.28/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.28/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.28/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.32  
% 2.28/1.34  tff(f_63, negated_conjecture, ~(![A, B, C, D]: ((r2_hidden(A, B) & r2_hidden(C, D)) => m1_subset_1(k1_tarski(k4_tarski(A, C)), k1_zfmisc_1(k2_zfmisc_1(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_relset_1)).
% 2.28/1.34  tff(f_27, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.28/1.34  tff(f_31, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_enumset1)).
% 2.28/1.34  tff(f_29, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 2.28/1.34  tff(f_52, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.28/1.34  tff(f_46, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 2.28/1.34  tff(f_44, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 2.28/1.34  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.28/1.34  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.28/1.34  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.34  tff(c_81, plain, (![A_43, B_44, C_45, D_46]: (k3_enumset1(A_43, A_43, B_44, C_45, D_46)=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.34  tff(c_6, plain, (![A_6, B_7]: (k3_enumset1(A_6, A_6, A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.34  tff(c_106, plain, (![C_50, D_51]: (k2_enumset1(C_50, C_50, C_50, D_51)=k2_tarski(C_50, D_51))), inference(superposition, [status(thm), theory('equality')], [c_81, c_6])).
% 2.28/1.34  tff(c_4, plain, (![A_5]: (k2_enumset1(A_5, A_5, A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.34  tff(c_122, plain, (![D_52]: (k2_tarski(D_52, D_52)=k1_tarski(D_52))), inference(superposition, [status(thm), theory('equality')], [c_106, c_4])).
% 2.28/1.34  tff(c_24, plain, (![A_21, B_22, C_23]: (r1_tarski(k2_tarski(A_21, B_22), C_23) | ~r2_hidden(B_22, C_23) | ~r2_hidden(A_21, C_23))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.34  tff(c_128, plain, (![D_52, C_23]: (r1_tarski(k1_tarski(D_52), C_23) | ~r2_hidden(D_52, C_23) | ~r2_hidden(D_52, C_23))), inference(superposition, [status(thm), theory('equality')], [c_122, c_24])).
% 2.28/1.34  tff(c_36, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.34  tff(c_113, plain, (![D_51]: (k2_tarski(D_51, D_51)=k1_tarski(D_51))), inference(superposition, [status(thm), theory('equality')], [c_106, c_4])).
% 2.28/1.34  tff(c_179, plain, (![A_69, C_70, D_71, B_72]: (k2_enumset1(k4_tarski(A_69, C_70), k4_tarski(A_69, D_71), k4_tarski(B_72, C_70), k4_tarski(B_72, D_71))=k2_zfmisc_1(k2_tarski(A_69, B_72), k2_tarski(C_70, D_71)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.28/1.34  tff(c_88, plain, (![C_45, D_46]: (k2_enumset1(C_45, C_45, C_45, D_46)=k2_tarski(C_45, D_46))), inference(superposition, [status(thm), theory('equality')], [c_81, c_6])).
% 2.28/1.34  tff(c_186, plain, (![B_72, D_71]: (k2_zfmisc_1(k2_tarski(B_72, B_72), k2_tarski(D_71, D_71))=k2_tarski(k4_tarski(B_72, D_71), k4_tarski(B_72, D_71)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_88])).
% 2.28/1.34  tff(c_208, plain, (![B_73, D_74]: (k2_zfmisc_1(k1_tarski(B_73), k1_tarski(D_74))=k1_tarski(k4_tarski(B_73, D_74)))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_113, c_113, c_186])).
% 2.28/1.34  tff(c_20, plain, (![A_13, C_15, B_14, D_16]: (r1_tarski(k2_zfmisc_1(A_13, C_15), k2_zfmisc_1(B_14, D_16)) | ~r1_tarski(C_15, D_16) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.34  tff(c_246, plain, (![B_83, D_84, B_85, D_86]: (r1_tarski(k1_tarski(k4_tarski(B_83, D_84)), k2_zfmisc_1(B_85, D_86)) | ~r1_tarski(k1_tarski(D_84), D_86) | ~r1_tarski(k1_tarski(B_83), B_85))), inference(superposition, [status(thm), theory('equality')], [c_208, c_20])).
% 2.28/1.34  tff(c_56, plain, (![C_31, A_32]: (r2_hidden(C_31, k1_zfmisc_1(A_32)) | ~r1_tarski(C_31, A_32))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.28/1.34  tff(c_30, plain, (![A_24, B_25]: (m1_subset_1(A_24, B_25) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.28/1.34  tff(c_64, plain, (![C_31, A_32]: (m1_subset_1(C_31, k1_zfmisc_1(A_32)) | ~r1_tarski(C_31, A_32))), inference(resolution, [status(thm)], [c_56, c_30])).
% 2.28/1.34  tff(c_32, plain, (~m1_subset_1(k1_tarski(k4_tarski('#skF_3', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.34  tff(c_69, plain, (~r1_tarski(k1_tarski(k4_tarski('#skF_3', '#skF_5')), k2_zfmisc_1('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_32])).
% 2.28/1.34  tff(c_257, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6') | ~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_246, c_69])).
% 2.28/1.34  tff(c_258, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_257])).
% 2.28/1.34  tff(c_261, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_128, c_258])).
% 2.28/1.34  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_261])).
% 2.28/1.34  tff(c_266, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_257])).
% 2.28/1.34  tff(c_270, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_128, c_266])).
% 2.28/1.34  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_270])).
% 2.28/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.34  
% 2.28/1.34  Inference rules
% 2.28/1.34  ----------------------
% 2.28/1.34  #Ref     : 0
% 2.28/1.34  #Sup     : 49
% 2.28/1.34  #Fact    : 0
% 2.28/1.34  #Define  : 0
% 2.28/1.34  #Split   : 1
% 2.28/1.34  #Chain   : 0
% 2.28/1.34  #Close   : 0
% 2.28/1.34  
% 2.28/1.34  Ordering : KBO
% 2.28/1.34  
% 2.28/1.34  Simplification rules
% 2.28/1.34  ----------------------
% 2.28/1.34  #Subsume      : 1
% 2.28/1.34  #Demod        : 17
% 2.28/1.34  #Tautology    : 25
% 2.28/1.34  #SimpNegUnit  : 0
% 2.28/1.34  #BackRed      : 0
% 2.28/1.34  
% 2.28/1.34  #Partial instantiations: 0
% 2.28/1.34  #Strategies tried      : 1
% 2.28/1.34  
% 2.28/1.34  Timing (in seconds)
% 2.28/1.34  ----------------------
% 2.28/1.34  Preprocessing        : 0.32
% 2.28/1.34  Parsing              : 0.16
% 2.28/1.34  CNF conversion       : 0.02
% 2.28/1.34  Main loop            : 0.21
% 2.28/1.34  Inferencing          : 0.09
% 2.28/1.34  Reduction            : 0.06
% 2.28/1.34  Demodulation         : 0.04
% 2.28/1.34  BG Simplification    : 0.01
% 2.28/1.34  Subsumption          : 0.03
% 2.28/1.34  Abstraction          : 0.01
% 2.28/1.34  MUC search           : 0.00
% 2.28/1.34  Cooper               : 0.00
% 2.28/1.34  Total                : 0.56
% 2.28/1.34  Index Insertion      : 0.00
% 2.28/1.34  Index Deletion       : 0.00
% 2.28/1.34  Index Matching       : 0.00
% 2.28/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
