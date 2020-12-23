%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:20 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   52 (  78 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 ( 127 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,B)
         => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_1'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_40])).

tff(c_10,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k2_zfmisc_1(k1_relat_1(A_11),k2_relat_1(A_11)))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [C_24,B_25,A_26] :
      ( r2_hidden(C_24,B_25)
      | ~ r2_hidden(C_24,A_26)
      | ~ r1_tarski(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    ! [B_27] :
      ( r2_hidden('#skF_4',B_27)
      | ~ r1_tarski('#skF_5',B_27) ) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [B_28,B_29] :
      ( r2_hidden('#skF_4',B_28)
      | ~ r1_tarski(B_29,B_28)
      | ~ r1_tarski('#skF_5',B_29) ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_64,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_4',k2_zfmisc_1(k1_relat_1(A_11),k2_relat_1(A_11)))
      | ~ r1_tarski('#skF_5',A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(resolution,[status(thm)],[c_10,c_59])).

tff(c_16,plain,(
    k4_tarski(k1_mcart_1('#skF_4'),k2_mcart_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    ! [B_25] :
      ( r2_hidden('#skF_4',B_25)
      | ~ r1_tarski('#skF_5',B_25) ) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_86,plain,(
    ! [A_38,B_39,C_40] :
      ( k4_tarski('#skF_2'(A_38,B_39,C_40),'#skF_3'(A_38,B_39,C_40)) = A_38
      | ~ r2_hidden(A_38,k2_zfmisc_1(B_39,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_mcart_1(k4_tarski(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_mcart_1(A_41) = '#skF_2'(A_41,B_42,C_43)
      | ~ r2_hidden(A_41,k2_zfmisc_1(B_42,C_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_12])).

tff(c_141,plain,(
    ! [B_47,C_48] :
      ( k1_mcart_1('#skF_4') = '#skF_2'('#skF_4',B_47,C_48)
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(B_47,C_48)) ) ),
    inference(resolution,[status(thm)],[c_54,c_101])).

tff(c_145,plain,
    ( '#skF_2'('#skF_4',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) = k1_mcart_1('#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_141])).

tff(c_148,plain,(
    '#skF_2'('#skF_4',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) = k1_mcart_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_145])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_mcart_1(k4_tarski(A_12,B_13)) = B_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    ! [A_44,B_45,C_46] :
      ( k2_mcart_1(A_44) = '#skF_3'(A_44,B_45,C_46)
      | ~ r2_hidden(A_44,k2_zfmisc_1(B_45,C_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_14])).

tff(c_149,plain,(
    ! [B_49,C_50] :
      ( k2_mcart_1('#skF_4') = '#skF_3'('#skF_4',B_49,C_50)
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(B_49,C_50)) ) ),
    inference(resolution,[status(thm)],[c_54,c_121])).

tff(c_153,plain,
    ( '#skF_3'('#skF_4',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) = k2_mcart_1('#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_149])).

tff(c_156,plain,(
    '#skF_3'('#skF_4',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) = k2_mcart_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_153])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( k4_tarski('#skF_2'(A_6,B_7,C_8),'#skF_3'(A_6,B_7,C_8)) = A_6
      | ~ r2_hidden(A_6,k2_zfmisc_1(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_167,plain,
    ( k4_tarski('#skF_2'('#skF_4',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')),k2_mcart_1('#skF_4')) = '#skF_4'
    | ~ r2_hidden('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_8])).

tff(c_170,plain,
    ( k4_tarski(k1_mcart_1('#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | ~ r2_hidden('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_167])).

tff(c_171,plain,(
    ~ r2_hidden('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_170])).

tff(c_175,plain,
    ( ~ r1_tarski('#skF_5','#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_171])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_45,c_175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:06:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.35  
% 2.08/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.35  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.08/1.35  
% 2.08/1.35  %Foreground sorts:
% 2.08/1.35  
% 2.08/1.35  
% 2.08/1.35  %Background operators:
% 2.08/1.35  
% 2.08/1.35  
% 2.08/1.35  %Foreground operators:
% 2.08/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.08/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.35  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.08/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.08/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.35  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.08/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.35  
% 2.08/1.37  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.08/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.08/1.37  tff(f_43, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.08/1.37  tff(f_39, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.08/1.37  tff(f_47, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.08/1.37  tff(c_20, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.37  tff(c_40, plain, (![A_20, B_21]: (~r2_hidden('#skF_1'(A_20, B_21), B_21) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.37  tff(c_45, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_40])).
% 2.08/1.37  tff(c_10, plain, (![A_11]: (r1_tarski(A_11, k2_zfmisc_1(k1_relat_1(A_11), k2_relat_1(A_11))) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.37  tff(c_18, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.37  tff(c_48, plain, (![C_24, B_25, A_26]: (r2_hidden(C_24, B_25) | ~r2_hidden(C_24, A_26) | ~r1_tarski(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.37  tff(c_55, plain, (![B_27]: (r2_hidden('#skF_4', B_27) | ~r1_tarski('#skF_5', B_27))), inference(resolution, [status(thm)], [c_18, c_48])).
% 2.08/1.37  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.37  tff(c_59, plain, (![B_28, B_29]: (r2_hidden('#skF_4', B_28) | ~r1_tarski(B_29, B_28) | ~r1_tarski('#skF_5', B_29))), inference(resolution, [status(thm)], [c_55, c_2])).
% 2.08/1.37  tff(c_64, plain, (![A_11]: (r2_hidden('#skF_4', k2_zfmisc_1(k1_relat_1(A_11), k2_relat_1(A_11))) | ~r1_tarski('#skF_5', A_11) | ~v1_relat_1(A_11))), inference(resolution, [status(thm)], [c_10, c_59])).
% 2.08/1.37  tff(c_16, plain, (k4_tarski(k1_mcart_1('#skF_4'), k2_mcart_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.37  tff(c_54, plain, (![B_25]: (r2_hidden('#skF_4', B_25) | ~r1_tarski('#skF_5', B_25))), inference(resolution, [status(thm)], [c_18, c_48])).
% 2.08/1.37  tff(c_86, plain, (![A_38, B_39, C_40]: (k4_tarski('#skF_2'(A_38, B_39, C_40), '#skF_3'(A_38, B_39, C_40))=A_38 | ~r2_hidden(A_38, k2_zfmisc_1(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.37  tff(c_12, plain, (![A_12, B_13]: (k1_mcart_1(k4_tarski(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.37  tff(c_101, plain, (![A_41, B_42, C_43]: (k1_mcart_1(A_41)='#skF_2'(A_41, B_42, C_43) | ~r2_hidden(A_41, k2_zfmisc_1(B_42, C_43)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_12])).
% 2.08/1.37  tff(c_141, plain, (![B_47, C_48]: (k1_mcart_1('#skF_4')='#skF_2'('#skF_4', B_47, C_48) | ~r1_tarski('#skF_5', k2_zfmisc_1(B_47, C_48)))), inference(resolution, [status(thm)], [c_54, c_101])).
% 2.08/1.37  tff(c_145, plain, ('#skF_2'('#skF_4', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))=k1_mcart_1('#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_141])).
% 2.08/1.37  tff(c_148, plain, ('#skF_2'('#skF_4', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))=k1_mcart_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_145])).
% 2.08/1.37  tff(c_14, plain, (![A_12, B_13]: (k2_mcart_1(k4_tarski(A_12, B_13))=B_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.37  tff(c_121, plain, (![A_44, B_45, C_46]: (k2_mcart_1(A_44)='#skF_3'(A_44, B_45, C_46) | ~r2_hidden(A_44, k2_zfmisc_1(B_45, C_46)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_14])).
% 2.08/1.37  tff(c_149, plain, (![B_49, C_50]: (k2_mcart_1('#skF_4')='#skF_3'('#skF_4', B_49, C_50) | ~r1_tarski('#skF_5', k2_zfmisc_1(B_49, C_50)))), inference(resolution, [status(thm)], [c_54, c_121])).
% 2.08/1.37  tff(c_153, plain, ('#skF_3'('#skF_4', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))=k2_mcart_1('#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_149])).
% 2.08/1.37  tff(c_156, plain, ('#skF_3'('#skF_4', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))=k2_mcart_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_153])).
% 2.08/1.37  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_tarski('#skF_2'(A_6, B_7, C_8), '#skF_3'(A_6, B_7, C_8))=A_6 | ~r2_hidden(A_6, k2_zfmisc_1(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.37  tff(c_167, plain, (k4_tarski('#skF_2'('#skF_4', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')), k2_mcart_1('#skF_4'))='#skF_4' | ~r2_hidden('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_156, c_8])).
% 2.08/1.37  tff(c_170, plain, (k4_tarski(k1_mcart_1('#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | ~r2_hidden('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_167])).
% 2.08/1.37  tff(c_171, plain, (~r2_hidden('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_16, c_170])).
% 2.08/1.37  tff(c_175, plain, (~r1_tarski('#skF_5', '#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_171])).
% 2.08/1.37  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_45, c_175])).
% 2.08/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.37  
% 2.08/1.37  Inference rules
% 2.08/1.37  ----------------------
% 2.08/1.37  #Ref     : 0
% 2.08/1.37  #Sup     : 37
% 2.08/1.37  #Fact    : 0
% 2.08/1.37  #Define  : 0
% 2.08/1.37  #Split   : 0
% 2.08/1.37  #Chain   : 0
% 2.08/1.37  #Close   : 0
% 2.08/1.37  
% 2.08/1.37  Ordering : KBO
% 2.08/1.37  
% 2.08/1.37  Simplification rules
% 2.08/1.37  ----------------------
% 2.08/1.37  #Subsume      : 2
% 2.08/1.37  #Demod        : 5
% 2.08/1.37  #Tautology    : 11
% 2.08/1.37  #SimpNegUnit  : 1
% 2.08/1.37  #BackRed      : 0
% 2.08/1.37  
% 2.08/1.37  #Partial instantiations: 0
% 2.08/1.37  #Strategies tried      : 1
% 2.08/1.37  
% 2.08/1.37  Timing (in seconds)
% 2.08/1.37  ----------------------
% 2.23/1.37  Preprocessing        : 0.33
% 2.23/1.37  Parsing              : 0.20
% 2.23/1.37  CNF conversion       : 0.02
% 2.23/1.37  Main loop            : 0.20
% 2.23/1.37  Inferencing          : 0.09
% 2.23/1.37  Reduction            : 0.05
% 2.23/1.37  Demodulation         : 0.04
% 2.23/1.37  BG Simplification    : 0.01
% 2.23/1.37  Subsumption          : 0.03
% 2.23/1.37  Abstraction          : 0.01
% 2.23/1.37  MUC search           : 0.00
% 2.23/1.37  Cooper               : 0.00
% 2.23/1.37  Total                : 0.57
% 2.23/1.37  Index Insertion      : 0.00
% 2.23/1.37  Index Deletion       : 0.00
% 2.23/1.37  Index Matching       : 0.00
% 2.23/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
