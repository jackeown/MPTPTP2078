%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:08 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   46 (  79 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 ( 127 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(A,k3_zfmisc_1(B,C,D))
          & ! [E,F,G] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & r2_hidden(G,D)
                & A = k3_mcart_1(E,F,G) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_27,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_16,plain,(
    r2_hidden('#skF_1',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_35,plain,(
    ! [A_31,B_32,C_33] : k2_zfmisc_1(k2_zfmisc_1(A_31,B_32),C_33) = k3_zfmisc_1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_9,C_11,B_10] :
      ( r2_hidden(k2_mcart_1(A_9),C_11)
      | ~ r2_hidden(A_9,k2_zfmisc_1(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_57,plain,(
    ! [A_37,C_38,A_39,B_40] :
      ( r2_hidden(k2_mcart_1(A_37),C_38)
      | ~ r2_hidden(A_37,k3_zfmisc_1(A_39,B_40,C_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_8])).

tff(c_60,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_57])).

tff(c_2,plain,(
    ! [A_1,B_2] : v1_relat_1(k2_zfmisc_1(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_47,plain,(
    ! [A_31,B_32,C_33] : v1_relat_1(k3_zfmisc_1(A_31,B_32,C_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_2])).

tff(c_62,plain,(
    ! [A_44,B_45] :
      ( k4_tarski(k1_mcart_1(A_44),k2_mcart_1(A_44)) = A_44
      | ~ r2_hidden(A_44,B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,
    ( k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_16,c_62])).

tff(c_70,plain,(
    k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_66])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden(k1_mcart_1(A_9),B_10)
      | ~ r2_hidden(A_9,k2_zfmisc_1(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [A_47,A_48,B_49,C_50] :
      ( r2_hidden(k1_mcart_1(A_47),k2_zfmisc_1(A_48,B_49))
      | ~ r2_hidden(A_47,k3_zfmisc_1(A_48,B_49,C_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_10])).

tff(c_93,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_90])).

tff(c_104,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_1')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_10])).

tff(c_103,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_8])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k4_tarski(k1_mcart_1(A_12),k2_mcart_1(A_12)) = A_12
      | ~ r2_hidden(A_12,B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_1')),k2_mcart_1(k1_mcart_1('#skF_1'))) = k1_mcart_1('#skF_1')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_93,c_12])).

tff(c_102,plain,(
    k4_tarski(k1_mcart_1(k1_mcart_1('#skF_1')),k2_mcart_1(k1_mcart_1('#skF_1'))) = k1_mcart_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_95])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k4_tarski(k4_tarski(A_3,B_4),C_5) = k3_mcart_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_164,plain,(
    ! [C_59] : k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')),k2_mcart_1(k1_mcart_1('#skF_1')),C_59) = k4_tarski(k1_mcart_1('#skF_1'),C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_4])).

tff(c_14,plain,(
    ! [E_17,F_18,G_19] :
      ( k3_mcart_1(E_17,F_18,G_19) != '#skF_1'
      | ~ r2_hidden(G_19,'#skF_4')
      | ~ r2_hidden(F_18,'#skF_3')
      | ~ r2_hidden(E_17,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_169,plain,(
    ! [C_59] :
      ( k4_tarski(k1_mcart_1('#skF_1'),C_59) != '#skF_1'
      | ~ r2_hidden(C_59,'#skF_4')
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1')),'#skF_3')
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_1')),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_14])).

tff(c_177,plain,(
    ! [C_60] :
      ( k4_tarski(k1_mcart_1('#skF_1'),C_60) != '#skF_1'
      | ~ r2_hidden(C_60,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_103,c_169])).

tff(c_180,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_177])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:59:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  %$ r2_hidden > v1_relat_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.19  
% 1.93/1.19  %Foreground sorts:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Background operators:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Foreground operators:
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.93/1.19  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.93/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.19  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.19  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.93/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.19  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.93/1.19  
% 1.93/1.21  tff(f_57, negated_conjecture, ~(![A, B, C, D]: ~(r2_hidden(A, k3_zfmisc_1(B, C, D)) & (![E, F, G]: ~(((r2_hidden(E, B) & r2_hidden(F, C)) & r2_hidden(G, D)) & (A = k3_mcart_1(E, F, G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_mcart_1)).
% 1.93/1.21  tff(f_31, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 1.93/1.21  tff(f_37, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.93/1.21  tff(f_27, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.93/1.21  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.93/1.21  tff(f_29, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.93/1.21  tff(c_16, plain, (r2_hidden('#skF_1', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.21  tff(c_35, plain, (![A_31, B_32, C_33]: (k2_zfmisc_1(k2_zfmisc_1(A_31, B_32), C_33)=k3_zfmisc_1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.21  tff(c_8, plain, (![A_9, C_11, B_10]: (r2_hidden(k2_mcart_1(A_9), C_11) | ~r2_hidden(A_9, k2_zfmisc_1(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.21  tff(c_57, plain, (![A_37, C_38, A_39, B_40]: (r2_hidden(k2_mcart_1(A_37), C_38) | ~r2_hidden(A_37, k3_zfmisc_1(A_39, B_40, C_38)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_8])).
% 1.93/1.21  tff(c_60, plain, (r2_hidden(k2_mcart_1('#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_16, c_57])).
% 1.93/1.21  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.21  tff(c_47, plain, (![A_31, B_32, C_33]: (v1_relat_1(k3_zfmisc_1(A_31, B_32, C_33)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_2])).
% 1.93/1.21  tff(c_62, plain, (![A_44, B_45]: (k4_tarski(k1_mcart_1(A_44), k2_mcart_1(A_44))=A_44 | ~r2_hidden(A_44, B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.93/1.21  tff(c_66, plain, (k4_tarski(k1_mcart_1('#skF_1'), k2_mcart_1('#skF_1'))='#skF_1' | ~v1_relat_1(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_62])).
% 1.93/1.21  tff(c_70, plain, (k4_tarski(k1_mcart_1('#skF_1'), k2_mcart_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_66])).
% 1.93/1.21  tff(c_10, plain, (![A_9, B_10, C_11]: (r2_hidden(k1_mcart_1(A_9), B_10) | ~r2_hidden(A_9, k2_zfmisc_1(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.21  tff(c_90, plain, (![A_47, A_48, B_49, C_50]: (r2_hidden(k1_mcart_1(A_47), k2_zfmisc_1(A_48, B_49)) | ~r2_hidden(A_47, k3_zfmisc_1(A_48, B_49, C_50)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_10])).
% 1.93/1.21  tff(c_93, plain, (r2_hidden(k1_mcart_1('#skF_1'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_90])).
% 1.93/1.21  tff(c_104, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_1')), '#skF_2')), inference(resolution, [status(thm)], [c_93, c_10])).
% 1.93/1.21  tff(c_103, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1')), '#skF_3')), inference(resolution, [status(thm)], [c_93, c_8])).
% 1.93/1.21  tff(c_12, plain, (![A_12, B_13]: (k4_tarski(k1_mcart_1(A_12), k2_mcart_1(A_12))=A_12 | ~r2_hidden(A_12, B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.93/1.21  tff(c_95, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_1')), k2_mcart_1(k1_mcart_1('#skF_1')))=k1_mcart_1('#skF_1') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_93, c_12])).
% 1.93/1.21  tff(c_102, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_1')), k2_mcart_1(k1_mcart_1('#skF_1')))=k1_mcart_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_95])).
% 1.93/1.21  tff(c_4, plain, (![A_3, B_4, C_5]: (k4_tarski(k4_tarski(A_3, B_4), C_5)=k3_mcart_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.21  tff(c_164, plain, (![C_59]: (k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')), k2_mcart_1(k1_mcart_1('#skF_1')), C_59)=k4_tarski(k1_mcart_1('#skF_1'), C_59))), inference(superposition, [status(thm), theory('equality')], [c_102, c_4])).
% 1.93/1.21  tff(c_14, plain, (![E_17, F_18, G_19]: (k3_mcart_1(E_17, F_18, G_19)!='#skF_1' | ~r2_hidden(G_19, '#skF_4') | ~r2_hidden(F_18, '#skF_3') | ~r2_hidden(E_17, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.21  tff(c_169, plain, (![C_59]: (k4_tarski(k1_mcart_1('#skF_1'), C_59)!='#skF_1' | ~r2_hidden(C_59, '#skF_4') | ~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1')), '#skF_3') | ~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_1')), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_14])).
% 1.93/1.21  tff(c_177, plain, (![C_60]: (k4_tarski(k1_mcart_1('#skF_1'), C_60)!='#skF_1' | ~r2_hidden(C_60, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_103, c_169])).
% 1.93/1.21  tff(c_180, plain, (~r2_hidden(k2_mcart_1('#skF_1'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_70, c_177])).
% 1.93/1.21  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_180])).
% 1.93/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  Inference rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Ref     : 0
% 1.93/1.21  #Sup     : 45
% 1.93/1.21  #Fact    : 0
% 1.93/1.21  #Define  : 0
% 1.93/1.21  #Split   : 2
% 1.93/1.21  #Chain   : 0
% 1.93/1.21  #Close   : 0
% 1.93/1.21  
% 1.93/1.21  Ordering : KBO
% 1.93/1.21  
% 1.93/1.21  Simplification rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Subsume      : 2
% 1.93/1.21  #Demod        : 15
% 1.93/1.21  #Tautology    : 22
% 1.93/1.21  #SimpNegUnit  : 0
% 1.93/1.21  #BackRed      : 0
% 1.93/1.21  
% 1.93/1.21  #Partial instantiations: 0
% 1.93/1.21  #Strategies tried      : 1
% 1.93/1.21  
% 1.93/1.21  Timing (in seconds)
% 1.93/1.21  ----------------------
% 1.93/1.21  Preprocessing        : 0.27
% 1.93/1.21  Parsing              : 0.15
% 1.93/1.21  CNF conversion       : 0.02
% 1.93/1.21  Main loop            : 0.19
% 1.93/1.21  Inferencing          : 0.08
% 1.93/1.21  Reduction            : 0.05
% 1.93/1.21  Demodulation         : 0.04
% 1.93/1.21  BG Simplification    : 0.01
% 1.93/1.21  Subsumption          : 0.03
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.48
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
