%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:27 EST 2020

% Result     : Theorem 13.72s
% Output     : CNFRefutation 13.72s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 138 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   68 ( 267 expanded)
%              Number of equality atoms :   46 ( 162 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
    <=> ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [C_44,A_45,D_46] :
      ( r2_hidden(C_44,k1_relat_1(A_45))
      | ~ r2_hidden(k4_tarski(C_44,D_46),A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_91,plain,(
    ! [C_44,D_46] : r2_hidden(C_44,k1_relat_1(k1_tarski(k4_tarski(C_44,D_46)))) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_186,plain,(
    ! [C_83,A_84] :
      ( r2_hidden(k4_tarski(C_83,'#skF_6'(A_84,k1_relat_1(A_84),C_83)),A_84)
      | ~ r2_hidden(C_83,k1_relat_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [A_11,B_12] : k2_zfmisc_1(k1_tarski(A_11),k1_tarski(B_12)) = k1_tarski(k4_tarski(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [C_9,A_7,B_8,D_10] :
      ( C_9 = A_7
      | ~ r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(k1_tarski(C_9),k1_tarski(D_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_39,plain,(
    ! [C_9,A_7,B_8,D_10] :
      ( C_9 = A_7
      | ~ r2_hidden(k4_tarski(A_7,B_8),k1_tarski(k4_tarski(C_9,D_10))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20])).

tff(c_215,plain,(
    ! [C_86,C_85,D_87] :
      ( C_86 = C_85
      | ~ r2_hidden(C_86,k1_relat_1(k1_tarski(k4_tarski(C_85,D_87)))) ) ),
    inference(resolution,[status(thm)],[c_186,c_39])).

tff(c_7908,plain,(
    ! [A_682,C_683,D_684] :
      ( '#skF_2'(A_682,k1_relat_1(k1_tarski(k4_tarski(C_683,D_684)))) = C_683
      | '#skF_1'(A_682,k1_relat_1(k1_tarski(k4_tarski(C_683,D_684)))) = A_682
      | k1_tarski(A_682) = k1_relat_1(k1_tarski(k4_tarski(C_683,D_684))) ) ),
    inference(resolution,[status(thm)],[c_12,c_215])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7943,plain,(
    ! [C_683,D_684] :
      ( '#skF_1'(C_683,k1_relat_1(k1_tarski(k4_tarski(C_683,D_684)))) = C_683
      | k1_relat_1(k1_tarski(k4_tarski(C_683,D_684))) = k1_tarski(C_683) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7908,c_8])).

tff(c_301,plain,(
    ! [A_108,B_109] :
      ( ~ r2_hidden('#skF_1'(A_108,B_109),B_109)
      | r2_hidden('#skF_2'(A_108,B_109),B_109)
      | k1_tarski(A_108) = B_109 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_211,plain,(
    ! [C_9,C_83,D_10] :
      ( C_9 = C_83
      | ~ r2_hidden(C_83,k1_relat_1(k1_tarski(k4_tarski(C_9,D_10)))) ) ),
    inference(resolution,[status(thm)],[c_186,c_39])).

tff(c_16884,plain,(
    ! [A_1120,C_1121,D_1122] :
      ( '#skF_2'(A_1120,k1_relat_1(k1_tarski(k4_tarski(C_1121,D_1122)))) = C_1121
      | ~ r2_hidden('#skF_1'(A_1120,k1_relat_1(k1_tarski(k4_tarski(C_1121,D_1122)))),k1_relat_1(k1_tarski(k4_tarski(C_1121,D_1122))))
      | k1_tarski(A_1120) = k1_relat_1(k1_tarski(k4_tarski(C_1121,D_1122))) ) ),
    inference(resolution,[status(thm)],[c_301,c_211])).

tff(c_16899,plain,(
    ! [C_683,D_684] :
      ( '#skF_2'(C_683,k1_relat_1(k1_tarski(k4_tarski(C_683,D_684)))) = C_683
      | ~ r2_hidden(C_683,k1_relat_1(k1_tarski(k4_tarski(C_683,D_684))))
      | k1_relat_1(k1_tarski(k4_tarski(C_683,D_684))) = k1_tarski(C_683)
      | k1_relat_1(k1_tarski(k4_tarski(C_683,D_684))) = k1_tarski(C_683) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7943,c_16884])).

tff(c_16928,plain,(
    ! [C_1123,D_1124] :
      ( '#skF_2'(C_1123,k1_relat_1(k1_tarski(k4_tarski(C_1123,D_1124)))) = C_1123
      | k1_relat_1(k1_tarski(k4_tarski(C_1123,D_1124))) = k1_tarski(C_1123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_16899])).

tff(c_7946,plain,(
    ! [C_685,D_686] :
      ( '#skF_1'(C_685,k1_relat_1(k1_tarski(k4_tarski(C_685,D_686)))) = C_685
      | k1_relat_1(k1_tarski(k4_tarski(C_685,D_686))) = k1_tarski(C_685) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7908,c_8])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7952,plain,(
    ! [C_685,D_686] :
      ( ~ r2_hidden(C_685,k1_relat_1(k1_tarski(k4_tarski(C_685,D_686))))
      | '#skF_2'(C_685,k1_relat_1(k1_tarski(k4_tarski(C_685,D_686)))) != C_685
      | k1_relat_1(k1_tarski(k4_tarski(C_685,D_686))) = k1_tarski(C_685)
      | k1_relat_1(k1_tarski(k4_tarski(C_685,D_686))) = k1_tarski(C_685) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7946,c_6])).

tff(c_7970,plain,(
    ! [C_685,D_686] :
      ( '#skF_2'(C_685,k1_relat_1(k1_tarski(k4_tarski(C_685,D_686)))) != C_685
      | k1_relat_1(k1_tarski(k4_tarski(C_685,D_686))) = k1_tarski(C_685) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_7952])).

tff(c_16977,plain,(
    ! [C_1123,D_1124] : k1_relat_1(k1_tarski(k4_tarski(C_1123,D_1124))) = k1_tarski(C_1123) ),
    inference(superposition,[status(thm),theory(equality)],[c_16928,c_7970])).

tff(c_36,plain,(
    ! [A_32,B_33,C_34] : k4_tarski(k4_tarski(A_32,B_33),C_34) = k3_mcart_1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_17104,plain,(
    ! [C_1125,D_1126] : k1_relat_1(k1_tarski(k4_tarski(C_1125,D_1126))) = k1_tarski(C_1125) ),
    inference(superposition,[status(thm),theory(equality)],[c_16928,c_7970])).

tff(c_17279,plain,(
    ! [A_32,B_33,C_34] : k1_relat_1(k1_tarski(k3_mcart_1(A_32,B_33,C_34))) = k1_tarski(k4_tarski(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_17104])).

tff(c_38,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_7','#skF_8','#skF_9')))) != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_17422,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_7','#skF_8'))) != k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17279,c_38])).

tff(c_17448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16977,c_17422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.72/5.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.72/5.61  
% 13.72/5.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.72/5.61  %$ r2_hidden > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 13.72/5.61  
% 13.72/5.61  %Foreground sorts:
% 13.72/5.61  
% 13.72/5.61  
% 13.72/5.61  %Background operators:
% 13.72/5.61  
% 13.72/5.61  
% 13.72/5.61  %Foreground operators:
% 13.72/5.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.72/5.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.72/5.61  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 13.72/5.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.72/5.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.72/5.61  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 13.72/5.61  tff('#skF_7', type, '#skF_7': $i).
% 13.72/5.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.72/5.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.72/5.61  tff('#skF_9', type, '#skF_9': $i).
% 13.72/5.61  tff('#skF_8', type, '#skF_8': $i).
% 13.72/5.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.72/5.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.72/5.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.72/5.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.72/5.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.72/5.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.72/5.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.72/5.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.72/5.62  
% 13.72/5.63  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 13.72/5.63  tff(f_50, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 13.72/5.63  tff(f_42, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 13.72/5.63  tff(f_40, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 13.72/5.63  tff(f_52, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 13.72/5.63  tff(f_55, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_mcart_1)).
% 13.72/5.63  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.72/5.63  tff(c_83, plain, (![C_44, A_45, D_46]: (r2_hidden(C_44, k1_relat_1(A_45)) | ~r2_hidden(k4_tarski(C_44, D_46), A_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.72/5.63  tff(c_91, plain, (![C_44, D_46]: (r2_hidden(C_44, k1_relat_1(k1_tarski(k4_tarski(C_44, D_46)))))), inference(resolution, [status(thm)], [c_4, c_83])).
% 13.72/5.63  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.72/5.63  tff(c_186, plain, (![C_83, A_84]: (r2_hidden(k4_tarski(C_83, '#skF_6'(A_84, k1_relat_1(A_84), C_83)), A_84) | ~r2_hidden(C_83, k1_relat_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.72/5.63  tff(c_22, plain, (![A_11, B_12]: (k2_zfmisc_1(k1_tarski(A_11), k1_tarski(B_12))=k1_tarski(k4_tarski(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.72/5.63  tff(c_20, plain, (![C_9, A_7, B_8, D_10]: (C_9=A_7 | ~r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(k1_tarski(C_9), k1_tarski(D_10))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.72/5.63  tff(c_39, plain, (![C_9, A_7, B_8, D_10]: (C_9=A_7 | ~r2_hidden(k4_tarski(A_7, B_8), k1_tarski(k4_tarski(C_9, D_10))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20])).
% 13.72/5.63  tff(c_215, plain, (![C_86, C_85, D_87]: (C_86=C_85 | ~r2_hidden(C_86, k1_relat_1(k1_tarski(k4_tarski(C_85, D_87)))))), inference(resolution, [status(thm)], [c_186, c_39])).
% 13.72/5.63  tff(c_7908, plain, (![A_682, C_683, D_684]: ('#skF_2'(A_682, k1_relat_1(k1_tarski(k4_tarski(C_683, D_684))))=C_683 | '#skF_1'(A_682, k1_relat_1(k1_tarski(k4_tarski(C_683, D_684))))=A_682 | k1_tarski(A_682)=k1_relat_1(k1_tarski(k4_tarski(C_683, D_684))))), inference(resolution, [status(thm)], [c_12, c_215])).
% 13.72/5.63  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.72/5.63  tff(c_7943, plain, (![C_683, D_684]: ('#skF_1'(C_683, k1_relat_1(k1_tarski(k4_tarski(C_683, D_684))))=C_683 | k1_relat_1(k1_tarski(k4_tarski(C_683, D_684)))=k1_tarski(C_683))), inference(superposition, [status(thm), theory('equality')], [c_7908, c_8])).
% 13.72/5.63  tff(c_301, plain, (![A_108, B_109]: (~r2_hidden('#skF_1'(A_108, B_109), B_109) | r2_hidden('#skF_2'(A_108, B_109), B_109) | k1_tarski(A_108)=B_109)), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.72/5.63  tff(c_211, plain, (![C_9, C_83, D_10]: (C_9=C_83 | ~r2_hidden(C_83, k1_relat_1(k1_tarski(k4_tarski(C_9, D_10)))))), inference(resolution, [status(thm)], [c_186, c_39])).
% 13.72/5.63  tff(c_16884, plain, (![A_1120, C_1121, D_1122]: ('#skF_2'(A_1120, k1_relat_1(k1_tarski(k4_tarski(C_1121, D_1122))))=C_1121 | ~r2_hidden('#skF_1'(A_1120, k1_relat_1(k1_tarski(k4_tarski(C_1121, D_1122)))), k1_relat_1(k1_tarski(k4_tarski(C_1121, D_1122)))) | k1_tarski(A_1120)=k1_relat_1(k1_tarski(k4_tarski(C_1121, D_1122))))), inference(resolution, [status(thm)], [c_301, c_211])).
% 13.72/5.63  tff(c_16899, plain, (![C_683, D_684]: ('#skF_2'(C_683, k1_relat_1(k1_tarski(k4_tarski(C_683, D_684))))=C_683 | ~r2_hidden(C_683, k1_relat_1(k1_tarski(k4_tarski(C_683, D_684)))) | k1_relat_1(k1_tarski(k4_tarski(C_683, D_684)))=k1_tarski(C_683) | k1_relat_1(k1_tarski(k4_tarski(C_683, D_684)))=k1_tarski(C_683))), inference(superposition, [status(thm), theory('equality')], [c_7943, c_16884])).
% 13.72/5.63  tff(c_16928, plain, (![C_1123, D_1124]: ('#skF_2'(C_1123, k1_relat_1(k1_tarski(k4_tarski(C_1123, D_1124))))=C_1123 | k1_relat_1(k1_tarski(k4_tarski(C_1123, D_1124)))=k1_tarski(C_1123))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_16899])).
% 13.72/5.63  tff(c_7946, plain, (![C_685, D_686]: ('#skF_1'(C_685, k1_relat_1(k1_tarski(k4_tarski(C_685, D_686))))=C_685 | k1_relat_1(k1_tarski(k4_tarski(C_685, D_686)))=k1_tarski(C_685))), inference(superposition, [status(thm), theory('equality')], [c_7908, c_8])).
% 13.72/5.63  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.72/5.63  tff(c_7952, plain, (![C_685, D_686]: (~r2_hidden(C_685, k1_relat_1(k1_tarski(k4_tarski(C_685, D_686)))) | '#skF_2'(C_685, k1_relat_1(k1_tarski(k4_tarski(C_685, D_686))))!=C_685 | k1_relat_1(k1_tarski(k4_tarski(C_685, D_686)))=k1_tarski(C_685) | k1_relat_1(k1_tarski(k4_tarski(C_685, D_686)))=k1_tarski(C_685))), inference(superposition, [status(thm), theory('equality')], [c_7946, c_6])).
% 13.72/5.63  tff(c_7970, plain, (![C_685, D_686]: ('#skF_2'(C_685, k1_relat_1(k1_tarski(k4_tarski(C_685, D_686))))!=C_685 | k1_relat_1(k1_tarski(k4_tarski(C_685, D_686)))=k1_tarski(C_685))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_7952])).
% 13.72/5.63  tff(c_16977, plain, (![C_1123, D_1124]: (k1_relat_1(k1_tarski(k4_tarski(C_1123, D_1124)))=k1_tarski(C_1123))), inference(superposition, [status(thm), theory('equality')], [c_16928, c_7970])).
% 13.72/5.63  tff(c_36, plain, (![A_32, B_33, C_34]: (k4_tarski(k4_tarski(A_32, B_33), C_34)=k3_mcart_1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.72/5.63  tff(c_17104, plain, (![C_1125, D_1126]: (k1_relat_1(k1_tarski(k4_tarski(C_1125, D_1126)))=k1_tarski(C_1125))), inference(superposition, [status(thm), theory('equality')], [c_16928, c_7970])).
% 13.72/5.63  tff(c_17279, plain, (![A_32, B_33, C_34]: (k1_relat_1(k1_tarski(k3_mcart_1(A_32, B_33, C_34)))=k1_tarski(k4_tarski(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_17104])).
% 13.72/5.63  tff(c_38, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_7', '#skF_8', '#skF_9'))))!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.72/5.63  tff(c_17422, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_7', '#skF_8')))!=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_17279, c_38])).
% 13.72/5.63  tff(c_17448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16977, c_17422])).
% 13.72/5.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.72/5.63  
% 13.72/5.63  Inference rules
% 13.72/5.63  ----------------------
% 13.72/5.63  #Ref     : 0
% 13.72/5.63  #Sup     : 4539
% 13.72/5.63  #Fact    : 0
% 13.72/5.63  #Define  : 0
% 13.72/5.63  #Split   : 0
% 13.72/5.63  #Chain   : 0
% 13.72/5.63  #Close   : 0
% 13.72/5.63  
% 13.72/5.63  Ordering : KBO
% 13.72/5.63  
% 13.72/5.63  Simplification rules
% 13.72/5.63  ----------------------
% 13.72/5.63  #Subsume      : 599
% 13.72/5.63  #Demod        : 878
% 13.72/5.63  #Tautology    : 255
% 13.72/5.63  #SimpNegUnit  : 0
% 13.72/5.63  #BackRed      : 141
% 13.72/5.63  
% 13.72/5.63  #Partial instantiations: 0
% 13.72/5.63  #Strategies tried      : 1
% 13.72/5.63  
% 13.72/5.63  Timing (in seconds)
% 13.72/5.63  ----------------------
% 13.72/5.63  Preprocessing        : 0.30
% 13.72/5.63  Parsing              : 0.15
% 13.72/5.63  CNF conversion       : 0.02
% 13.72/5.63  Main loop            : 4.53
% 13.72/5.63  Inferencing          : 0.88
% 13.72/5.63  Reduction            : 0.87
% 13.72/5.63  Demodulation         : 0.64
% 13.72/5.63  BG Simplification    : 0.15
% 13.72/5.63  Subsumption          : 2.33
% 13.72/5.63  Abstraction          : 0.24
% 13.72/5.63  MUC search           : 0.00
% 13.72/5.63  Cooper               : 0.00
% 13.72/5.63  Total                : 4.85
% 13.72/5.63  Index Insertion      : 0.00
% 13.72/5.63  Index Deletion       : 0.00
% 13.72/5.63  Index Matching       : 0.00
% 13.72/5.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
