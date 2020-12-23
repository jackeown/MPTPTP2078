%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:20 EST 2020

% Result     : Theorem 4.97s
% Output     : CNFRefutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 ( 120 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
                & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_32,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11'))
    | ~ r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_53,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,(
    ! [C_62,A_63] :
      ( r2_hidden(k4_tarski(C_62,'#skF_5'(A_63,k1_relat_1(A_63),C_62)),A_63)
      | ~ r2_hidden(C_62,k1_relat_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1272,plain,(
    ! [C_176,A_177,B_178] :
      ( r2_hidden(k4_tarski(C_176,'#skF_5'(A_177,k1_relat_1(A_177),C_176)),B_178)
      | ~ r1_tarski(A_177,B_178)
      | ~ r2_hidden(C_176,k1_relat_1(A_177)) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1292,plain,(
    ! [C_179,B_180,A_181] :
      ( r2_hidden(C_179,k1_relat_1(B_180))
      | ~ r1_tarski(A_181,B_180)
      | ~ r2_hidden(C_179,k1_relat_1(A_181)) ) ),
    inference(resolution,[status(thm)],[c_1272,c_10])).

tff(c_1305,plain,(
    ! [C_182] :
      ( r2_hidden(C_182,k1_relat_1('#skF_11'))
      | ~ r2_hidden(C_182,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_34,c_1292])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1511,plain,(
    ! [A_191] :
      ( r1_tarski(A_191,k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_1'(A_191,k1_relat_1('#skF_11')),k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1305,c_4])).

tff(c_1523,plain,(
    r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_1511])).

tff(c_1529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_53,c_1523])).

tff(c_1530,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1557,plain,(
    ! [A_199,C_200] :
      ( r2_hidden(k4_tarski('#skF_9'(A_199,k2_relat_1(A_199),C_200),C_200),A_199)
      | ~ r2_hidden(C_200,k2_relat_1(A_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2747,plain,(
    ! [A_310,C_311,B_312] :
      ( r2_hidden(k4_tarski('#skF_9'(A_310,k2_relat_1(A_310),C_311),C_311),B_312)
      | ~ r1_tarski(A_310,B_312)
      | ~ r2_hidden(C_311,k2_relat_1(A_310)) ) ),
    inference(resolution,[status(thm)],[c_1557,c_2])).

tff(c_22,plain,(
    ! [C_40,A_25,D_43] :
      ( r2_hidden(C_40,k2_relat_1(A_25))
      | ~ r2_hidden(k4_tarski(D_43,C_40),A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2767,plain,(
    ! [C_313,B_314,A_315] :
      ( r2_hidden(C_313,k2_relat_1(B_314))
      | ~ r1_tarski(A_315,B_314)
      | ~ r2_hidden(C_313,k2_relat_1(A_315)) ) ),
    inference(resolution,[status(thm)],[c_2747,c_22])).

tff(c_2780,plain,(
    ! [C_316] :
      ( r2_hidden(C_316,k2_relat_1('#skF_11'))
      | ~ r2_hidden(C_316,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_34,c_2767])).

tff(c_2977,plain,(
    ! [A_323] :
      ( r1_tarski(A_323,k2_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_1'(A_323,k2_relat_1('#skF_11')),k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_2780,c_4])).

tff(c_2989,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_2977])).

tff(c_2995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1530,c_1530,c_2989])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:16:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.97/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/2.03  
% 4.97/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/2.03  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_4
% 4.97/2.03  
% 4.97/2.03  %Foreground sorts:
% 4.97/2.03  
% 4.97/2.03  
% 4.97/2.03  %Background operators:
% 4.97/2.03  
% 4.97/2.03  
% 4.97/2.03  %Foreground operators:
% 4.97/2.03  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.97/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.97/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.97/2.03  tff('#skF_11', type, '#skF_11': $i).
% 4.97/2.03  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.97/2.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.97/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.97/2.03  tff('#skF_10', type, '#skF_10': $i).
% 4.97/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.97/2.03  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.97/2.03  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.97/2.03  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 4.97/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.97/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.97/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.97/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.97/2.03  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.97/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.97/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.97/2.03  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.97/2.03  
% 4.97/2.04  tff(f_60, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 4.97/2.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.97/2.04  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.97/2.04  tff(f_48, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 4.97/2.04  tff(c_32, plain, (~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11')) | ~r1_tarski(k1_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.97/2.04  tff(c_53, plain, (~r1_tarski(k1_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_32])).
% 4.97/2.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.97/2.04  tff(c_34, plain, (r1_tarski('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.97/2.04  tff(c_63, plain, (![C_62, A_63]: (r2_hidden(k4_tarski(C_62, '#skF_5'(A_63, k1_relat_1(A_63), C_62)), A_63) | ~r2_hidden(C_62, k1_relat_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.97/2.04  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.97/2.04  tff(c_1272, plain, (![C_176, A_177, B_178]: (r2_hidden(k4_tarski(C_176, '#skF_5'(A_177, k1_relat_1(A_177), C_176)), B_178) | ~r1_tarski(A_177, B_178) | ~r2_hidden(C_176, k1_relat_1(A_177)))), inference(resolution, [status(thm)], [c_63, c_2])).
% 4.97/2.04  tff(c_10, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k1_relat_1(A_6)) | ~r2_hidden(k4_tarski(C_21, D_24), A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.97/2.04  tff(c_1292, plain, (![C_179, B_180, A_181]: (r2_hidden(C_179, k1_relat_1(B_180)) | ~r1_tarski(A_181, B_180) | ~r2_hidden(C_179, k1_relat_1(A_181)))), inference(resolution, [status(thm)], [c_1272, c_10])).
% 4.97/2.04  tff(c_1305, plain, (![C_182]: (r2_hidden(C_182, k1_relat_1('#skF_11')) | ~r2_hidden(C_182, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_34, c_1292])).
% 4.97/2.04  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.97/2.04  tff(c_1511, plain, (![A_191]: (r1_tarski(A_191, k1_relat_1('#skF_11')) | ~r2_hidden('#skF_1'(A_191, k1_relat_1('#skF_11')), k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1305, c_4])).
% 4.97/2.04  tff(c_1523, plain, (r1_tarski(k1_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_6, c_1511])).
% 4.97/2.04  tff(c_1529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_53, c_1523])).
% 4.97/2.04  tff(c_1530, plain, (~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_32])).
% 4.97/2.04  tff(c_1557, plain, (![A_199, C_200]: (r2_hidden(k4_tarski('#skF_9'(A_199, k2_relat_1(A_199), C_200), C_200), A_199) | ~r2_hidden(C_200, k2_relat_1(A_199)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.97/2.04  tff(c_2747, plain, (![A_310, C_311, B_312]: (r2_hidden(k4_tarski('#skF_9'(A_310, k2_relat_1(A_310), C_311), C_311), B_312) | ~r1_tarski(A_310, B_312) | ~r2_hidden(C_311, k2_relat_1(A_310)))), inference(resolution, [status(thm)], [c_1557, c_2])).
% 4.97/2.04  tff(c_22, plain, (![C_40, A_25, D_43]: (r2_hidden(C_40, k2_relat_1(A_25)) | ~r2_hidden(k4_tarski(D_43, C_40), A_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.97/2.04  tff(c_2767, plain, (![C_313, B_314, A_315]: (r2_hidden(C_313, k2_relat_1(B_314)) | ~r1_tarski(A_315, B_314) | ~r2_hidden(C_313, k2_relat_1(A_315)))), inference(resolution, [status(thm)], [c_2747, c_22])).
% 4.97/2.04  tff(c_2780, plain, (![C_316]: (r2_hidden(C_316, k2_relat_1('#skF_11')) | ~r2_hidden(C_316, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_34, c_2767])).
% 4.97/2.04  tff(c_2977, plain, (![A_323]: (r1_tarski(A_323, k2_relat_1('#skF_11')) | ~r2_hidden('#skF_1'(A_323, k2_relat_1('#skF_11')), k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_2780, c_4])).
% 4.97/2.04  tff(c_2989, plain, (r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_6, c_2977])).
% 4.97/2.04  tff(c_2995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1530, c_1530, c_2989])).
% 4.97/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/2.04  
% 4.97/2.04  Inference rules
% 4.97/2.04  ----------------------
% 4.97/2.04  #Ref     : 0
% 4.97/2.04  #Sup     : 663
% 4.97/2.04  #Fact    : 0
% 4.97/2.04  #Define  : 0
% 4.97/2.04  #Split   : 13
% 4.97/2.04  #Chain   : 0
% 4.97/2.04  #Close   : 0
% 4.97/2.04  
% 4.97/2.04  Ordering : KBO
% 4.97/2.04  
% 4.97/2.04  Simplification rules
% 4.97/2.04  ----------------------
% 4.97/2.04  #Subsume      : 104
% 4.97/2.04  #Demod        : 123
% 4.97/2.04  #Tautology    : 43
% 4.97/2.04  #SimpNegUnit  : 2
% 4.97/2.04  #BackRed      : 42
% 4.97/2.04  
% 4.97/2.04  #Partial instantiations: 0
% 4.97/2.04  #Strategies tried      : 1
% 4.97/2.04  
% 4.97/2.04  Timing (in seconds)
% 4.97/2.04  ----------------------
% 4.97/2.04  Preprocessing        : 0.30
% 4.97/2.05  Parsing              : 0.16
% 4.97/2.05  CNF conversion       : 0.03
% 4.97/2.05  Main loop            : 0.93
% 4.97/2.05  Inferencing          : 0.32
% 4.97/2.05  Reduction            : 0.24
% 4.97/2.05  Demodulation         : 0.15
% 4.97/2.05  BG Simplification    : 0.04
% 4.97/2.05  Subsumption          : 0.25
% 4.97/2.05  Abstraction          : 0.05
% 4.97/2.05  MUC search           : 0.00
% 4.97/2.05  Cooper               : 0.00
% 4.97/2.05  Total                : 1.25
% 4.97/2.05  Index Insertion      : 0.00
% 4.97/2.05  Index Deletion       : 0.00
% 4.97/2.05  Index Matching       : 0.00
% 4.97/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
