%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:21 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   51 (  70 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 105 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden(A_27,B_28)
      | ~ r1_xboole_0(k1_tarski(A_27),B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [A_27] : ~ r2_hidden(A_27,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_28,plain,
    ( k11_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_34])).

tff(c_26,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_198,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(k4_tarski('#skF_1'(A_66,B_67),'#skF_2'(A_66,B_67)),A_66)
      | r2_hidden('#skF_3'(A_66,B_67),B_67)
      | k1_relat_1(A_66) = B_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_231,plain,(
    ! [B_67] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_67),B_67)
      | k1_relat_1(k1_xboole_0) = B_67 ) ),
    inference(resolution,[status(thm)],[c_198,c_49])).

tff(c_251,plain,(
    ! [B_71] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_71),B_71)
      | k1_xboole_0 = B_71 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_231])).

tff(c_54,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(k4_tarski(A_33,B_34),C_35)
      | ~ r2_hidden(B_34,k11_relat_1(C_35,A_33))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [C_19,A_4,D_22] :
      ( r2_hidden(C_19,k1_relat_1(A_4))
      | ~ r2_hidden(k4_tarski(C_19,D_22),A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    ! [A_33,C_35,B_34] :
      ( r2_hidden(A_33,k1_relat_1(C_35))
      | ~ r2_hidden(B_34,k11_relat_1(C_35,A_33))
      | ~ v1_relat_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_287,plain,(
    ! [A_72,C_73] :
      ( r2_hidden(A_72,k1_relat_1(C_73))
      | ~ v1_relat_1(C_73)
      | k11_relat_1(C_73,A_72) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_251,c_62])).

tff(c_324,plain,
    ( ~ v1_relat_1('#skF_6')
    | k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_287,c_50])).

tff(c_339,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_324])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_339])).

tff(c_343,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_342,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_396,plain,(
    ! [C_89,A_90] :
      ( r2_hidden(k4_tarski(C_89,'#skF_4'(A_90,k1_relat_1(A_90),C_89)),A_90)
      | ~ r2_hidden(C_89,k1_relat_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ! [B_24,C_25,A_23] :
      ( r2_hidden(B_24,k11_relat_1(C_25,A_23))
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_939,plain,(
    ! [A_125,C_126] :
      ( r2_hidden('#skF_4'(A_125,k1_relat_1(A_125),C_126),k11_relat_1(A_125,C_126))
      | ~ v1_relat_1(A_125)
      | ~ r2_hidden(C_126,k1_relat_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_396,c_20])).

tff(c_956,plain,
    ( r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_6'),'#skF_5'),k1_xboole_0)
    | ~ v1_relat_1('#skF_6')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_939])).

tff(c_963,plain,(
    r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_6'),'#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_26,c_956])).

tff(c_965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_963])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:33:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.81/1.40  
% 2.81/1.40  %Foreground sorts:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Background operators:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Foreground operators:
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.81/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.81/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.81/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.40  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.81/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.40  
% 2.81/1.41  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.81/1.41  tff(f_32, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.81/1.41  tff(f_57, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.81/1.41  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.81/1.41  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.81/1.41  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.81/1.41  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.41  tff(c_44, plain, (![A_27, B_28]: (~r2_hidden(A_27, B_28) | ~r1_xboole_0(k1_tarski(A_27), B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.41  tff(c_49, plain, (![A_27]: (~r2_hidden(A_27, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_44])).
% 2.81/1.41  tff(c_28, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.41  tff(c_50, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.81/1.41  tff(c_34, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6')) | k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.41  tff(c_52, plain, (k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_34])).
% 2.81/1.41  tff(c_26, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.41  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.81/1.41  tff(c_198, plain, (![A_66, B_67]: (r2_hidden(k4_tarski('#skF_1'(A_66, B_67), '#skF_2'(A_66, B_67)), A_66) | r2_hidden('#skF_3'(A_66, B_67), B_67) | k1_relat_1(A_66)=B_67)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.81/1.41  tff(c_231, plain, (![B_67]: (r2_hidden('#skF_3'(k1_xboole_0, B_67), B_67) | k1_relat_1(k1_xboole_0)=B_67)), inference(resolution, [status(thm)], [c_198, c_49])).
% 2.81/1.41  tff(c_251, plain, (![B_71]: (r2_hidden('#skF_3'(k1_xboole_0, B_71), B_71) | k1_xboole_0=B_71)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_231])).
% 2.81/1.41  tff(c_54, plain, (![A_33, B_34, C_35]: (r2_hidden(k4_tarski(A_33, B_34), C_35) | ~r2_hidden(B_34, k11_relat_1(C_35, A_33)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.41  tff(c_8, plain, (![C_19, A_4, D_22]: (r2_hidden(C_19, k1_relat_1(A_4)) | ~r2_hidden(k4_tarski(C_19, D_22), A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.81/1.41  tff(c_62, plain, (![A_33, C_35, B_34]: (r2_hidden(A_33, k1_relat_1(C_35)) | ~r2_hidden(B_34, k11_relat_1(C_35, A_33)) | ~v1_relat_1(C_35))), inference(resolution, [status(thm)], [c_54, c_8])).
% 2.81/1.41  tff(c_287, plain, (![A_72, C_73]: (r2_hidden(A_72, k1_relat_1(C_73)) | ~v1_relat_1(C_73) | k11_relat_1(C_73, A_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_251, c_62])).
% 2.81/1.41  tff(c_324, plain, (~v1_relat_1('#skF_6') | k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_287, c_50])).
% 2.81/1.41  tff(c_339, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_324])).
% 2.81/1.41  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_339])).
% 2.81/1.41  tff(c_343, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_28])).
% 2.81/1.41  tff(c_342, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.81/1.41  tff(c_396, plain, (![C_89, A_90]: (r2_hidden(k4_tarski(C_89, '#skF_4'(A_90, k1_relat_1(A_90), C_89)), A_90) | ~r2_hidden(C_89, k1_relat_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.81/1.41  tff(c_20, plain, (![B_24, C_25, A_23]: (r2_hidden(B_24, k11_relat_1(C_25, A_23)) | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.41  tff(c_939, plain, (![A_125, C_126]: (r2_hidden('#skF_4'(A_125, k1_relat_1(A_125), C_126), k11_relat_1(A_125, C_126)) | ~v1_relat_1(A_125) | ~r2_hidden(C_126, k1_relat_1(A_125)))), inference(resolution, [status(thm)], [c_396, c_20])).
% 2.81/1.41  tff(c_956, plain, (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_6'), '#skF_5'), k1_xboole_0) | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_939])).
% 2.81/1.41  tff(c_963, plain, (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_6'), '#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_26, c_956])).
% 2.81/1.41  tff(c_965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_963])).
% 2.81/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.41  
% 2.81/1.41  Inference rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Ref     : 0
% 2.81/1.41  #Sup     : 198
% 2.81/1.41  #Fact    : 0
% 2.81/1.41  #Define  : 0
% 2.81/1.41  #Split   : 4
% 2.81/1.41  #Chain   : 0
% 2.81/1.41  #Close   : 0
% 2.81/1.41  
% 2.81/1.41  Ordering : KBO
% 2.81/1.41  
% 2.81/1.41  Simplification rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Subsume      : 41
% 2.81/1.41  #Demod        : 66
% 2.81/1.41  #Tautology    : 36
% 2.81/1.41  #SimpNegUnit  : 31
% 2.81/1.41  #BackRed      : 0
% 2.81/1.41  
% 2.81/1.41  #Partial instantiations: 0
% 2.81/1.41  #Strategies tried      : 1
% 2.81/1.41  
% 2.81/1.41  Timing (in seconds)
% 2.81/1.41  ----------------------
% 2.81/1.41  Preprocessing        : 0.27
% 2.81/1.41  Parsing              : 0.15
% 2.81/1.41  CNF conversion       : 0.02
% 2.81/1.41  Main loop            : 0.37
% 2.81/1.41  Inferencing          : 0.15
% 2.81/1.41  Reduction            : 0.09
% 2.81/1.42  Demodulation         : 0.05
% 2.81/1.42  BG Simplification    : 0.02
% 2.81/1.42  Subsumption          : 0.09
% 2.81/1.42  Abstraction          : 0.02
% 2.81/1.42  MUC search           : 0.00
% 2.81/1.42  Cooper               : 0.00
% 2.81/1.42  Total                : 0.67
% 2.81/1.42  Index Insertion      : 0.00
% 2.81/1.42  Index Deletion       : 0.00
% 2.81/1.42  Index Matching       : 0.00
% 2.81/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
