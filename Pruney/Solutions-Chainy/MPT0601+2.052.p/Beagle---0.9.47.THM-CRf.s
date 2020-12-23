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

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 100 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,B_31)
      | ~ r1_xboole_0(k1_tarski(A_30),B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    ! [A_30] : ~ r2_hidden(A_30,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_40])).

tff(c_32,plain,
    ( k11_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_47,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_38])).

tff(c_30,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_67,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),B_45)
      | r2_hidden('#skF_2'(A_44,B_45),A_44)
      | B_45 = A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [B_46] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_46),B_46)
      | k1_xboole_0 = B_46 ) ),
    inference(resolution,[status(thm)],[c_67,c_45])).

tff(c_50,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden(k4_tarski(A_36,B_37),C_38)
      | ~ r2_hidden(B_37,k11_relat_1(C_38,A_36))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [C_22,A_7,D_25] :
      ( r2_hidden(C_22,k1_relat_1(A_7))
      | ~ r2_hidden(k4_tarski(C_22,D_25),A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    ! [A_36,C_38,B_37] :
      ( r2_hidden(A_36,k1_relat_1(C_38))
      | ~ r2_hidden(B_37,k11_relat_1(C_38,A_36))
      | ~ v1_relat_1(C_38) ) ),
    inference(resolution,[status(thm)],[c_50,c_16])).

tff(c_106,plain,(
    ! [A_49,C_50] :
      ( r2_hidden(A_49,k1_relat_1(C_50))
      | ~ v1_relat_1(C_50)
      | k11_relat_1(C_50,A_49) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_89,c_58])).

tff(c_120,plain,
    ( ~ v1_relat_1('#skF_8')
    | k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_47])).

tff(c_126,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_120])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_126])).

tff(c_130,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_129,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_239,plain,(
    ! [C_74,A_75] :
      ( r2_hidden(k4_tarski(C_74,'#skF_6'(A_75,k1_relat_1(A_75),C_74)),A_75)
      | ~ r2_hidden(C_74,k1_relat_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [B_27,C_28,A_26] :
      ( r2_hidden(B_27,k11_relat_1(C_28,A_26))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_824,plain,(
    ! [A_109,C_110] :
      ( r2_hidden('#skF_6'(A_109,k1_relat_1(A_109),C_110),k11_relat_1(A_109,C_110))
      | ~ v1_relat_1(A_109)
      | ~ r2_hidden(C_110,k1_relat_1(A_109)) ) ),
    inference(resolution,[status(thm)],[c_239,c_28])).

tff(c_841,plain,
    ( r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0)
    | ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_824])).

tff(c_846,plain,(
    r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_30,c_841])).

tff(c_848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:55:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.64  
% 2.75/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.64  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.75/1.64  
% 2.75/1.64  %Foreground sorts:
% 2.75/1.64  
% 2.75/1.64  
% 2.75/1.64  %Background operators:
% 2.75/1.64  
% 2.75/1.64  
% 2.75/1.64  %Foreground operators:
% 2.75/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.64  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.75/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.75/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.64  tff('#skF_7', type, '#skF_7': $i).
% 2.75/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.75/1.64  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.75/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.64  tff('#skF_8', type, '#skF_8': $i).
% 2.75/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.64  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.75/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.75/1.64  
% 2.75/1.65  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.75/1.65  tff(f_39, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.75/1.65  tff(f_61, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.75/1.65  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.75/1.65  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.75/1.65  tff(f_47, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.75/1.65  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.75/1.65  tff(c_40, plain, (![A_30, B_31]: (~r2_hidden(A_30, B_31) | ~r1_xboole_0(k1_tarski(A_30), B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.65  tff(c_45, plain, (![A_30]: (~r2_hidden(A_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_40])).
% 2.75/1.65  tff(c_32, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.75/1.65  tff(c_47, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.75/1.65  tff(c_38, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8')) | k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.75/1.65  tff(c_48, plain, (k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_47, c_38])).
% 2.75/1.65  tff(c_30, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.75/1.65  tff(c_67, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), B_45) | r2_hidden('#skF_2'(A_44, B_45), A_44) | B_45=A_44)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.65  tff(c_89, plain, (![B_46]: (r2_hidden('#skF_1'(k1_xboole_0, B_46), B_46) | k1_xboole_0=B_46)), inference(resolution, [status(thm)], [c_67, c_45])).
% 2.75/1.65  tff(c_50, plain, (![A_36, B_37, C_38]: (r2_hidden(k4_tarski(A_36, B_37), C_38) | ~r2_hidden(B_37, k11_relat_1(C_38, A_36)) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.75/1.65  tff(c_16, plain, (![C_22, A_7, D_25]: (r2_hidden(C_22, k1_relat_1(A_7)) | ~r2_hidden(k4_tarski(C_22, D_25), A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.75/1.65  tff(c_58, plain, (![A_36, C_38, B_37]: (r2_hidden(A_36, k1_relat_1(C_38)) | ~r2_hidden(B_37, k11_relat_1(C_38, A_36)) | ~v1_relat_1(C_38))), inference(resolution, [status(thm)], [c_50, c_16])).
% 2.75/1.65  tff(c_106, plain, (![A_49, C_50]: (r2_hidden(A_49, k1_relat_1(C_50)) | ~v1_relat_1(C_50) | k11_relat_1(C_50, A_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_89, c_58])).
% 2.75/1.65  tff(c_120, plain, (~v1_relat_1('#skF_8') | k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_106, c_47])).
% 2.75/1.65  tff(c_126, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_120])).
% 2.75/1.65  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_126])).
% 2.75/1.65  tff(c_130, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_32])).
% 2.75/1.65  tff(c_129, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.75/1.65  tff(c_239, plain, (![C_74, A_75]: (r2_hidden(k4_tarski(C_74, '#skF_6'(A_75, k1_relat_1(A_75), C_74)), A_75) | ~r2_hidden(C_74, k1_relat_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.75/1.65  tff(c_28, plain, (![B_27, C_28, A_26]: (r2_hidden(B_27, k11_relat_1(C_28, A_26)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.75/1.65  tff(c_824, plain, (![A_109, C_110]: (r2_hidden('#skF_6'(A_109, k1_relat_1(A_109), C_110), k11_relat_1(A_109, C_110)) | ~v1_relat_1(A_109) | ~r2_hidden(C_110, k1_relat_1(A_109)))), inference(resolution, [status(thm)], [c_239, c_28])).
% 2.75/1.65  tff(c_841, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0) | ~v1_relat_1('#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_824])).
% 2.75/1.65  tff(c_846, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_30, c_841])).
% 2.75/1.65  tff(c_848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_846])).
% 2.75/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.65  
% 2.75/1.65  Inference rules
% 2.75/1.65  ----------------------
% 2.75/1.65  #Ref     : 0
% 2.75/1.65  #Sup     : 165
% 2.75/1.65  #Fact    : 0
% 2.75/1.65  #Define  : 0
% 2.75/1.65  #Split   : 3
% 2.75/1.65  #Chain   : 0
% 2.75/1.65  #Close   : 0
% 2.75/1.65  
% 2.75/1.65  Ordering : KBO
% 2.75/1.65  
% 2.75/1.65  Simplification rules
% 2.75/1.65  ----------------------
% 2.75/1.65  #Subsume      : 42
% 2.75/1.65  #Demod        : 57
% 2.75/1.65  #Tautology    : 30
% 2.75/1.65  #SimpNegUnit  : 20
% 2.75/1.65  #BackRed      : 1
% 2.75/1.65  
% 2.75/1.65  #Partial instantiations: 0
% 2.75/1.65  #Strategies tried      : 1
% 2.75/1.65  
% 2.75/1.65  Timing (in seconds)
% 2.75/1.65  ----------------------
% 2.75/1.65  Preprocessing        : 0.40
% 2.75/1.65  Parsing              : 0.22
% 2.75/1.65  CNF conversion       : 0.03
% 2.75/1.65  Main loop            : 0.35
% 2.75/1.65  Inferencing          : 0.14
% 2.75/1.65  Reduction            : 0.09
% 2.75/1.65  Demodulation         : 0.05
% 2.75/1.65  BG Simplification    : 0.02
% 2.75/1.65  Subsumption          : 0.08
% 2.75/1.65  Abstraction          : 0.02
% 2.75/1.65  MUC search           : 0.00
% 2.75/1.65  Cooper               : 0.00
% 2.75/1.65  Total                : 0.78
% 2.75/1.65  Index Insertion      : 0.00
% 2.75/1.65  Index Deletion       : 0.00
% 2.75/1.66  Index Matching       : 0.00
% 2.75/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
