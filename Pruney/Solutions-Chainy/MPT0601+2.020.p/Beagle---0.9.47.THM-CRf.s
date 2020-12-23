%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:16 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   56 (  69 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 101 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_40])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden(k4_tarski(A_61,B_62),C_63)
      | ~ r2_hidden(B_62,k11_relat_1(C_63,A_61))
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [C_27,A_12,D_30] :
      ( r2_hidden(C_27,k1_relat_1(A_12))
      | ~ r2_hidden(k4_tarski(C_27,D_30),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_118,plain,(
    ! [A_64,C_65,B_66] :
      ( r2_hidden(A_64,k1_relat_1(C_65))
      | ~ r2_hidden(B_66,k11_relat_1(C_65,A_64))
      | ~ v1_relat_1(C_65) ) ),
    inference(resolution,[status(thm)],[c_104,c_14])).

tff(c_127,plain,(
    ! [A_67,C_68] :
      ( r2_hidden(A_67,k1_relat_1(C_68))
      | ~ v1_relat_1(C_68)
      | k11_relat_1(C_68,A_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_118])).

tff(c_141,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_127,c_52])).

tff(c_147,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_141])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_147])).

tff(c_150,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_10,plain,(
    ! [A_9,B_11] :
      ( k9_relat_1(A_9,k1_tarski(B_11)) = k11_relat_1(A_9,B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_151,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_183,plain,(
    ! [B_81,A_82] :
      ( r1_xboole_0(k1_relat_1(B_81),A_82)
      | k9_relat_1(B_81,A_82) != k1_xboole_0
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_191,plain,(
    ! [A_83,B_84] :
      ( r1_xboole_0(A_83,k1_relat_1(B_84))
      | k9_relat_1(B_84,A_83) != k1_xboole_0
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_183,c_2])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_167,plain,(
    ! [A_69,C_70,B_71] :
      ( ~ r2_hidden(A_69,C_70)
      | ~ r1_xboole_0(k2_tarski(A_69,B_71),C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_170,plain,(
    ! [A_5,C_70] :
      ( ~ r2_hidden(A_5,C_70)
      | ~ r1_xboole_0(k1_tarski(A_5),C_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_167])).

tff(c_210,plain,(
    ! [A_85,B_86] :
      ( ~ r2_hidden(A_85,k1_relat_1(B_86))
      | k9_relat_1(B_86,k1_tarski(A_85)) != k1_xboole_0
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_191,c_170])).

tff(c_213,plain,
    ( k9_relat_1('#skF_7',k1_tarski('#skF_6')) != k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_151,c_210])).

tff(c_220,plain,(
    k9_relat_1('#skF_7',k1_tarski('#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_213])).

tff(c_234,plain,
    ( k11_relat_1('#skF_7','#skF_6') != k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_220])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_150,c_234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:40:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 1.91/1.20  
% 1.91/1.20  %Foreground sorts:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Background operators:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Foreground operators:
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.91/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.91/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.20  tff('#skF_7', type, '#skF_7': $i).
% 1.91/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.91/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.20  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.91/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.91/1.20  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.91/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.91/1.20  
% 1.99/1.21  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 1.99/1.21  tff(f_37, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.99/1.21  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 1.99/1.21  tff(f_57, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.99/1.21  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 1.99/1.21  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 1.99/1.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.99/1.21  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.99/1.21  tff(f_44, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.99/1.21  tff(c_32, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.99/1.21  tff(c_34, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.99/1.21  tff(c_52, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_34])).
% 1.99/1.21  tff(c_40, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.99/1.21  tff(c_58, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_40])).
% 1.99/1.21  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.21  tff(c_104, plain, (![A_61, B_62, C_63]: (r2_hidden(k4_tarski(A_61, B_62), C_63) | ~r2_hidden(B_62, k11_relat_1(C_63, A_61)) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.99/1.21  tff(c_14, plain, (![C_27, A_12, D_30]: (r2_hidden(C_27, k1_relat_1(A_12)) | ~r2_hidden(k4_tarski(C_27, D_30), A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.21  tff(c_118, plain, (![A_64, C_65, B_66]: (r2_hidden(A_64, k1_relat_1(C_65)) | ~r2_hidden(B_66, k11_relat_1(C_65, A_64)) | ~v1_relat_1(C_65))), inference(resolution, [status(thm)], [c_104, c_14])).
% 1.99/1.21  tff(c_127, plain, (![A_67, C_68]: (r2_hidden(A_67, k1_relat_1(C_68)) | ~v1_relat_1(C_68) | k11_relat_1(C_68, A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_118])).
% 1.99/1.21  tff(c_141, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_127, c_52])).
% 1.99/1.21  tff(c_147, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_141])).
% 1.99/1.21  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_147])).
% 1.99/1.21  tff(c_150, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 1.99/1.21  tff(c_10, plain, (![A_9, B_11]: (k9_relat_1(A_9, k1_tarski(B_11))=k11_relat_1(A_9, B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.21  tff(c_151, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_34])).
% 1.99/1.21  tff(c_183, plain, (![B_81, A_82]: (r1_xboole_0(k1_relat_1(B_81), A_82) | k9_relat_1(B_81, A_82)!=k1_xboole_0 | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.99/1.21  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.21  tff(c_191, plain, (![A_83, B_84]: (r1_xboole_0(A_83, k1_relat_1(B_84)) | k9_relat_1(B_84, A_83)!=k1_xboole_0 | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_183, c_2])).
% 1.99/1.21  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.21  tff(c_167, plain, (![A_69, C_70, B_71]: (~r2_hidden(A_69, C_70) | ~r1_xboole_0(k2_tarski(A_69, B_71), C_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.99/1.21  tff(c_170, plain, (![A_5, C_70]: (~r2_hidden(A_5, C_70) | ~r1_xboole_0(k1_tarski(A_5), C_70))), inference(superposition, [status(thm), theory('equality')], [c_6, c_167])).
% 1.99/1.21  tff(c_210, plain, (![A_85, B_86]: (~r2_hidden(A_85, k1_relat_1(B_86)) | k9_relat_1(B_86, k1_tarski(A_85))!=k1_xboole_0 | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_191, c_170])).
% 1.99/1.21  tff(c_213, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_6'))!=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_151, c_210])).
% 1.99/1.21  tff(c_220, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_213])).
% 1.99/1.21  tff(c_234, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10, c_220])).
% 1.99/1.21  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_150, c_234])).
% 1.99/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.21  
% 1.99/1.21  Inference rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Ref     : 0
% 1.99/1.21  #Sup     : 39
% 1.99/1.21  #Fact    : 0
% 1.99/1.21  #Define  : 0
% 1.99/1.21  #Split   : 2
% 1.99/1.21  #Chain   : 0
% 1.99/1.21  #Close   : 0
% 1.99/1.21  
% 1.99/1.21  Ordering : KBO
% 1.99/1.21  
% 1.99/1.21  Simplification rules
% 1.99/1.21  ----------------------
% 1.99/1.21  #Subsume      : 2
% 1.99/1.21  #Demod        : 7
% 1.99/1.21  #Tautology    : 17
% 1.99/1.21  #SimpNegUnit  : 2
% 1.99/1.21  #BackRed      : 0
% 1.99/1.21  
% 1.99/1.21  #Partial instantiations: 0
% 1.99/1.21  #Strategies tried      : 1
% 1.99/1.21  
% 1.99/1.21  Timing (in seconds)
% 1.99/1.21  ----------------------
% 1.99/1.22  Preprocessing        : 0.30
% 1.99/1.22  Parsing              : 0.16
% 1.99/1.22  CNF conversion       : 0.02
% 1.99/1.22  Main loop            : 0.16
% 1.99/1.22  Inferencing          : 0.06
% 1.99/1.22  Reduction            : 0.04
% 1.99/1.22  Demodulation         : 0.03
% 1.99/1.22  BG Simplification    : 0.01
% 1.99/1.22  Subsumption          : 0.03
% 1.99/1.22  Abstraction          : 0.01
% 1.99/1.22  MUC search           : 0.00
% 1.99/1.22  Cooper               : 0.00
% 1.99/1.22  Total                : 0.49
% 1.99/1.22  Index Insertion      : 0.00
% 1.99/1.22  Index Deletion       : 0.00
% 1.99/1.22  Index Matching       : 0.00
% 1.99/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
