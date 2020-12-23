%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:16 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   54 (  70 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 103 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_64,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden(k4_tarski(A_59,B_60),C_61)
      | ~ r2_hidden(B_60,k11_relat_1(C_61,A_59))
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [C_27,A_12,D_30] :
      ( r2_hidden(C_27,k1_relat_1(A_12))
      | ~ r2_hidden(k4_tarski(C_27,D_30),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128,plain,(
    ! [A_62,C_63,B_64] :
      ( r2_hidden(A_62,k1_relat_1(C_63))
      | ~ r2_hidden(B_64,k11_relat_1(C_63,A_62))
      | ~ v1_relat_1(C_63) ) ),
    inference(resolution,[status(thm)],[c_113,c_20])).

tff(c_137,plain,(
    ! [A_65,C_66] :
      ( r2_hidden(A_65,k1_relat_1(C_66))
      | ~ v1_relat_1(C_66)
      | k11_relat_1(C_66,A_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_128])).

tff(c_40,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_65,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_40])).

tff(c_144,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_65])).

tff(c_148,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_144])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_148])).

tff(c_151,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_154,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_40])).

tff(c_16,plain,(
    ! [A_9,B_11] :
      ( k9_relat_1(A_9,k1_tarski(B_11)) = k11_relat_1(A_9,B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_176,plain,(
    ! [B_75,A_76] :
      ( r1_xboole_0(k1_relat_1(B_75),A_76)
      | k9_relat_1(B_75,A_76) != k1_xboole_0
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_277,plain,(
    ! [B_97,A_98] :
      ( k4_xboole_0(k1_relat_1(B_97),A_98) = k1_relat_1(B_97)
      | k9_relat_1(B_97,A_98) != k1_xboole_0
      | ~ v1_relat_1(B_97) ) ),
    inference(resolution,[status(thm)],[c_176,c_4])).

tff(c_12,plain,(
    ! [C_8,B_7] : ~ r2_hidden(C_8,k4_xboole_0(B_7,k1_tarski(C_8))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_302,plain,(
    ! [C_99,B_100] :
      ( ~ r2_hidden(C_99,k1_relat_1(B_100))
      | k9_relat_1(B_100,k1_tarski(C_99)) != k1_xboole_0
      | ~ v1_relat_1(B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_12])).

tff(c_316,plain,
    ( k9_relat_1('#skF_7',k1_tarski('#skF_6')) != k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_151,c_302])).

tff(c_326,plain,(
    k9_relat_1('#skF_7',k1_tarski('#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_316])).

tff(c_353,plain,
    ( k11_relat_1('#skF_7','#skF_6') != k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_326])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_154,c_353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:05:01 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  
% 2.11/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 2.11/1.24  
% 2.11/1.24  %Foreground sorts:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Background operators:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Foreground operators:
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.11/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.24  tff('#skF_7', type, '#skF_7': $i).
% 2.11/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.11/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.24  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.11/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.11/1.24  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.11/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.11/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.11/1.24  
% 2.11/1.25  tff(f_79, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.11/1.25  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.11/1.25  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.11/1.25  tff(f_59, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.11/1.25  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.11/1.25  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.11/1.25  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.11/1.25  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.11/1.25  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.25  tff(c_46, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.25  tff(c_64, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 2.11/1.25  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.25  tff(c_113, plain, (![A_59, B_60, C_61]: (r2_hidden(k4_tarski(A_59, B_60), C_61) | ~r2_hidden(B_60, k11_relat_1(C_61, A_59)) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.11/1.25  tff(c_20, plain, (![C_27, A_12, D_30]: (r2_hidden(C_27, k1_relat_1(A_12)) | ~r2_hidden(k4_tarski(C_27, D_30), A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.11/1.25  tff(c_128, plain, (![A_62, C_63, B_64]: (r2_hidden(A_62, k1_relat_1(C_63)) | ~r2_hidden(B_64, k11_relat_1(C_63, A_62)) | ~v1_relat_1(C_63))), inference(resolution, [status(thm)], [c_113, c_20])).
% 2.11/1.25  tff(c_137, plain, (![A_65, C_66]: (r2_hidden(A_65, k1_relat_1(C_66)) | ~v1_relat_1(C_66) | k11_relat_1(C_66, A_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_128])).
% 2.11/1.25  tff(c_40, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.25  tff(c_65, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_40])).
% 2.11/1.25  tff(c_144, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_137, c_65])).
% 2.11/1.25  tff(c_148, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_144])).
% 2.11/1.25  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_148])).
% 2.11/1.25  tff(c_151, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 2.11/1.25  tff(c_154, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_151, c_40])).
% 2.11/1.25  tff(c_16, plain, (![A_9, B_11]: (k9_relat_1(A_9, k1_tarski(B_11))=k11_relat_1(A_9, B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.11/1.25  tff(c_176, plain, (![B_75, A_76]: (r1_xboole_0(k1_relat_1(B_75), A_76) | k9_relat_1(B_75, A_76)!=k1_xboole_0 | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.11/1.25  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.25  tff(c_277, plain, (![B_97, A_98]: (k4_xboole_0(k1_relat_1(B_97), A_98)=k1_relat_1(B_97) | k9_relat_1(B_97, A_98)!=k1_xboole_0 | ~v1_relat_1(B_97))), inference(resolution, [status(thm)], [c_176, c_4])).
% 2.11/1.25  tff(c_12, plain, (![C_8, B_7]: (~r2_hidden(C_8, k4_xboole_0(B_7, k1_tarski(C_8))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.25  tff(c_302, plain, (![C_99, B_100]: (~r2_hidden(C_99, k1_relat_1(B_100)) | k9_relat_1(B_100, k1_tarski(C_99))!=k1_xboole_0 | ~v1_relat_1(B_100))), inference(superposition, [status(thm), theory('equality')], [c_277, c_12])).
% 2.11/1.25  tff(c_316, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_6'))!=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_151, c_302])).
% 2.11/1.25  tff(c_326, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_316])).
% 2.11/1.25  tff(c_353, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16, c_326])).
% 2.11/1.25  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_154, c_353])).
% 2.11/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  Inference rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Ref     : 0
% 2.11/1.25  #Sup     : 61
% 2.11/1.25  #Fact    : 0
% 2.11/1.25  #Define  : 0
% 2.11/1.25  #Split   : 1
% 2.11/1.25  #Chain   : 0
% 2.11/1.25  #Close   : 0
% 2.11/1.25  
% 2.11/1.25  Ordering : KBO
% 2.11/1.25  
% 2.11/1.25  Simplification rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Subsume      : 0
% 2.11/1.25  #Demod        : 8
% 2.11/1.25  #Tautology    : 25
% 2.11/1.25  #SimpNegUnit  : 2
% 2.11/1.25  #BackRed      : 0
% 2.11/1.25  
% 2.11/1.25  #Partial instantiations: 0
% 2.11/1.25  #Strategies tried      : 1
% 2.11/1.25  
% 2.11/1.25  Timing (in seconds)
% 2.11/1.25  ----------------------
% 2.11/1.26  Preprocessing        : 0.30
% 2.11/1.26  Parsing              : 0.16
% 2.11/1.26  CNF conversion       : 0.02
% 2.11/1.26  Main loop            : 0.20
% 2.11/1.26  Inferencing          : 0.08
% 2.11/1.26  Reduction            : 0.05
% 2.11/1.26  Demodulation         : 0.03
% 2.11/1.26  BG Simplification    : 0.02
% 2.11/1.26  Subsumption          : 0.03
% 2.11/1.26  Abstraction          : 0.01
% 2.11/1.26  MUC search           : 0.00
% 2.11/1.26  Cooper               : 0.00
% 2.11/1.26  Total                : 0.53
% 2.11/1.26  Index Insertion      : 0.00
% 2.11/1.26  Index Deletion       : 0.00
% 2.11/1.26  Index Matching       : 0.00
% 2.11/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
