%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:21 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   49 (  80 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 125 expanded)
%              Number of equality atoms :   18 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_29,B_30] : ~ r2_hidden(A_29,k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_34,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_65,plain,(
    k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_26,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_248,plain,(
    ! [A_60,B_61] :
      ( r2_hidden(k4_tarski('#skF_1'(A_60,B_61),'#skF_2'(A_60,B_61)),A_60)
      | r2_hidden('#skF_3'(A_60,B_61),B_61)
      | k1_relat_1(A_60) = B_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_301,plain,(
    ! [B_62] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_62),B_62)
      | k1_relat_1(k1_xboole_0) = B_62 ) ),
    inference(resolution,[status(thm)],[c_248,c_60])).

tff(c_346,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_301,c_60])).

tff(c_300,plain,(
    ! [B_61] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_61),B_61)
      | k1_relat_1(k1_xboole_0) = B_61 ) ),
    inference(resolution,[status(thm)],[c_248,c_60])).

tff(c_377,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_66),B_66)
      | k1_xboole_0 = B_66 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_300])).

tff(c_80,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(k4_tarski(A_40,B_41),C_42)
      | ~ r2_hidden(B_41,k11_relat_1(C_42,A_40))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ! [C_20,A_5,D_23] :
      ( r2_hidden(C_20,k1_relat_1(A_5))
      | ~ r2_hidden(k4_tarski(C_20,D_23),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_96,plain,(
    ! [A_40,C_42,B_41] :
      ( r2_hidden(A_40,k1_relat_1(C_42))
      | ~ r2_hidden(B_41,k11_relat_1(C_42,A_40))
      | ~ v1_relat_1(C_42) ) ),
    inference(resolution,[status(thm)],[c_80,c_12])).

tff(c_392,plain,(
    ! [A_67,C_68] :
      ( r2_hidden(A_67,k1_relat_1(C_68))
      | ~ v1_relat_1(C_68)
      | k11_relat_1(C_68,A_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_377,c_96])).

tff(c_28,plain,
    ( k11_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_28])).

tff(c_409,plain,
    ( ~ v1_relat_1('#skF_6')
    | k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_392,c_77])).

tff(c_419,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_409])).

tff(c_421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_419])).

tff(c_422,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_423,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_472,plain,(
    ! [C_83,A_84] :
      ( r2_hidden(k4_tarski(C_83,'#skF_4'(A_84,k1_relat_1(A_84),C_83)),A_84)
      | ~ r2_hidden(C_83,k1_relat_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [B_25,C_26,A_24] :
      ( r2_hidden(B_25,k11_relat_1(C_26,A_24))
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1258,plain,(
    ! [A_132,C_133] :
      ( r2_hidden('#skF_4'(A_132,k1_relat_1(A_132),C_133),k11_relat_1(A_132,C_133))
      | ~ v1_relat_1(A_132)
      | ~ r2_hidden(C_133,k1_relat_1(A_132)) ) ),
    inference(resolution,[status(thm)],[c_472,c_24])).

tff(c_1278,plain,
    ( r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_6'),'#skF_5'),k1_xboole_0)
    | ~ v1_relat_1('#skF_6')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_1258])).

tff(c_1283,plain,(
    r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_6'),'#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_26,c_1278])).

tff(c_1285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.46  
% 2.95/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.46  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.95/1.46  
% 2.95/1.46  %Foreground sorts:
% 2.95/1.46  
% 2.95/1.46  
% 2.95/1.46  %Background operators:
% 2.95/1.46  
% 2.95/1.46  
% 2.95/1.46  %Foreground operators:
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.95/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.95/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.95/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.46  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.95/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.95/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.95/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.95/1.46  
% 2.95/1.47  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.95/1.47  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.95/1.47  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.95/1.47  tff(f_42, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.95/1.47  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.95/1.47  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.47  tff(c_57, plain, (![A_29, B_30]: (~r2_hidden(A_29, k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.95/1.47  tff(c_60, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_57])).
% 2.95/1.47  tff(c_34, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6')) | k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.95/1.47  tff(c_65, plain, (k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 2.95/1.47  tff(c_26, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.95/1.47  tff(c_248, plain, (![A_60, B_61]: (r2_hidden(k4_tarski('#skF_1'(A_60, B_61), '#skF_2'(A_60, B_61)), A_60) | r2_hidden('#skF_3'(A_60, B_61), B_61) | k1_relat_1(A_60)=B_61)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.95/1.47  tff(c_301, plain, (![B_62]: (r2_hidden('#skF_3'(k1_xboole_0, B_62), B_62) | k1_relat_1(k1_xboole_0)=B_62)), inference(resolution, [status(thm)], [c_248, c_60])).
% 2.95/1.47  tff(c_346, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_301, c_60])).
% 2.95/1.47  tff(c_300, plain, (![B_61]: (r2_hidden('#skF_3'(k1_xboole_0, B_61), B_61) | k1_relat_1(k1_xboole_0)=B_61)), inference(resolution, [status(thm)], [c_248, c_60])).
% 2.95/1.47  tff(c_377, plain, (![B_66]: (r2_hidden('#skF_3'(k1_xboole_0, B_66), B_66) | k1_xboole_0=B_66)), inference(demodulation, [status(thm), theory('equality')], [c_346, c_300])).
% 2.95/1.47  tff(c_80, plain, (![A_40, B_41, C_42]: (r2_hidden(k4_tarski(A_40, B_41), C_42) | ~r2_hidden(B_41, k11_relat_1(C_42, A_40)) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.95/1.47  tff(c_12, plain, (![C_20, A_5, D_23]: (r2_hidden(C_20, k1_relat_1(A_5)) | ~r2_hidden(k4_tarski(C_20, D_23), A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.95/1.47  tff(c_96, plain, (![A_40, C_42, B_41]: (r2_hidden(A_40, k1_relat_1(C_42)) | ~r2_hidden(B_41, k11_relat_1(C_42, A_40)) | ~v1_relat_1(C_42))), inference(resolution, [status(thm)], [c_80, c_12])).
% 2.95/1.47  tff(c_392, plain, (![A_67, C_68]: (r2_hidden(A_67, k1_relat_1(C_68)) | ~v1_relat_1(C_68) | k11_relat_1(C_68, A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_377, c_96])).
% 2.95/1.47  tff(c_28, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.95/1.47  tff(c_77, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_65, c_28])).
% 2.95/1.47  tff(c_409, plain, (~v1_relat_1('#skF_6') | k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_392, c_77])).
% 2.95/1.47  tff(c_419, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_409])).
% 2.95/1.47  tff(c_421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_419])).
% 2.95/1.47  tff(c_422, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_34])).
% 2.95/1.47  tff(c_423, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.95/1.47  tff(c_472, plain, (![C_83, A_84]: (r2_hidden(k4_tarski(C_83, '#skF_4'(A_84, k1_relat_1(A_84), C_83)), A_84) | ~r2_hidden(C_83, k1_relat_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.95/1.47  tff(c_24, plain, (![B_25, C_26, A_24]: (r2_hidden(B_25, k11_relat_1(C_26, A_24)) | ~r2_hidden(k4_tarski(A_24, B_25), C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.95/1.47  tff(c_1258, plain, (![A_132, C_133]: (r2_hidden('#skF_4'(A_132, k1_relat_1(A_132), C_133), k11_relat_1(A_132, C_133)) | ~v1_relat_1(A_132) | ~r2_hidden(C_133, k1_relat_1(A_132)))), inference(resolution, [status(thm)], [c_472, c_24])).
% 2.95/1.47  tff(c_1278, plain, (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_6'), '#skF_5'), k1_xboole_0) | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_423, c_1258])).
% 2.95/1.47  tff(c_1283, plain, (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_6'), '#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_422, c_26, c_1278])).
% 2.95/1.47  tff(c_1285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1283])).
% 2.95/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.47  
% 2.95/1.47  Inference rules
% 2.95/1.47  ----------------------
% 2.95/1.47  #Ref     : 0
% 2.95/1.47  #Sup     : 254
% 2.95/1.47  #Fact    : 0
% 2.95/1.47  #Define  : 0
% 2.95/1.47  #Split   : 6
% 2.95/1.47  #Chain   : 0
% 2.95/1.47  #Close   : 0
% 2.95/1.47  
% 2.95/1.47  Ordering : KBO
% 2.95/1.47  
% 2.95/1.47  Simplification rules
% 2.95/1.47  ----------------------
% 2.95/1.47  #Subsume      : 77
% 2.95/1.47  #Demod        : 197
% 2.95/1.47  #Tautology    : 55
% 2.95/1.47  #SimpNegUnit  : 31
% 2.95/1.47  #BackRed      : 19
% 2.95/1.47  
% 2.95/1.47  #Partial instantiations: 0
% 2.95/1.47  #Strategies tried      : 1
% 2.95/1.47  
% 2.95/1.47  Timing (in seconds)
% 2.95/1.47  ----------------------
% 2.95/1.47  Preprocessing        : 0.27
% 2.95/1.47  Parsing              : 0.14
% 2.95/1.47  CNF conversion       : 0.02
% 2.95/1.47  Main loop            : 0.42
% 2.95/1.47  Inferencing          : 0.16
% 2.95/1.47  Reduction            : 0.12
% 2.95/1.47  Demodulation         : 0.07
% 2.95/1.47  BG Simplification    : 0.02
% 2.95/1.47  Subsumption          : 0.09
% 2.95/1.47  Abstraction          : 0.02
% 2.95/1.47  MUC search           : 0.00
% 2.95/1.47  Cooper               : 0.00
% 2.95/1.47  Total                : 0.71
% 2.95/1.47  Index Insertion      : 0.00
% 2.95/1.47  Index Deletion       : 0.00
% 2.95/1.47  Index Matching       : 0.00
% 2.95/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
