%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:21 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   51 (  85 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 131 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_29,B_30] :
      ( ~ r2_hidden(A_29,B_30)
      | ~ r1_xboole_0(k1_tarski(A_29),B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    ! [A_29] : ~ r2_hidden(A_29,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_26,plain,
    ( k11_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_51,plain,(
    k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_32])).

tff(c_24,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_200,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(k4_tarski('#skF_1'(A_57,B_58),'#skF_2'(A_57,B_58)),A_57)
      | r2_hidden('#skF_3'(A_57,B_58),B_58)
      | k1_relat_1(A_57) = B_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_248,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_59),B_59)
      | k1_relat_1(k1_xboole_0) = B_59 ) ),
    inference(resolution,[status(thm)],[c_200,c_48])).

tff(c_288,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_248,c_48])).

tff(c_247,plain,(
    ! [B_58] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_58),B_58)
      | k1_relat_1(k1_xboole_0) = B_58 ) ),
    inference(resolution,[status(thm)],[c_200,c_48])).

tff(c_317,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_63),B_63)
      | k1_xboole_0 = B_63 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_247])).

tff(c_53,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden(k4_tarski(A_35,B_36),C_37)
      | ~ r2_hidden(B_36,k11_relat_1(C_37,A_35))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [C_20,A_5,D_23] :
      ( r2_hidden(C_20,k1_relat_1(A_5))
      | ~ r2_hidden(k4_tarski(C_20,D_23),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61,plain,(
    ! [A_35,C_37,B_36] :
      ( r2_hidden(A_35,k1_relat_1(C_37))
      | ~ r2_hidden(B_36,k11_relat_1(C_37,A_35))
      | ~ v1_relat_1(C_37) ) ),
    inference(resolution,[status(thm)],[c_53,c_10])).

tff(c_345,plain,(
    ! [A_66,C_67] :
      ( r2_hidden(A_66,k1_relat_1(C_67))
      | ~ v1_relat_1(C_67)
      | k11_relat_1(C_67,A_66) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_317,c_61])).

tff(c_362,plain,
    ( ~ v1_relat_1('#skF_6')
    | k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_345,c_50])).

tff(c_372,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_362])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_372])).

tff(c_375,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_382,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_32])).

tff(c_401,plain,(
    ! [C_77,A_78] :
      ( r2_hidden(k4_tarski(C_77,'#skF_4'(A_78,k1_relat_1(A_78),C_77)),A_78)
      | ~ r2_hidden(C_77,k1_relat_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [B_25,C_26,A_24] :
      ( r2_hidden(B_25,k11_relat_1(C_26,A_24))
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1067,plain,(
    ! [A_123,C_124] :
      ( r2_hidden('#skF_4'(A_123,k1_relat_1(A_123),C_124),k11_relat_1(A_123,C_124))
      | ~ v1_relat_1(A_123)
      | ~ r2_hidden(C_124,k1_relat_1(A_123)) ) ),
    inference(resolution,[status(thm)],[c_401,c_22])).

tff(c_1084,plain,
    ( r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_6'),'#skF_5'),k1_xboole_0)
    | ~ v1_relat_1('#skF_6')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_1067])).

tff(c_1089,plain,(
    r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_6'),'#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_24,c_1084])).

tff(c_1091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.47  
% 2.94/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.47  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.94/1.47  
% 2.94/1.47  %Foreground sorts:
% 2.94/1.47  
% 2.94/1.47  
% 2.94/1.47  %Background operators:
% 2.94/1.47  
% 2.94/1.47  
% 2.94/1.47  %Foreground operators:
% 2.94/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.94/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.94/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.94/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.94/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.94/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.47  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.94/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.94/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.94/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.94/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.94/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.94/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.94/1.47  
% 2.94/1.48  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.94/1.48  tff(f_34, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.94/1.48  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.94/1.48  tff(f_42, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.94/1.48  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.94/1.48  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.94/1.48  tff(c_43, plain, (![A_29, B_30]: (~r2_hidden(A_29, B_30) | ~r1_xboole_0(k1_tarski(A_29), B_30))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.94/1.48  tff(c_48, plain, (![A_29]: (~r2_hidden(A_29, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_43])).
% 2.94/1.48  tff(c_26, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.94/1.48  tff(c_50, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.94/1.48  tff(c_32, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6')) | k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.94/1.48  tff(c_51, plain, (k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_32])).
% 2.94/1.48  tff(c_24, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.94/1.48  tff(c_200, plain, (![A_57, B_58]: (r2_hidden(k4_tarski('#skF_1'(A_57, B_58), '#skF_2'(A_57, B_58)), A_57) | r2_hidden('#skF_3'(A_57, B_58), B_58) | k1_relat_1(A_57)=B_58)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.94/1.48  tff(c_248, plain, (![B_59]: (r2_hidden('#skF_3'(k1_xboole_0, B_59), B_59) | k1_relat_1(k1_xboole_0)=B_59)), inference(resolution, [status(thm)], [c_200, c_48])).
% 2.94/1.48  tff(c_288, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_248, c_48])).
% 2.94/1.48  tff(c_247, plain, (![B_58]: (r2_hidden('#skF_3'(k1_xboole_0, B_58), B_58) | k1_relat_1(k1_xboole_0)=B_58)), inference(resolution, [status(thm)], [c_200, c_48])).
% 2.94/1.48  tff(c_317, plain, (![B_63]: (r2_hidden('#skF_3'(k1_xboole_0, B_63), B_63) | k1_xboole_0=B_63)), inference(demodulation, [status(thm), theory('equality')], [c_288, c_247])).
% 2.94/1.48  tff(c_53, plain, (![A_35, B_36, C_37]: (r2_hidden(k4_tarski(A_35, B_36), C_37) | ~r2_hidden(B_36, k11_relat_1(C_37, A_35)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.94/1.48  tff(c_10, plain, (![C_20, A_5, D_23]: (r2_hidden(C_20, k1_relat_1(A_5)) | ~r2_hidden(k4_tarski(C_20, D_23), A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.94/1.48  tff(c_61, plain, (![A_35, C_37, B_36]: (r2_hidden(A_35, k1_relat_1(C_37)) | ~r2_hidden(B_36, k11_relat_1(C_37, A_35)) | ~v1_relat_1(C_37))), inference(resolution, [status(thm)], [c_53, c_10])).
% 2.94/1.48  tff(c_345, plain, (![A_66, C_67]: (r2_hidden(A_66, k1_relat_1(C_67)) | ~v1_relat_1(C_67) | k11_relat_1(C_67, A_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_317, c_61])).
% 2.94/1.48  tff(c_362, plain, (~v1_relat_1('#skF_6') | k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_345, c_50])).
% 2.94/1.48  tff(c_372, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_362])).
% 2.94/1.48  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_372])).
% 2.94/1.48  tff(c_375, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 2.94/1.48  tff(c_382, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_375, c_32])).
% 2.94/1.48  tff(c_401, plain, (![C_77, A_78]: (r2_hidden(k4_tarski(C_77, '#skF_4'(A_78, k1_relat_1(A_78), C_77)), A_78) | ~r2_hidden(C_77, k1_relat_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.94/1.48  tff(c_22, plain, (![B_25, C_26, A_24]: (r2_hidden(B_25, k11_relat_1(C_26, A_24)) | ~r2_hidden(k4_tarski(A_24, B_25), C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.94/1.48  tff(c_1067, plain, (![A_123, C_124]: (r2_hidden('#skF_4'(A_123, k1_relat_1(A_123), C_124), k11_relat_1(A_123, C_124)) | ~v1_relat_1(A_123) | ~r2_hidden(C_124, k1_relat_1(A_123)))), inference(resolution, [status(thm)], [c_401, c_22])).
% 2.94/1.48  tff(c_1084, plain, (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_6'), '#skF_5'), k1_xboole_0) | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_375, c_1067])).
% 2.94/1.48  tff(c_1089, plain, (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_6'), '#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_382, c_24, c_1084])).
% 2.94/1.48  tff(c_1091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1089])).
% 2.94/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.48  
% 2.94/1.48  Inference rules
% 2.94/1.48  ----------------------
% 2.94/1.48  #Ref     : 0
% 2.94/1.48  #Sup     : 210
% 2.94/1.48  #Fact    : 0
% 2.94/1.48  #Define  : 0
% 2.94/1.48  #Split   : 5
% 2.94/1.48  #Chain   : 0
% 2.94/1.48  #Close   : 0
% 2.94/1.48  
% 2.94/1.48  Ordering : KBO
% 2.94/1.48  
% 2.94/1.48  Simplification rules
% 2.94/1.48  ----------------------
% 2.94/1.48  #Subsume      : 66
% 2.94/1.48  #Demod        : 168
% 2.94/1.48  #Tautology    : 42
% 2.94/1.48  #SimpNegUnit  : 21
% 2.94/1.48  #BackRed      : 17
% 2.94/1.48  
% 2.94/1.48  #Partial instantiations: 0
% 2.94/1.48  #Strategies tried      : 1
% 2.94/1.48  
% 2.94/1.48  Timing (in seconds)
% 2.94/1.48  ----------------------
% 2.94/1.49  Preprocessing        : 0.27
% 2.94/1.49  Parsing              : 0.13
% 2.94/1.49  CNF conversion       : 0.02
% 2.94/1.49  Main loop            : 0.40
% 2.94/1.49  Inferencing          : 0.15
% 2.94/1.49  Reduction            : 0.11
% 2.94/1.49  Demodulation         : 0.07
% 2.94/1.49  BG Simplification    : 0.02
% 2.94/1.49  Subsumption          : 0.09
% 2.94/1.49  Abstraction          : 0.03
% 2.94/1.49  MUC search           : 0.00
% 2.94/1.49  Cooper               : 0.00
% 2.94/1.49  Total                : 0.69
% 2.94/1.49  Index Insertion      : 0.00
% 2.94/1.49  Index Deletion       : 0.00
% 2.94/1.49  Index Matching       : 0.00
% 2.94/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
