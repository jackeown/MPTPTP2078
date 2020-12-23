%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:58 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 130 expanded)
%              Number of leaves         :   28 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 210 expanded)
%              Number of equality atoms :   29 (  70 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(c_38,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_69,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    ! [B_35] : k2_zfmisc_1(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [A_29,B_30] : v1_relat_1(k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_44,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_129,plain,(
    ! [A_53,C_54] :
      ( r2_hidden(k4_tarski('#skF_6'(A_53,k2_relat_1(A_53),C_54),C_54),A_53)
      | ~ r2_hidden(C_54,k2_relat_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [A_55,C_56] :
      ( ~ v1_xboole_0(A_55)
      | ~ r2_hidden(C_56,k2_relat_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_172,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(A_58)
      | k2_relat_1(A_58) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_141])).

tff(c_184,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_172])).

tff(c_28,plain,(
    ! [A_28] :
      ( v1_relat_1(k4_relat_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [A_32] :
      ( k1_relat_1(k4_relat_1(A_32)) = k2_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_95,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(k1_relat_1(A_44))
      | ~ v1_relat_1(A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_120,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k2_relat_1(A_51))
      | ~ v1_relat_1(k4_relat_1(A_51))
      | v1_xboole_0(k4_relat_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_95])).

tff(c_70,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_2'(A_40),A_40)
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(A_40)
      | k1_xboole_0 = A_40 ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_124,plain,(
    ! [A_51] :
      ( k4_relat_1(A_51) = k1_xboole_0
      | ~ v1_xboole_0(k2_relat_1(A_51))
      | ~ v1_relat_1(k4_relat_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_120,c_74])).

tff(c_197,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_124])).

tff(c_206,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6,c_197])).

tff(c_268,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_272,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_268])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_272])).

tff(c_277,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_34,plain,(
    ! [A_32] :
      ( k2_relat_1(k4_relat_1(A_32)) = k1_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_285,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_34])).

tff(c_297,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_184,c_285])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_297])).

tff(c_300,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_370,plain,(
    ! [A_79,C_80] :
      ( r2_hidden(k4_tarski('#skF_6'(A_79,k2_relat_1(A_79),C_80),C_80),A_79)
      | ~ r2_hidden(C_80,k2_relat_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_383,plain,(
    ! [A_83,C_84] :
      ( ~ v1_xboole_0(A_83)
      | ~ r2_hidden(C_84,k2_relat_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_370,c_2])).

tff(c_402,plain,(
    ! [A_85] :
      ( ~ v1_xboole_0(A_85)
      | k2_relat_1(A_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_383])).

tff(c_408,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_402])).

tff(c_413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:50:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.45  
% 2.21/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.45  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 2.50/1.45  
% 2.50/1.45  %Foreground sorts:
% 2.50/1.45  
% 2.50/1.45  
% 2.50/1.45  %Background operators:
% 2.50/1.45  
% 2.50/1.45  
% 2.50/1.45  %Foreground operators:
% 2.50/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.50/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.45  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.50/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.50/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.50/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.50/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.50/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.45  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.50/1.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.50/1.45  
% 2.50/1.47  tff(f_78, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.50/1.47  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.50/1.47  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.50/1.47  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.50/1.47  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.50/1.47  tff(f_54, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.50/1.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.50/1.47  tff(f_58, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.50/1.47  tff(f_74, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.50/1.47  tff(f_68, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.50/1.47  tff(c_38, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.50/1.47  tff(c_69, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.50/1.47  tff(c_40, plain, (![B_35]: (k2_zfmisc_1(k1_xboole_0, B_35)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.50/1.47  tff(c_30, plain, (![A_29, B_30]: (v1_relat_1(k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.50/1.47  tff(c_44, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_30])).
% 2.50/1.47  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.50/1.47  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.50/1.47  tff(c_129, plain, (![A_53, C_54]: (r2_hidden(k4_tarski('#skF_6'(A_53, k2_relat_1(A_53), C_54), C_54), A_53) | ~r2_hidden(C_54, k2_relat_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.50/1.47  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.47  tff(c_141, plain, (![A_55, C_56]: (~v1_xboole_0(A_55) | ~r2_hidden(C_56, k2_relat_1(A_55)))), inference(resolution, [status(thm)], [c_129, c_2])).
% 2.50/1.47  tff(c_172, plain, (![A_58]: (~v1_xboole_0(A_58) | k2_relat_1(A_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_141])).
% 2.50/1.47  tff(c_184, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_172])).
% 2.50/1.47  tff(c_28, plain, (![A_28]: (v1_relat_1(k4_relat_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.50/1.47  tff(c_36, plain, (![A_32]: (k1_relat_1(k4_relat_1(A_32))=k2_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.50/1.47  tff(c_95, plain, (![A_44]: (~v1_xboole_0(k1_relat_1(A_44)) | ~v1_relat_1(A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.50/1.47  tff(c_120, plain, (![A_51]: (~v1_xboole_0(k2_relat_1(A_51)) | ~v1_relat_1(k4_relat_1(A_51)) | v1_xboole_0(k4_relat_1(A_51)) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_36, c_95])).
% 2.50/1.47  tff(c_70, plain, (![A_40]: (r2_hidden('#skF_2'(A_40), A_40) | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.50/1.47  tff(c_74, plain, (![A_40]: (~v1_xboole_0(A_40) | k1_xboole_0=A_40)), inference(resolution, [status(thm)], [c_70, c_2])).
% 2.50/1.47  tff(c_124, plain, (![A_51]: (k4_relat_1(A_51)=k1_xboole_0 | ~v1_xboole_0(k2_relat_1(A_51)) | ~v1_relat_1(k4_relat_1(A_51)) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_120, c_74])).
% 2.50/1.47  tff(c_197, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_184, c_124])).
% 2.50/1.47  tff(c_206, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6, c_197])).
% 2.50/1.47  tff(c_268, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_206])).
% 2.50/1.47  tff(c_272, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_268])).
% 2.50/1.47  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_272])).
% 2.50/1.47  tff(c_277, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_206])).
% 2.50/1.47  tff(c_34, plain, (![A_32]: (k2_relat_1(k4_relat_1(A_32))=k1_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.50/1.47  tff(c_285, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_277, c_34])).
% 2.50/1.47  tff(c_297, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_184, c_285])).
% 2.50/1.47  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_297])).
% 2.50/1.47  tff(c_300, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.50/1.47  tff(c_370, plain, (![A_79, C_80]: (r2_hidden(k4_tarski('#skF_6'(A_79, k2_relat_1(A_79), C_80), C_80), A_79) | ~r2_hidden(C_80, k2_relat_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.50/1.47  tff(c_383, plain, (![A_83, C_84]: (~v1_xboole_0(A_83) | ~r2_hidden(C_84, k2_relat_1(A_83)))), inference(resolution, [status(thm)], [c_370, c_2])).
% 2.50/1.47  tff(c_402, plain, (![A_85]: (~v1_xboole_0(A_85) | k2_relat_1(A_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_383])).
% 2.50/1.47  tff(c_408, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_402])).
% 2.50/1.47  tff(c_413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_408])).
% 2.50/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.47  
% 2.50/1.47  Inference rules
% 2.50/1.47  ----------------------
% 2.50/1.47  #Ref     : 0
% 2.50/1.47  #Sup     : 83
% 2.50/1.47  #Fact    : 0
% 2.50/1.47  #Define  : 0
% 2.50/1.47  #Split   : 2
% 2.50/1.47  #Chain   : 0
% 2.50/1.47  #Close   : 0
% 2.50/1.47  
% 2.50/1.47  Ordering : KBO
% 2.50/1.47  
% 2.50/1.47  Simplification rules
% 2.50/1.47  ----------------------
% 2.50/1.47  #Subsume      : 3
% 2.50/1.47  #Demod        : 27
% 2.50/1.47  #Tautology    : 41
% 2.50/1.47  #SimpNegUnit  : 2
% 2.50/1.47  #BackRed      : 0
% 2.50/1.47  
% 2.50/1.47  #Partial instantiations: 0
% 2.50/1.47  #Strategies tried      : 1
% 2.50/1.47  
% 2.50/1.47  Timing (in seconds)
% 2.50/1.47  ----------------------
% 2.50/1.47  Preprocessing        : 0.36
% 2.50/1.47  Parsing              : 0.19
% 2.50/1.47  CNF conversion       : 0.03
% 2.50/1.47  Main loop            : 0.24
% 2.50/1.47  Inferencing          : 0.09
% 2.50/1.47  Reduction            : 0.06
% 2.50/1.47  Demodulation         : 0.04
% 2.50/1.47  BG Simplification    : 0.01
% 2.50/1.47  Subsumption          : 0.05
% 2.50/1.47  Abstraction          : 0.01
% 2.50/1.47  MUC search           : 0.00
% 2.50/1.47  Cooper               : 0.00
% 2.50/1.47  Total                : 0.63
% 2.50/1.47  Index Insertion      : 0.00
% 2.50/1.47  Index Deletion       : 0.00
% 2.50/1.47  Index Matching       : 0.00
% 2.50/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
