%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:52 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 118 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 174 expanded)
%              Number of equality atoms :   24 (  60 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_42,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_71,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_355,plain,(
    ! [A_89,B_90] :
      ( r2_hidden(k4_tarski('#skF_2'(A_89,B_90),'#skF_3'(A_89,B_90)),A_89)
      | r2_hidden('#skF_4'(A_89,B_90),B_90)
      | k1_relat_1(A_89) = B_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    ! [C_43,B_44] : ~ r2_hidden(C_43,k4_xboole_0(B_44,k1_tarski(C_43))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    ! [C_43] : ~ r2_hidden(C_43,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_483,plain,(
    ! [B_102] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_102),B_102)
      | k1_relat_1(k1_xboole_0) = B_102 ) ),
    inference(resolution,[status(thm)],[c_355,c_69])).

tff(c_519,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_483,c_69])).

tff(c_535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_519])).

tff(c_536,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_37] :
      ( v1_relat_1(A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_47,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_537,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_849,plain,(
    ! [A_148,B_149] :
      ( r2_hidden(k4_tarski('#skF_2'(A_148,B_149),'#skF_3'(A_148,B_149)),A_148)
      | r2_hidden('#skF_4'(A_148,B_149),B_149)
      | k1_relat_1(A_148) = B_149 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_872,plain,(
    ! [B_149] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_149),B_149)
      | k1_relat_1(k1_xboole_0) = B_149 ) ),
    inference(resolution,[status(thm)],[c_849,c_69])).

tff(c_882,plain,(
    ! [B_149] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_149),B_149)
      | k1_xboole_0 = B_149 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_872])).

tff(c_34,plain,(
    ! [A_32] :
      ( v1_relat_1(k4_relat_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_36] :
      ( k2_relat_1(k4_relat_1(A_36)) = k1_relat_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_623,plain,(
    ! [A_120,B_121] :
      ( r2_hidden('#skF_6'(A_120,B_121),k2_relat_1(B_121))
      | ~ r2_hidden(A_120,k1_relat_1(B_121))
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2668,plain,(
    ! [A_212,A_213] :
      ( r2_hidden('#skF_6'(A_212,k4_relat_1(A_213)),k1_relat_1(A_213))
      | ~ r2_hidden(A_212,k1_relat_1(k4_relat_1(A_213)))
      | ~ v1_relat_1(k4_relat_1(A_213))
      | ~ v1_relat_1(A_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_623])).

tff(c_2713,plain,(
    ! [A_212] :
      ( r2_hidden('#skF_6'(A_212,k4_relat_1(k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(A_212,k1_relat_1(k4_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_2668])).

tff(c_2727,plain,(
    ! [A_212] :
      ( r2_hidden('#skF_6'(A_212,k4_relat_1(k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(A_212,k1_relat_1(k4_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_2713])).

tff(c_2728,plain,(
    ! [A_212] :
      ( ~ r2_hidden(A_212,k1_relat_1(k4_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_2727])).

tff(c_2729,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_2728])).

tff(c_2732,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_2729])).

tff(c_2736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_2732])).

tff(c_2739,plain,(
    ! [A_214] : ~ r2_hidden(A_214,k1_relat_1(k4_relat_1(k1_xboole_0))) ),
    inference(splitRight,[status(thm)],[c_2728])).

tff(c_2785,plain,(
    k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_882,c_2739])).

tff(c_40,plain,(
    ! [A_36] :
      ( k1_relat_1(k4_relat_1(A_36)) = k2_relat_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2877,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2785,c_40])).

tff(c_2915,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_2877])).

tff(c_2917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_536,c_2915])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:40:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.67  
% 3.86/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.67  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.86/1.67  
% 3.86/1.67  %Foreground sorts:
% 3.86/1.67  
% 3.86/1.67  
% 3.86/1.67  %Background operators:
% 3.86/1.67  
% 3.86/1.67  
% 3.86/1.67  %Foreground operators:
% 3.86/1.67  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.86/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.86/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.86/1.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.86/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.86/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.86/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.86/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.86/1.67  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.86/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.86/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.86/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.86/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.86/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.86/1.67  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.86/1.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.86/1.67  
% 3.86/1.68  tff(f_80, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.86/1.68  tff(f_57, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.86/1.68  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.86/1.68  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.86/1.68  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.86/1.68  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.86/1.68  tff(f_61, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.86/1.68  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 3.86/1.68  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 3.86/1.68  tff(c_42, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.86/1.68  tff(c_71, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 3.86/1.68  tff(c_355, plain, (![A_89, B_90]: (r2_hidden(k4_tarski('#skF_2'(A_89, B_90), '#skF_3'(A_89, B_90)), A_89) | r2_hidden('#skF_4'(A_89, B_90), B_90) | k1_relat_1(A_89)=B_90)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.86/1.68  tff(c_8, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.86/1.68  tff(c_66, plain, (![C_43, B_44]: (~r2_hidden(C_43, k4_xboole_0(B_44, k1_tarski(C_43))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.86/1.68  tff(c_69, plain, (![C_43]: (~r2_hidden(C_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_66])).
% 3.86/1.68  tff(c_483, plain, (![B_102]: (r2_hidden('#skF_4'(k1_xboole_0, B_102), B_102) | k1_relat_1(k1_xboole_0)=B_102)), inference(resolution, [status(thm)], [c_355, c_69])).
% 3.86/1.68  tff(c_519, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_483, c_69])).
% 3.86/1.68  tff(c_535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_519])).
% 3.86/1.68  tff(c_536, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.86/1.68  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.68  tff(c_43, plain, (![A_37]: (v1_relat_1(A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.86/1.68  tff(c_47, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_43])).
% 3.86/1.68  tff(c_537, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.86/1.68  tff(c_849, plain, (![A_148, B_149]: (r2_hidden(k4_tarski('#skF_2'(A_148, B_149), '#skF_3'(A_148, B_149)), A_148) | r2_hidden('#skF_4'(A_148, B_149), B_149) | k1_relat_1(A_148)=B_149)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.86/1.68  tff(c_872, plain, (![B_149]: (r2_hidden('#skF_4'(k1_xboole_0, B_149), B_149) | k1_relat_1(k1_xboole_0)=B_149)), inference(resolution, [status(thm)], [c_849, c_69])).
% 3.86/1.68  tff(c_882, plain, (![B_149]: (r2_hidden('#skF_4'(k1_xboole_0, B_149), B_149) | k1_xboole_0=B_149)), inference(demodulation, [status(thm), theory('equality')], [c_537, c_872])).
% 3.86/1.68  tff(c_34, plain, (![A_32]: (v1_relat_1(k4_relat_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.86/1.68  tff(c_38, plain, (![A_36]: (k2_relat_1(k4_relat_1(A_36))=k1_relat_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.86/1.68  tff(c_623, plain, (![A_120, B_121]: (r2_hidden('#skF_6'(A_120, B_121), k2_relat_1(B_121)) | ~r2_hidden(A_120, k1_relat_1(B_121)) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.86/1.68  tff(c_2668, plain, (![A_212, A_213]: (r2_hidden('#skF_6'(A_212, k4_relat_1(A_213)), k1_relat_1(A_213)) | ~r2_hidden(A_212, k1_relat_1(k4_relat_1(A_213))) | ~v1_relat_1(k4_relat_1(A_213)) | ~v1_relat_1(A_213))), inference(superposition, [status(thm), theory('equality')], [c_38, c_623])).
% 3.86/1.68  tff(c_2713, plain, (![A_212]: (r2_hidden('#skF_6'(A_212, k4_relat_1(k1_xboole_0)), k1_xboole_0) | ~r2_hidden(A_212, k1_relat_1(k4_relat_1(k1_xboole_0))) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_537, c_2668])).
% 3.86/1.68  tff(c_2727, plain, (![A_212]: (r2_hidden('#skF_6'(A_212, k4_relat_1(k1_xboole_0)), k1_xboole_0) | ~r2_hidden(A_212, k1_relat_1(k4_relat_1(k1_xboole_0))) | ~v1_relat_1(k4_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_2713])).
% 3.86/1.68  tff(c_2728, plain, (![A_212]: (~r2_hidden(A_212, k1_relat_1(k4_relat_1(k1_xboole_0))) | ~v1_relat_1(k4_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_69, c_2727])).
% 3.86/1.68  tff(c_2729, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2728])).
% 3.86/1.68  tff(c_2732, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_2729])).
% 3.86/1.68  tff(c_2736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_2732])).
% 3.86/1.68  tff(c_2739, plain, (![A_214]: (~r2_hidden(A_214, k1_relat_1(k4_relat_1(k1_xboole_0))))), inference(splitRight, [status(thm)], [c_2728])).
% 3.86/1.68  tff(c_2785, plain, (k1_relat_1(k4_relat_1(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_882, c_2739])).
% 3.86/1.68  tff(c_40, plain, (![A_36]: (k1_relat_1(k4_relat_1(A_36))=k2_relat_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.86/1.68  tff(c_2877, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2785, c_40])).
% 3.86/1.68  tff(c_2915, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_47, c_2877])).
% 3.86/1.68  tff(c_2917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_536, c_2915])).
% 3.86/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.68  
% 3.86/1.68  Inference rules
% 3.86/1.68  ----------------------
% 3.86/1.68  #Ref     : 0
% 3.86/1.68  #Sup     : 668
% 3.86/1.68  #Fact    : 0
% 3.86/1.68  #Define  : 0
% 3.86/1.68  #Split   : 2
% 3.86/1.68  #Chain   : 0
% 3.86/1.68  #Close   : 0
% 3.86/1.68  
% 3.86/1.68  Ordering : KBO
% 3.86/1.68  
% 3.86/1.68  Simplification rules
% 3.86/1.68  ----------------------
% 3.86/1.68  #Subsume      : 113
% 3.86/1.68  #Demod        : 534
% 3.86/1.68  #Tautology    : 286
% 3.86/1.68  #SimpNegUnit  : 26
% 3.86/1.68  #BackRed      : 1
% 3.86/1.68  
% 3.86/1.68  #Partial instantiations: 0
% 3.86/1.68  #Strategies tried      : 1
% 3.86/1.68  
% 3.86/1.68  Timing (in seconds)
% 3.86/1.68  ----------------------
% 3.86/1.69  Preprocessing        : 0.31
% 3.86/1.69  Parsing              : 0.16
% 3.86/1.69  CNF conversion       : 0.02
% 3.86/1.69  Main loop            : 0.60
% 3.86/1.69  Inferencing          : 0.21
% 3.86/1.69  Reduction            : 0.17
% 3.86/1.69  Demodulation         : 0.11
% 3.86/1.69  BG Simplification    : 0.03
% 3.86/1.69  Subsumption          : 0.14
% 3.86/1.69  Abstraction          : 0.03
% 3.86/1.69  MUC search           : 0.00
% 4.20/1.69  Cooper               : 0.00
% 4.20/1.69  Total                : 0.94
% 4.20/1.69  Index Insertion      : 0.00
% 4.20/1.69  Index Deletion       : 0.00
% 4.20/1.69  Index Matching       : 0.00
% 4.20/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
