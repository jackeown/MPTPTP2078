%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:55 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 105 expanded)
%              Number of equality atoms :   40 (  63 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(c_49,plain,(
    ! [B_39] : k2_zfmisc_1(k1_xboole_0,B_39) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_30,B_31] : v1_relat_1(k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_30])).

tff(c_38,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_85,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_372,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(k4_tarski('#skF_1'(A_76,B_77),'#skF_2'(A_76,B_77)),A_76)
      | r2_hidden('#skF_3'(A_76,B_77),B_77)
      | k1_relat_1(A_76) = B_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    ! [A_41,B_42] : ~ r2_hidden(A_41,k2_zfmisc_1(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_79,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_76])).

tff(c_422,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_78),B_78)
      | k1_relat_1(k1_xboole_0) = B_78 ) ),
    inference(resolution,[status(thm)],[c_372,c_79])).

tff(c_458,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_422,c_79])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_458])).

tff(c_473,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,(
    ! [A_35] :
      ( k2_relat_1(k4_relat_1(A_35)) = k1_relat_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_29] :
      ( v1_relat_1(k4_relat_1(A_29))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_472,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_478,plain,(
    ! [B_79,A_80] : k2_xboole_0(B_79,A_80) = k2_xboole_0(A_80,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_494,plain,(
    ! [A_80] : k2_xboole_0(k1_xboole_0,A_80) = A_80 ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_6])).

tff(c_629,plain,(
    ! [A_95,B_96] :
      ( k2_xboole_0(k2_relat_1(A_95),k2_relat_1(B_96)) = k2_relat_1(k2_xboole_0(A_95,B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | k2_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_662,plain,(
    ! [A_97,B_98] :
      ( k2_relat_1(A_97) = k1_xboole_0
      | k2_relat_1(k2_xboole_0(A_97,B_98)) != k1_xboole_0
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_4])).

tff(c_668,plain,(
    ! [A_80] :
      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
      | k2_relat_1(A_80) != k1_xboole_0
      | ~ v1_relat_1(A_80)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_662])).

tff(c_679,plain,(
    ! [A_80] :
      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
      | k2_relat_1(A_80) != k1_xboole_0
      | ~ v1_relat_1(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_668])).

tff(c_683,plain,(
    ! [A_99] :
      ( k2_relat_1(A_99) != k1_xboole_0
      | ~ v1_relat_1(A_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_679])).

tff(c_720,plain,(
    ! [A_104] :
      ( k2_relat_1(k4_relat_1(A_104)) != k1_xboole_0
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_28,c_683])).

tff(c_724,plain,(
    ! [A_105] :
      ( k1_relat_1(A_105) != k1_xboole_0
      | ~ v1_relat_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_720])).

tff(c_728,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_53,c_724])).

tff(c_735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_473,c_728])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.37  
% 2.40/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.37  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.40/1.37  
% 2.40/1.37  %Foreground sorts:
% 2.40/1.37  
% 2.40/1.37  
% 2.40/1.37  %Background operators:
% 2.40/1.37  
% 2.40/1.37  
% 2.40/1.37  %Foreground operators:
% 2.40/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.40/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.40/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.40/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.40/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.40/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.40/1.37  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.40/1.37  
% 2.40/1.38  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.40/1.38  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.40/1.38  tff(f_73, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.40/1.38  tff(f_50, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.40/1.38  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.40/1.38  tff(f_69, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.40/1.38  tff(f_54, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.40/1.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.40/1.38  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.40/1.38  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 2.40/1.38  tff(f_31, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.40/1.38  tff(c_49, plain, (![B_39]: (k2_zfmisc_1(k1_xboole_0, B_39)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.38  tff(c_30, plain, (![A_30, B_31]: (v1_relat_1(k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.40/1.38  tff(c_53, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_49, c_30])).
% 2.40/1.38  tff(c_38, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.38  tff(c_85, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.40/1.38  tff(c_372, plain, (![A_76, B_77]: (r2_hidden(k4_tarski('#skF_1'(A_76, B_77), '#skF_2'(A_76, B_77)), A_76) | r2_hidden('#skF_3'(A_76, B_77), B_77) | k1_relat_1(A_76)=B_77)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.40/1.38  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.38  tff(c_76, plain, (![A_41, B_42]: (~r2_hidden(A_41, k2_zfmisc_1(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.40/1.38  tff(c_79, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_76])).
% 2.40/1.38  tff(c_422, plain, (![B_78]: (r2_hidden('#skF_3'(k1_xboole_0, B_78), B_78) | k1_relat_1(k1_xboole_0)=B_78)), inference(resolution, [status(thm)], [c_372, c_79])).
% 2.40/1.38  tff(c_458, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_422, c_79])).
% 2.40/1.38  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_458])).
% 2.40/1.38  tff(c_473, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.40/1.38  tff(c_34, plain, (![A_35]: (k2_relat_1(k4_relat_1(A_35))=k1_relat_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.40/1.38  tff(c_28, plain, (![A_29]: (v1_relat_1(k4_relat_1(A_29)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.40/1.38  tff(c_472, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.40/1.38  tff(c_478, plain, (![B_79, A_80]: (k2_xboole_0(B_79, A_80)=k2_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.40/1.38  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.38  tff(c_494, plain, (![A_80]: (k2_xboole_0(k1_xboole_0, A_80)=A_80)), inference(superposition, [status(thm), theory('equality')], [c_478, c_6])).
% 2.40/1.38  tff(c_629, plain, (![A_95, B_96]: (k2_xboole_0(k2_relat_1(A_95), k2_relat_1(B_96))=k2_relat_1(k2_xboole_0(A_95, B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.40/1.38  tff(c_4, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | k2_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.38  tff(c_662, plain, (![A_97, B_98]: (k2_relat_1(A_97)=k1_xboole_0 | k2_relat_1(k2_xboole_0(A_97, B_98))!=k1_xboole_0 | ~v1_relat_1(B_98) | ~v1_relat_1(A_97))), inference(superposition, [status(thm), theory('equality')], [c_629, c_4])).
% 2.40/1.38  tff(c_668, plain, (![A_80]: (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(A_80)!=k1_xboole_0 | ~v1_relat_1(A_80) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_494, c_662])).
% 2.40/1.38  tff(c_679, plain, (![A_80]: (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(A_80)!=k1_xboole_0 | ~v1_relat_1(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_668])).
% 2.40/1.38  tff(c_683, plain, (![A_99]: (k2_relat_1(A_99)!=k1_xboole_0 | ~v1_relat_1(A_99))), inference(negUnitSimplification, [status(thm)], [c_472, c_679])).
% 2.40/1.38  tff(c_720, plain, (![A_104]: (k2_relat_1(k4_relat_1(A_104))!=k1_xboole_0 | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_28, c_683])).
% 2.40/1.38  tff(c_724, plain, (![A_105]: (k1_relat_1(A_105)!=k1_xboole_0 | ~v1_relat_1(A_105) | ~v1_relat_1(A_105))), inference(superposition, [status(thm), theory('equality')], [c_34, c_720])).
% 2.40/1.38  tff(c_728, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_53, c_724])).
% 2.40/1.38  tff(c_735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_473, c_728])).
% 2.40/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.38  
% 2.40/1.38  Inference rules
% 2.40/1.38  ----------------------
% 2.40/1.38  #Ref     : 0
% 2.40/1.38  #Sup     : 160
% 2.40/1.38  #Fact    : 0
% 2.40/1.38  #Define  : 0
% 2.40/1.38  #Split   : 1
% 2.40/1.38  #Chain   : 0
% 2.40/1.38  #Close   : 0
% 2.40/1.38  
% 2.40/1.38  Ordering : KBO
% 2.40/1.38  
% 2.40/1.38  Simplification rules
% 2.40/1.38  ----------------------
% 2.40/1.38  #Subsume      : 22
% 2.40/1.38  #Demod        : 21
% 2.40/1.38  #Tautology    : 77
% 2.40/1.38  #SimpNegUnit  : 3
% 2.40/1.38  #BackRed      : 0
% 2.40/1.38  
% 2.40/1.38  #Partial instantiations: 0
% 2.40/1.38  #Strategies tried      : 1
% 2.40/1.38  
% 2.40/1.38  Timing (in seconds)
% 2.40/1.38  ----------------------
% 2.40/1.39  Preprocessing        : 0.28
% 2.40/1.39  Parsing              : 0.15
% 2.40/1.39  CNF conversion       : 0.02
% 2.40/1.39  Main loop            : 0.29
% 2.40/1.39  Inferencing          : 0.11
% 2.40/1.39  Reduction            : 0.09
% 2.40/1.39  Demodulation         : 0.06
% 2.40/1.39  BG Simplification    : 0.02
% 2.40/1.39  Subsumption          : 0.05
% 2.40/1.39  Abstraction          : 0.01
% 2.40/1.39  MUC search           : 0.00
% 2.40/1.39  Cooper               : 0.00
% 2.40/1.39  Total                : 0.60
% 2.40/1.39  Index Insertion      : 0.00
% 2.40/1.39  Index Deletion       : 0.00
% 2.40/1.39  Index Matching       : 0.00
% 2.40/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
