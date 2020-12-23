%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:15 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   61 (  76 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   79 ( 114 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_10 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_52,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_54,plain,
    ( k11_relat_1('#skF_10','#skF_9') = k1_xboole_0
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_82,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( r2_hidden('#skF_9',k1_relat_1('#skF_10'))
    | k11_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_83,plain,(
    k11_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_253,plain,(
    ! [A_94,B_95,C_96] :
      ( r2_hidden(k4_tarski(A_94,B_95),C_96)
      | ~ r2_hidden(B_95,k11_relat_1(C_96,A_94))
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    ! [C_33,A_18,D_36] :
      ( r2_hidden(C_33,k1_relat_1(A_18))
      | ~ r2_hidden(k4_tarski(C_33,D_36),A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_268,plain,(
    ! [A_97,C_98,B_99] :
      ( r2_hidden(A_97,k1_relat_1(C_98))
      | ~ r2_hidden(B_99,k11_relat_1(C_98,A_97))
      | ~ v1_relat_1(C_98) ) ),
    inference(resolution,[status(thm)],[c_253,c_34])).

tff(c_285,plain,(
    ! [A_100,C_101] :
      ( r2_hidden(A_100,k1_relat_1(C_101))
      | ~ v1_relat_1(C_101)
      | k11_relat_1(C_101,A_100) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_268])).

tff(c_292,plain,
    ( ~ v1_relat_1('#skF_10')
    | k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_285,c_82])).

tff(c_296,plain,(
    k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_292])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_296])).

tff(c_299,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_299])).

tff(c_302,plain,(
    k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_30,plain,(
    ! [A_15,B_17] :
      ( k9_relat_1(A_15,k1_tarski(B_17)) = k11_relat_1(A_15,B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_303,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_63,plain,(
    ! [A_46] : k2_tarski(A_46,A_46) = k1_tarski(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [D_13,A_8] : r2_hidden(D_13,k2_tarski(A_8,D_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_69,plain,(
    ! [A_46] : r2_hidden(A_46,k1_tarski(A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_12])).

tff(c_437,plain,(
    ! [B_130,A_131] :
      ( r1_xboole_0(k1_relat_1(B_130),A_131)
      | k9_relat_1(B_130,A_131) != k1_xboole_0
      | ~ v1_relat_1(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1150,plain,(
    ! [C_206,A_207,B_208] :
      ( ~ r2_hidden(C_206,A_207)
      | ~ r2_hidden(C_206,k1_relat_1(B_208))
      | k9_relat_1(B_208,A_207) != k1_xboole_0
      | ~ v1_relat_1(B_208) ) ),
    inference(resolution,[status(thm)],[c_437,c_2])).

tff(c_1268,plain,(
    ! [A_210,B_211] :
      ( ~ r2_hidden(A_210,k1_relat_1(B_211))
      | k9_relat_1(B_211,k1_tarski(A_210)) != k1_xboole_0
      | ~ v1_relat_1(B_211) ) ),
    inference(resolution,[status(thm)],[c_69,c_1150])).

tff(c_1317,plain,
    ( k9_relat_1('#skF_10',k1_tarski('#skF_9')) != k1_xboole_0
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_303,c_1268])).

tff(c_1342,plain,(
    k9_relat_1('#skF_10',k1_tarski('#skF_9')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1317])).

tff(c_1364,plain,
    ( k11_relat_1('#skF_10','#skF_9') != k1_xboole_0
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1342])).

tff(c_1367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_302,c_1364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.58  
% 3.28/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.58  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_10 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_1 > #skF_5
% 3.28/1.58  
% 3.28/1.58  %Foreground sorts:
% 3.28/1.58  
% 3.28/1.58  
% 3.28/1.58  %Background operators:
% 3.28/1.58  
% 3.28/1.58  
% 3.28/1.58  %Foreground operators:
% 3.28/1.58  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.28/1.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.28/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.28/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.28/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.28/1.58  tff('#skF_10', type, '#skF_10': $i).
% 3.28/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.58  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.28/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.28/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.28/1.58  tff('#skF_9', type, '#skF_9': $i).
% 3.28/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.28/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.58  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.28/1.58  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.28/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.28/1.58  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.28/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.58  
% 3.28/1.59  tff(f_95, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.28/1.59  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.28/1.59  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.28/1.59  tff(f_75, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.28/1.59  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.28/1.59  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.28/1.59  tff(f_60, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.28/1.59  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 3.28/1.59  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.28/1.59  tff(c_52, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.28/1.59  tff(c_54, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0 | ~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.28/1.59  tff(c_82, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.28/1.59  tff(c_60, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10')) | k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.28/1.59  tff(c_83, plain, (k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 3.28/1.59  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.59  tff(c_253, plain, (![A_94, B_95, C_96]: (r2_hidden(k4_tarski(A_94, B_95), C_96) | ~r2_hidden(B_95, k11_relat_1(C_96, A_94)) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.28/1.59  tff(c_34, plain, (![C_33, A_18, D_36]: (r2_hidden(C_33, k1_relat_1(A_18)) | ~r2_hidden(k4_tarski(C_33, D_36), A_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.28/1.59  tff(c_268, plain, (![A_97, C_98, B_99]: (r2_hidden(A_97, k1_relat_1(C_98)) | ~r2_hidden(B_99, k11_relat_1(C_98, A_97)) | ~v1_relat_1(C_98))), inference(resolution, [status(thm)], [c_253, c_34])).
% 3.28/1.59  tff(c_285, plain, (![A_100, C_101]: (r2_hidden(A_100, k1_relat_1(C_101)) | ~v1_relat_1(C_101) | k11_relat_1(C_101, A_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_268])).
% 3.28/1.59  tff(c_292, plain, (~v1_relat_1('#skF_10') | k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_285, c_82])).
% 3.28/1.59  tff(c_296, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_292])).
% 3.28/1.59  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_296])).
% 3.28/1.59  tff(c_299, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_60])).
% 3.28/1.59  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_299])).
% 3.28/1.59  tff(c_302, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.28/1.59  tff(c_30, plain, (![A_15, B_17]: (k9_relat_1(A_15, k1_tarski(B_17))=k11_relat_1(A_15, B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.28/1.59  tff(c_303, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_54])).
% 3.28/1.59  tff(c_63, plain, (![A_46]: (k2_tarski(A_46, A_46)=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.28/1.59  tff(c_12, plain, (![D_13, A_8]: (r2_hidden(D_13, k2_tarski(A_8, D_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.28/1.59  tff(c_69, plain, (![A_46]: (r2_hidden(A_46, k1_tarski(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_12])).
% 3.28/1.59  tff(c_437, plain, (![B_130, A_131]: (r1_xboole_0(k1_relat_1(B_130), A_131) | k9_relat_1(B_130, A_131)!=k1_xboole_0 | ~v1_relat_1(B_130))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.28/1.59  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.59  tff(c_1150, plain, (![C_206, A_207, B_208]: (~r2_hidden(C_206, A_207) | ~r2_hidden(C_206, k1_relat_1(B_208)) | k9_relat_1(B_208, A_207)!=k1_xboole_0 | ~v1_relat_1(B_208))), inference(resolution, [status(thm)], [c_437, c_2])).
% 3.28/1.59  tff(c_1268, plain, (![A_210, B_211]: (~r2_hidden(A_210, k1_relat_1(B_211)) | k9_relat_1(B_211, k1_tarski(A_210))!=k1_xboole_0 | ~v1_relat_1(B_211))), inference(resolution, [status(thm)], [c_69, c_1150])).
% 3.28/1.59  tff(c_1317, plain, (k9_relat_1('#skF_10', k1_tarski('#skF_9'))!=k1_xboole_0 | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_303, c_1268])).
% 3.28/1.59  tff(c_1342, plain, (k9_relat_1('#skF_10', k1_tarski('#skF_9'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1317])).
% 3.28/1.59  tff(c_1364, plain, (k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0 | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1342])).
% 3.28/1.59  tff(c_1367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_302, c_1364])).
% 3.28/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.59  
% 3.28/1.59  Inference rules
% 3.28/1.59  ----------------------
% 3.28/1.59  #Ref     : 0
% 3.28/1.59  #Sup     : 288
% 3.28/1.59  #Fact    : 0
% 3.28/1.59  #Define  : 0
% 3.28/1.59  #Split   : 2
% 3.28/1.59  #Chain   : 0
% 3.28/1.59  #Close   : 0
% 3.28/1.59  
% 3.28/1.59  Ordering : KBO
% 3.28/1.59  
% 3.28/1.59  Simplification rules
% 3.28/1.59  ----------------------
% 3.28/1.59  #Subsume      : 16
% 3.28/1.59  #Demod        : 43
% 3.28/1.59  #Tautology    : 81
% 3.28/1.59  #SimpNegUnit  : 2
% 3.28/1.59  #BackRed      : 0
% 3.28/1.59  
% 3.28/1.59  #Partial instantiations: 0
% 3.28/1.59  #Strategies tried      : 1
% 3.28/1.59  
% 3.28/1.59  Timing (in seconds)
% 3.28/1.59  ----------------------
% 3.28/1.59  Preprocessing        : 0.34
% 3.28/1.59  Parsing              : 0.18
% 3.28/1.59  CNF conversion       : 0.03
% 3.28/1.59  Main loop            : 0.43
% 3.28/1.59  Inferencing          : 0.16
% 3.28/1.60  Reduction            : 0.11
% 3.28/1.60  Demodulation         : 0.09
% 3.28/1.60  BG Simplification    : 0.02
% 3.28/1.60  Subsumption          : 0.09
% 3.28/1.60  Abstraction          : 0.03
% 3.28/1.60  MUC search           : 0.00
% 3.28/1.60  Cooper               : 0.00
% 3.28/1.60  Total                : 0.79
% 3.28/1.60  Index Insertion      : 0.00
% 3.28/1.60  Index Deletion       : 0.00
% 3.28/1.60  Index Matching       : 0.00
% 3.28/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
