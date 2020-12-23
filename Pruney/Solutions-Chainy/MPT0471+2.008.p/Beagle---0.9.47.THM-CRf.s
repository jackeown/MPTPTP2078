%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:21 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 117 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 205 expanded)
%              Number of equality atoms :   31 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_93,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_58,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_56,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_36,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_2'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_37,plain,(
    ! [A_27] :
      ( v1_relat_1(A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_41,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_37])).

tff(c_57,plain,(
    ! [A_30] :
      ( v1_xboole_0(k1_relat_1(A_30))
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_66,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) = k1_xboole_0
      | ~ v1_xboole_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_74,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_66])).

tff(c_355,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_3'(A_61,B_62),k1_relat_1(B_62))
      | ~ r2_hidden(A_61,k2_relat_1(B_62))
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_361,plain,(
    ! [A_61] :
      ( r2_hidden('#skF_3'(A_61,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_61,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_355])).

tff(c_363,plain,(
    ! [A_61] :
      ( r2_hidden('#skF_3'(A_61,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_61,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_361])).

tff(c_91,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k2_xboole_0(A_34,B_35)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_98,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_91])).

tff(c_10,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3),A_2)
      | r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_164,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,B_51)
      | ~ r2_hidden(C_52,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_438,plain,(
    ! [C_67,B_68,A_69] :
      ( ~ r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | k4_xboole_0(A_69,B_68) != A_69 ) ),
    inference(resolution,[status(thm)],[c_22,c_164])).

tff(c_1956,plain,(
    ! [A_124,B_125,A_126] :
      ( ~ r2_hidden('#skF_1'(A_124,B_125),A_126)
      | k4_xboole_0(A_126,A_124) != A_126
      | r1_xboole_0(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_10,c_438])).

tff(c_1962,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,A_2) != A_2
      | r1_xboole_0(A_2,B_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_1956])).

tff(c_1967,plain,(
    ! [A_127,B_128] :
      ( k1_xboole_0 != A_127
      | r1_xboole_0(A_127,B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1962])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1975,plain,(
    ! [B_128] : k4_xboole_0(k1_xboole_0,B_128) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1967,c_20])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3),B_3)
      | r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2181,plain,(
    ! [B_131,A_132] :
      ( k4_xboole_0(B_131,A_132) != B_131
      | r1_xboole_0(A_132,B_131) ) ),
    inference(resolution,[status(thm)],[c_8,c_1956])).

tff(c_6,plain,(
    ! [A_2,B_3,C_6] :
      ( ~ r1_xboole_0(A_2,B_3)
      | ~ r2_hidden(C_6,B_3)
      | ~ r2_hidden(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2576,plain,(
    ! [C_150,B_151,A_152] :
      ( ~ r2_hidden(C_150,B_151)
      | ~ r2_hidden(C_150,A_152)
      | k4_xboole_0(B_151,A_152) != B_151 ) ),
    inference(resolution,[status(thm)],[c_2181,c_6])).

tff(c_2578,plain,(
    ! [A_61,A_152] :
      ( ~ r2_hidden('#skF_3'(A_61,k1_xboole_0),A_152)
      | k4_xboole_0(k1_xboole_0,A_152) != k1_xboole_0
      | ~ r2_hidden(A_61,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_363,c_2576])).

tff(c_3017,plain,(
    ! [A_159,A_160] :
      ( ~ r2_hidden('#skF_3'(A_159,k1_xboole_0),A_160)
      | ~ r2_hidden(A_159,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1975,c_2578])).

tff(c_3029,plain,(
    ! [A_161] : ~ r2_hidden(A_161,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_363,c_3017])).

tff(c_3044,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_3029])).

tff(c_168,plain,(
    ! [A_53] :
      ( k2_xboole_0(k1_relat_1(A_53),k2_relat_1(A_53)) = k3_relat_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_183,plain,
    ( k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_168])).

tff(c_187,plain,(
    k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k3_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_183])).

tff(c_3051,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k3_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3044,c_187])).

tff(c_3055,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3051])).

tff(c_3057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_3055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:35:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.68  
% 3.76/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.68  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.00/1.68  
% 4.00/1.68  %Foreground sorts:
% 4.00/1.68  
% 4.00/1.68  
% 4.00/1.68  %Background operators:
% 4.00/1.68  
% 4.00/1.68  
% 4.00/1.68  %Foreground operators:
% 4.00/1.68  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.00/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.00/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.00/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.00/1.68  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.00/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.00/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.00/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.00/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.00/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.00/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.00/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.00/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.00/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.00/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.00/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.00/1.68  
% 4.00/1.69  tff(f_93, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 4.00/1.69  tff(f_58, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.00/1.69  tff(f_56, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.00/1.69  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.00/1.69  tff(f_74, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.00/1.69  tff(f_82, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 4.00/1.69  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.00/1.69  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 4.00/1.69  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.00/1.69  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.00/1.69  tff(f_66, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.00/1.69  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 4.00/1.69  tff(c_36, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.00/1.69  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.00/1.69  tff(c_12, plain, (![A_7]: (r2_hidden('#skF_2'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.00/1.69  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.00/1.69  tff(c_37, plain, (![A_27]: (v1_relat_1(A_27) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.00/1.69  tff(c_41, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_37])).
% 4.00/1.69  tff(c_57, plain, (![A_30]: (v1_xboole_0(k1_relat_1(A_30)) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.00/1.69  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.00/1.69  tff(c_66, plain, (![A_31]: (k1_relat_1(A_31)=k1_xboole_0 | ~v1_xboole_0(A_31))), inference(resolution, [status(thm)], [c_57, c_4])).
% 4.00/1.69  tff(c_74, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_66])).
% 4.00/1.69  tff(c_355, plain, (![A_61, B_62]: (r2_hidden('#skF_3'(A_61, B_62), k1_relat_1(B_62)) | ~r2_hidden(A_61, k2_relat_1(B_62)) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.00/1.69  tff(c_361, plain, (![A_61]: (r2_hidden('#skF_3'(A_61, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_61, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_74, c_355])).
% 4.00/1.69  tff(c_363, plain, (![A_61]: (r2_hidden('#skF_3'(A_61, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_61, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_361])).
% 4.00/1.69  tff(c_91, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k2_xboole_0(A_34, B_35))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.00/1.69  tff(c_98, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_91])).
% 4.00/1.69  tff(c_10, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3), A_2) | r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.00/1.69  tff(c_22, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.00/1.69  tff(c_164, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, B_51) | ~r2_hidden(C_52, A_50))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.00/1.69  tff(c_438, plain, (![C_67, B_68, A_69]: (~r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | k4_xboole_0(A_69, B_68)!=A_69)), inference(resolution, [status(thm)], [c_22, c_164])).
% 4.00/1.69  tff(c_1956, plain, (![A_124, B_125, A_126]: (~r2_hidden('#skF_1'(A_124, B_125), A_126) | k4_xboole_0(A_126, A_124)!=A_126 | r1_xboole_0(A_124, B_125))), inference(resolution, [status(thm)], [c_10, c_438])).
% 4.00/1.69  tff(c_1962, plain, (![A_2, B_3]: (k4_xboole_0(A_2, A_2)!=A_2 | r1_xboole_0(A_2, B_3))), inference(resolution, [status(thm)], [c_10, c_1956])).
% 4.00/1.69  tff(c_1967, plain, (![A_127, B_128]: (k1_xboole_0!=A_127 | r1_xboole_0(A_127, B_128))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1962])).
% 4.00/1.69  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.00/1.69  tff(c_1975, plain, (![B_128]: (k4_xboole_0(k1_xboole_0, B_128)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1967, c_20])).
% 4.00/1.69  tff(c_8, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3), B_3) | r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.00/1.69  tff(c_2181, plain, (![B_131, A_132]: (k4_xboole_0(B_131, A_132)!=B_131 | r1_xboole_0(A_132, B_131))), inference(resolution, [status(thm)], [c_8, c_1956])).
% 4.00/1.69  tff(c_6, plain, (![A_2, B_3, C_6]: (~r1_xboole_0(A_2, B_3) | ~r2_hidden(C_6, B_3) | ~r2_hidden(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.00/1.69  tff(c_2576, plain, (![C_150, B_151, A_152]: (~r2_hidden(C_150, B_151) | ~r2_hidden(C_150, A_152) | k4_xboole_0(B_151, A_152)!=B_151)), inference(resolution, [status(thm)], [c_2181, c_6])).
% 4.00/1.69  tff(c_2578, plain, (![A_61, A_152]: (~r2_hidden('#skF_3'(A_61, k1_xboole_0), A_152) | k4_xboole_0(k1_xboole_0, A_152)!=k1_xboole_0 | ~r2_hidden(A_61, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_363, c_2576])).
% 4.00/1.69  tff(c_3017, plain, (![A_159, A_160]: (~r2_hidden('#skF_3'(A_159, k1_xboole_0), A_160) | ~r2_hidden(A_159, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1975, c_2578])).
% 4.00/1.69  tff(c_3029, plain, (![A_161]: (~r2_hidden(A_161, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_363, c_3017])).
% 4.00/1.69  tff(c_3044, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_3029])).
% 4.00/1.69  tff(c_168, plain, (![A_53]: (k2_xboole_0(k1_relat_1(A_53), k2_relat_1(A_53))=k3_relat_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.00/1.69  tff(c_183, plain, (k2_xboole_0(k1_xboole_0, k2_relat_1(k1_xboole_0))=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_168])).
% 4.00/1.69  tff(c_187, plain, (k2_xboole_0(k1_xboole_0, k2_relat_1(k1_xboole_0))=k3_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_41, c_183])).
% 4.00/1.69  tff(c_3051, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k3_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3044, c_187])).
% 4.00/1.69  tff(c_3055, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3051])).
% 4.00/1.69  tff(c_3057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_3055])).
% 4.00/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.69  
% 4.00/1.69  Inference rules
% 4.00/1.69  ----------------------
% 4.00/1.69  #Ref     : 0
% 4.00/1.69  #Sup     : 776
% 4.00/1.69  #Fact    : 0
% 4.00/1.69  #Define  : 0
% 4.00/1.69  #Split   : 1
% 4.00/1.69  #Chain   : 0
% 4.00/1.69  #Close   : 0
% 4.00/1.69  
% 4.00/1.69  Ordering : KBO
% 4.00/1.69  
% 4.00/1.69  Simplification rules
% 4.00/1.69  ----------------------
% 4.00/1.69  #Subsume      : 89
% 4.00/1.69  #Demod        : 427
% 4.00/1.69  #Tautology    : 390
% 4.00/1.69  #SimpNegUnit  : 18
% 4.00/1.69  #BackRed      : 7
% 4.00/1.69  
% 4.00/1.69  #Partial instantiations: 0
% 4.00/1.69  #Strategies tried      : 1
% 4.00/1.69  
% 4.00/1.69  Timing (in seconds)
% 4.00/1.69  ----------------------
% 4.00/1.70  Preprocessing        : 0.31
% 4.00/1.70  Parsing              : 0.17
% 4.00/1.70  CNF conversion       : 0.02
% 4.00/1.70  Main loop            : 0.62
% 4.00/1.70  Inferencing          : 0.21
% 4.00/1.70  Reduction            : 0.24
% 4.00/1.70  Demodulation         : 0.18
% 4.00/1.70  BG Simplification    : 0.03
% 4.00/1.70  Subsumption          : 0.10
% 4.00/1.70  Abstraction          : 0.03
% 4.00/1.70  MUC search           : 0.00
% 4.00/1.70  Cooper               : 0.00
% 4.00/1.70  Total                : 0.96
% 4.00/1.70  Index Insertion      : 0.00
% 4.00/1.70  Index Deletion       : 0.00
% 4.00/1.70  Index Matching       : 0.00
% 4.00/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
