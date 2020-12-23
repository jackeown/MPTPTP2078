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
% DateTime   : Thu Dec  3 09:58:54 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 126 expanded)
%              Number of leaves         :   31 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 193 expanded)
%              Number of equality atoms :   23 (  53 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_36,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_111,plain,(
    ! [C_57,A_58] :
      ( r2_hidden(k4_tarski(C_57,'#skF_6'(A_58,k1_relat_1(A_58),C_57)),A_58)
      | ~ r2_hidden(C_57,k1_relat_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_71,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,k3_xboole_0(A_42,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_78,plain,(
    ! [A_8,C_44] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_44,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_81,plain,(
    ! [C_44] : ~ r2_hidden(C_44,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_78])).

tff(c_130,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_111,c_81])).

tff(c_138,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_138])).

tff(c_144,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    ! [A_36] :
      ( v1_relat_1(A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_145,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_337,plain,(
    ! [A_98,B_99] :
      ( r2_hidden(k4_tarski('#skF_3'(A_98,B_99),'#skF_4'(A_98,B_99)),A_98)
      | r2_hidden('#skF_5'(A_98,B_99),B_99)
      | k1_relat_1(A_98) = B_99 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_168,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_175,plain,(
    ! [A_8,C_67] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_67,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_168])).

tff(c_178,plain,(
    ! [C_67] : ~ r2_hidden(C_67,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_175])).

tff(c_356,plain,(
    ! [B_99] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_99),B_99)
      | k1_relat_1(k1_xboole_0) = B_99 ) ),
    inference(resolution,[status(thm)],[c_337,c_178])).

tff(c_366,plain,(
    ! [B_99] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_99),B_99)
      | k1_xboole_0 = B_99 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_356])).

tff(c_28,plain,(
    ! [A_30] :
      ( v1_relat_1(k4_relat_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ! [A_34] :
      ( k2_relat_1(k4_relat_1(A_34)) = k1_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_203,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_7'(A_76,B_77),k2_relat_1(B_77))
      | ~ r2_hidden(A_76,k1_relat_1(B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_818,plain,(
    ! [A_126,A_127] :
      ( r2_hidden('#skF_7'(A_126,k4_relat_1(A_127)),k1_relat_1(A_127))
      | ~ r2_hidden(A_126,k1_relat_1(k4_relat_1(A_127)))
      | ~ v1_relat_1(k4_relat_1(A_127))
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_203])).

tff(c_866,plain,(
    ! [A_126] :
      ( r2_hidden('#skF_7'(A_126,k4_relat_1(k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(A_126,k1_relat_1(k4_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_818])).

tff(c_880,plain,(
    ! [A_126] :
      ( r2_hidden('#skF_7'(A_126,k4_relat_1(k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(A_126,k1_relat_1(k4_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_866])).

tff(c_881,plain,(
    ! [A_126] :
      ( ~ r2_hidden(A_126,k1_relat_1(k4_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_880])).

tff(c_882,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_881])).

tff(c_885,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_882])).

tff(c_889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_885])).

tff(c_892,plain,(
    ! [A_128] : ~ r2_hidden(A_128,k1_relat_1(k4_relat_1(k1_xboole_0))) ),
    inference(splitRight,[status(thm)],[c_881])).

tff(c_934,plain,(
    k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_366,c_892])).

tff(c_34,plain,(
    ! [A_34] :
      ( k1_relat_1(k4_relat_1(A_34)) = k2_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_953,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_934,c_34])).

tff(c_966,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_953])).

tff(c_968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:19:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.81  
% 3.03/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.81  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 3.03/1.81  
% 3.03/1.81  %Foreground sorts:
% 3.03/1.81  
% 3.03/1.81  
% 3.03/1.81  %Background operators:
% 3.03/1.81  
% 3.03/1.81  
% 3.03/1.81  %Foreground operators:
% 3.03/1.81  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.03/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.81  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.03/1.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.03/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.03/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.03/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.03/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.03/1.81  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.03/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.03/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.03/1.81  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.03/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.03/1.81  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.03/1.81  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.03/1.81  
% 3.03/1.83  tff(f_87, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.03/1.83  tff(f_48, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.03/1.83  tff(f_64, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.03/1.83  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.03/1.83  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.03/1.83  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.03/1.83  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.03/1.83  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.03/1.83  tff(f_68, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.03/1.83  tff(f_83, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 3.03/1.83  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 3.03/1.83  tff(c_36, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.03/1.83  tff(c_52, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 3.03/1.83  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.03/1.83  tff(c_111, plain, (![C_57, A_58]: (r2_hidden(k4_tarski(C_57, '#skF_6'(A_58, k1_relat_1(A_58), C_57)), A_58) | ~r2_hidden(C_57, k1_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.03/1.83  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.03/1.83  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.03/1.83  tff(c_71, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, k3_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.03/1.83  tff(c_78, plain, (![A_8, C_44]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_71])).
% 3.03/1.83  tff(c_81, plain, (![C_44]: (~r2_hidden(C_44, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_78])).
% 3.03/1.83  tff(c_130, plain, (![C_62]: (~r2_hidden(C_62, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_111, c_81])).
% 3.03/1.83  tff(c_138, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_130])).
% 3.03/1.83  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_138])).
% 3.03/1.83  tff(c_144, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.03/1.83  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.03/1.83  tff(c_38, plain, (![A_36]: (v1_relat_1(A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.03/1.83  tff(c_42, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_38])).
% 3.03/1.83  tff(c_145, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.03/1.83  tff(c_337, plain, (![A_98, B_99]: (r2_hidden(k4_tarski('#skF_3'(A_98, B_99), '#skF_4'(A_98, B_99)), A_98) | r2_hidden('#skF_5'(A_98, B_99), B_99) | k1_relat_1(A_98)=B_99)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.03/1.83  tff(c_168, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.03/1.83  tff(c_175, plain, (![A_8, C_67]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_168])).
% 3.03/1.83  tff(c_178, plain, (![C_67]: (~r2_hidden(C_67, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_175])).
% 3.03/1.83  tff(c_356, plain, (![B_99]: (r2_hidden('#skF_5'(k1_xboole_0, B_99), B_99) | k1_relat_1(k1_xboole_0)=B_99)), inference(resolution, [status(thm)], [c_337, c_178])).
% 3.03/1.83  tff(c_366, plain, (![B_99]: (r2_hidden('#skF_5'(k1_xboole_0, B_99), B_99) | k1_xboole_0=B_99)), inference(demodulation, [status(thm), theory('equality')], [c_145, c_356])).
% 3.03/1.83  tff(c_28, plain, (![A_30]: (v1_relat_1(k4_relat_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.03/1.83  tff(c_32, plain, (![A_34]: (k2_relat_1(k4_relat_1(A_34))=k1_relat_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.03/1.83  tff(c_203, plain, (![A_76, B_77]: (r2_hidden('#skF_7'(A_76, B_77), k2_relat_1(B_77)) | ~r2_hidden(A_76, k1_relat_1(B_77)) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.03/1.83  tff(c_818, plain, (![A_126, A_127]: (r2_hidden('#skF_7'(A_126, k4_relat_1(A_127)), k1_relat_1(A_127)) | ~r2_hidden(A_126, k1_relat_1(k4_relat_1(A_127))) | ~v1_relat_1(k4_relat_1(A_127)) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_32, c_203])).
% 3.03/1.83  tff(c_866, plain, (![A_126]: (r2_hidden('#skF_7'(A_126, k4_relat_1(k1_xboole_0)), k1_xboole_0) | ~r2_hidden(A_126, k1_relat_1(k4_relat_1(k1_xboole_0))) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_145, c_818])).
% 3.03/1.83  tff(c_880, plain, (![A_126]: (r2_hidden('#skF_7'(A_126, k4_relat_1(k1_xboole_0)), k1_xboole_0) | ~r2_hidden(A_126, k1_relat_1(k4_relat_1(k1_xboole_0))) | ~v1_relat_1(k4_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_866])).
% 3.03/1.83  tff(c_881, plain, (![A_126]: (~r2_hidden(A_126, k1_relat_1(k4_relat_1(k1_xboole_0))) | ~v1_relat_1(k4_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_178, c_880])).
% 3.03/1.83  tff(c_882, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_881])).
% 3.03/1.83  tff(c_885, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_882])).
% 3.03/1.83  tff(c_889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_885])).
% 3.03/1.83  tff(c_892, plain, (![A_128]: (~r2_hidden(A_128, k1_relat_1(k4_relat_1(k1_xboole_0))))), inference(splitRight, [status(thm)], [c_881])).
% 3.03/1.83  tff(c_934, plain, (k1_relat_1(k4_relat_1(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_366, c_892])).
% 3.03/1.83  tff(c_34, plain, (![A_34]: (k1_relat_1(k4_relat_1(A_34))=k2_relat_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.03/1.83  tff(c_953, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_934, c_34])).
% 3.03/1.83  tff(c_966, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_953])).
% 3.03/1.83  tff(c_968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_966])).
% 3.03/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.83  
% 3.03/1.83  Inference rules
% 3.03/1.83  ----------------------
% 3.03/1.83  #Ref     : 0
% 3.03/1.83  #Sup     : 197
% 3.03/1.83  #Fact    : 0
% 3.03/1.83  #Define  : 0
% 3.03/1.83  #Split   : 2
% 3.03/1.83  #Chain   : 0
% 3.03/1.83  #Close   : 0
% 3.03/1.83  
% 3.03/1.83  Ordering : KBO
% 3.03/1.83  
% 3.03/1.83  Simplification rules
% 3.03/1.83  ----------------------
% 3.03/1.83  #Subsume      : 48
% 3.03/1.83  #Demod        : 146
% 3.03/1.83  #Tautology    : 58
% 3.03/1.83  #SimpNegUnit  : 21
% 3.03/1.83  #BackRed      : 1
% 3.03/1.83  
% 3.03/1.83  #Partial instantiations: 0
% 3.03/1.83  #Strategies tried      : 1
% 3.03/1.83  
% 3.03/1.83  Timing (in seconds)
% 3.03/1.83  ----------------------
% 3.03/1.83  Preprocessing        : 0.45
% 3.03/1.83  Parsing              : 0.25
% 3.03/1.83  CNF conversion       : 0.03
% 3.03/1.83  Main loop            : 0.48
% 3.03/1.83  Inferencing          : 0.19
% 3.03/1.83  Reduction            : 0.13
% 3.03/1.83  Demodulation         : 0.09
% 3.03/1.83  BG Simplification    : 0.02
% 3.03/1.83  Subsumption          : 0.09
% 3.03/1.83  Abstraction          : 0.02
% 3.03/1.83  MUC search           : 0.00
% 3.03/1.83  Cooper               : 0.00
% 3.03/1.83  Total                : 0.97
% 3.03/1.83  Index Insertion      : 0.00
% 3.03/1.83  Index Deletion       : 0.00
% 3.03/1.83  Index Matching       : 0.00
% 3.03/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
