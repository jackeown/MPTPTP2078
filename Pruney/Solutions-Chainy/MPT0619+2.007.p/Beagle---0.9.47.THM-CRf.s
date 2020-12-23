%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:52 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 141 expanded)
%              Number of leaves         :   32 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  101 ( 276 expanded)
%              Number of equality atoms :   43 ( 123 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_133,plain,(
    ! [A_45,B_46] :
      ( k9_relat_1(A_45,k1_tarski(B_46)) = k11_relat_1(A_45,B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_154,plain,(
    ! [A_50] :
      ( k9_relat_1(A_50,k1_relat_1('#skF_3')) = k11_relat_1(A_50,'#skF_2')
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_133])).

tff(c_26,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_161,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_26])).

tff(c_171,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_161])).

tff(c_142,plain,(
    ! [A_45] :
      ( k9_relat_1(A_45,k1_relat_1('#skF_3')) = k11_relat_1(A_45,'#skF_2')
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_133])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | ~ r1_tarski(k1_tarski(A_37),B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    ! [A_39] : r2_hidden(A_39,k1_tarski(A_39)) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_98,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_95])).

tff(c_183,plain,(
    ! [B_57,A_58] :
      ( r1_xboole_0(k1_relat_1(B_57),A_58)
      | k9_relat_1(B_57,A_58) != k1_xboole_0
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_77,plain,(
    ! [A_34,B_35] :
      ( ~ r2_hidden(A_34,B_35)
      | ~ r1_xboole_0(k1_tarski(A_34),B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    ! [B_35] :
      ( ~ r2_hidden('#skF_2',B_35)
      | ~ r1_xboole_0(k1_relat_1('#skF_3'),B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_77])).

tff(c_190,plain,(
    ! [A_58] :
      ( ~ r2_hidden('#skF_2',A_58)
      | k9_relat_1('#skF_3',A_58) != k1_xboole_0
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_183,c_80])).

tff(c_195,plain,(
    ! [A_59] :
      ( ~ r2_hidden('#skF_2',A_59)
      | k9_relat_1('#skF_3',A_59) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_190])).

tff(c_203,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_195])).

tff(c_208,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_203])).

tff(c_213,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_171,c_208])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_1'(A_13,B_14),A_13)
      | k1_xboole_0 = A_13
      | k1_tarski(B_14) = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ r2_hidden(B_23,k11_relat_1(C_24,A_22))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_272,plain,(
    ! [C_69,A_70,B_71] :
      ( k1_funct_1(C_69,A_70) = B_71
      | ~ r2_hidden(k4_tarski(A_70,B_71),C_69)
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_324,plain,(
    ! [C_78,A_79,B_80] :
      ( k1_funct_1(C_78,A_79) = B_80
      | ~ v1_funct_1(C_78)
      | ~ r2_hidden(B_80,k11_relat_1(C_78,A_79))
      | ~ v1_relat_1(C_78) ) ),
    inference(resolution,[status(thm)],[c_32,c_272])).

tff(c_335,plain,(
    ! [B_80] :
      ( k1_funct_1('#skF_3','#skF_2') = B_80
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_80,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_324])).

tff(c_340,plain,(
    ! [B_81] :
      ( k1_funct_1('#skF_3','#skF_2') = B_81
      | ~ r2_hidden(B_81,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_335])).

tff(c_348,plain,(
    ! [B_14] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_14) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_14) ) ),
    inference(resolution,[status(thm)],[c_22,c_340])).

tff(c_353,plain,(
    ! [B_82] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_82) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_82) ) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_348])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( '#skF_1'(A_13,B_14) != B_14
      | k1_xboole_0 = A_13
      | k1_tarski(B_14) = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_361,plain,(
    ! [B_82] :
      ( k1_funct_1('#skF_3','#skF_2') != B_82
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_82)
      | k2_relat_1('#skF_3') = k1_tarski(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_20])).

tff(c_369,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_361])).

tff(c_42,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:11:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.35  
% 2.32/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.32/1.35  
% 2.32/1.35  %Foreground sorts:
% 2.32/1.35  
% 2.32/1.35  
% 2.32/1.35  %Background operators:
% 2.32/1.35  
% 2.32/1.35  
% 2.32/1.35  %Foreground operators:
% 2.32/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.32/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.32/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.35  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.32/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.32/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.32/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.35  
% 2.32/1.36  tff(f_100, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.32/1.36  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.32/1.36  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.32/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.32/1.36  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.32/1.36  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.32/1.36  tff(f_46, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.32/1.36  tff(f_60, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.32/1.36  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.32/1.36  tff(f_91, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.32/1.36  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.36  tff(c_44, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.36  tff(c_133, plain, (![A_45, B_46]: (k9_relat_1(A_45, k1_tarski(B_46))=k11_relat_1(A_45, B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.32/1.36  tff(c_154, plain, (![A_50]: (k9_relat_1(A_50, k1_relat_1('#skF_3'))=k11_relat_1(A_50, '#skF_2') | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_44, c_133])).
% 2.32/1.36  tff(c_26, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.32/1.36  tff(c_161, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_154, c_26])).
% 2.32/1.36  tff(c_171, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_161])).
% 2.32/1.36  tff(c_142, plain, (![A_45]: (k9_relat_1(A_45, k1_relat_1('#skF_3'))=k11_relat_1(A_45, '#skF_2') | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_44, c_133])).
% 2.32/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.36  tff(c_82, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | ~r1_tarski(k1_tarski(A_37), B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.32/1.36  tff(c_95, plain, (![A_39]: (r2_hidden(A_39, k1_tarski(A_39)))), inference(resolution, [status(thm)], [c_6, c_82])).
% 2.32/1.36  tff(c_98, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_95])).
% 2.32/1.36  tff(c_183, plain, (![B_57, A_58]: (r1_xboole_0(k1_relat_1(B_57), A_58) | k9_relat_1(B_57, A_58)!=k1_xboole_0 | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.32/1.36  tff(c_77, plain, (![A_34, B_35]: (~r2_hidden(A_34, B_35) | ~r1_xboole_0(k1_tarski(A_34), B_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.32/1.36  tff(c_80, plain, (![B_35]: (~r2_hidden('#skF_2', B_35) | ~r1_xboole_0(k1_relat_1('#skF_3'), B_35))), inference(superposition, [status(thm), theory('equality')], [c_44, c_77])).
% 2.32/1.36  tff(c_190, plain, (![A_58]: (~r2_hidden('#skF_2', A_58) | k9_relat_1('#skF_3', A_58)!=k1_xboole_0 | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_183, c_80])).
% 2.32/1.36  tff(c_195, plain, (![A_59]: (~r2_hidden('#skF_2', A_59) | k9_relat_1('#skF_3', A_59)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_190])).
% 2.32/1.36  tff(c_203, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_98, c_195])).
% 2.32/1.36  tff(c_208, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_203])).
% 2.32/1.36  tff(c_213, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_171, c_208])).
% 2.32/1.36  tff(c_22, plain, (![A_13, B_14]: (r2_hidden('#skF_1'(A_13, B_14), A_13) | k1_xboole_0=A_13 | k1_tarski(B_14)=A_13)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.36  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.36  tff(c_32, plain, (![A_22, B_23, C_24]: (r2_hidden(k4_tarski(A_22, B_23), C_24) | ~r2_hidden(B_23, k11_relat_1(C_24, A_22)) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.36  tff(c_272, plain, (![C_69, A_70, B_71]: (k1_funct_1(C_69, A_70)=B_71 | ~r2_hidden(k4_tarski(A_70, B_71), C_69) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.32/1.36  tff(c_324, plain, (![C_78, A_79, B_80]: (k1_funct_1(C_78, A_79)=B_80 | ~v1_funct_1(C_78) | ~r2_hidden(B_80, k11_relat_1(C_78, A_79)) | ~v1_relat_1(C_78))), inference(resolution, [status(thm)], [c_32, c_272])).
% 2.32/1.36  tff(c_335, plain, (![B_80]: (k1_funct_1('#skF_3', '#skF_2')=B_80 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_80, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_324])).
% 2.32/1.36  tff(c_340, plain, (![B_81]: (k1_funct_1('#skF_3', '#skF_2')=B_81 | ~r2_hidden(B_81, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_335])).
% 2.32/1.36  tff(c_348, plain, (![B_14]: ('#skF_1'(k2_relat_1('#skF_3'), B_14)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_14))), inference(resolution, [status(thm)], [c_22, c_340])).
% 2.32/1.36  tff(c_353, plain, (![B_82]: ('#skF_1'(k2_relat_1('#skF_3'), B_82)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_82))), inference(negUnitSimplification, [status(thm)], [c_213, c_348])).
% 2.32/1.36  tff(c_20, plain, (![A_13, B_14]: ('#skF_1'(A_13, B_14)!=B_14 | k1_xboole_0=A_13 | k1_tarski(B_14)=A_13)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.36  tff(c_361, plain, (![B_82]: (k1_funct_1('#skF_3', '#skF_2')!=B_82 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_82) | k2_relat_1('#skF_3')=k1_tarski(B_82))), inference(superposition, [status(thm), theory('equality')], [c_353, c_20])).
% 2.32/1.36  tff(c_369, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_213, c_361])).
% 2.32/1.36  tff(c_42, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.32/1.36  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_369, c_42])).
% 2.32/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.36  
% 2.32/1.36  Inference rules
% 2.32/1.36  ----------------------
% 2.32/1.36  #Ref     : 0
% 2.32/1.36  #Sup     : 65
% 2.32/1.36  #Fact    : 0
% 2.32/1.36  #Define  : 0
% 2.32/1.36  #Split   : 0
% 2.32/1.36  #Chain   : 0
% 2.32/1.36  #Close   : 0
% 2.32/1.36  
% 2.32/1.36  Ordering : KBO
% 2.32/1.36  
% 2.32/1.36  Simplification rules
% 2.32/1.36  ----------------------
% 2.32/1.36  #Subsume      : 5
% 2.32/1.36  #Demod        : 25
% 2.32/1.36  #Tautology    : 31
% 2.32/1.36  #SimpNegUnit  : 3
% 2.32/1.36  #BackRed      : 1
% 2.32/1.36  
% 2.32/1.36  #Partial instantiations: 0
% 2.32/1.36  #Strategies tried      : 1
% 2.32/1.36  
% 2.32/1.36  Timing (in seconds)
% 2.32/1.36  ----------------------
% 2.32/1.37  Preprocessing        : 0.33
% 2.32/1.37  Parsing              : 0.18
% 2.32/1.37  CNF conversion       : 0.02
% 2.51/1.37  Main loop            : 0.22
% 2.51/1.37  Inferencing          : 0.08
% 2.51/1.37  Reduction            : 0.07
% 2.51/1.37  Demodulation         : 0.05
% 2.51/1.37  BG Simplification    : 0.02
% 2.51/1.37  Subsumption          : 0.04
% 2.51/1.37  Abstraction          : 0.01
% 2.51/1.37  MUC search           : 0.00
% 2.51/1.37  Cooper               : 0.00
% 2.51/1.37  Total                : 0.58
% 2.51/1.37  Index Insertion      : 0.00
% 2.51/1.37  Index Deletion       : 0.00
% 2.51/1.37  Index Matching       : 0.00
% 2.51/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
