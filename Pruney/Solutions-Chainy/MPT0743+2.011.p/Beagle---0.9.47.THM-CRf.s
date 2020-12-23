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
% DateTime   : Thu Dec  3 10:06:10 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 449 expanded)
%              Number of leaves         :   21 ( 155 expanded)
%              Depth                    :   12
%              Number of atoms          :  179 (1241 expanded)
%              Number of equality atoms :   18 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_69,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_65,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_34,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ! [A_15] :
      ( v3_ordinal1(k1_ordinal1(A_15))
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_183,plain,(
    ! [B_52,A_53] :
      ( r2_hidden(B_52,A_53)
      | r1_ordinal1(A_53,B_52)
      | ~ v3_ordinal1(B_52)
      | ~ v3_ordinal1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_72,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_79,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_36])).

tff(c_221,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_183,c_79])).

tff(c_242,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_221])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r1_ordinal1(A_7,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_247,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ r1_ordinal1(A_55,B_56)
      | ~ v3_ordinal1(B_56)
      | ~ v3_ordinal1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_304,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_ordinal1(A_63,B_62)
      | ~ v3_ordinal1(B_62)
      | ~ v3_ordinal1(A_63) ) ),
    inference(resolution,[status(thm)],[c_247,c_4])).

tff(c_372,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_ordinal1(B_73,A_74)
      | ~ r1_ordinal1(A_74,B_73)
      | ~ v3_ordinal1(B_73)
      | ~ v3_ordinal1(A_74) ) ),
    inference(resolution,[status(thm)],[c_16,c_304])).

tff(c_384,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_242,c_372])).

tff(c_396,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_384])).

tff(c_402,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_26,plain,(
    ! [B_14,A_12] :
      ( r2_hidden(B_14,A_12)
      | r1_ordinal1(A_12,B_14)
      | ~ v3_ordinal1(B_14)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_388,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_372])).

tff(c_401,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_388])).

tff(c_415,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_418,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_415])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_418])).

tff(c_424,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_80,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,B_31)
      | r2_hidden(A_30,k1_ordinal1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_91,plain,(
    ! [B_31,A_30] :
      ( ~ r2_hidden(k1_ordinal1(B_31),A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_236,plain,(
    ! [A_53,B_31] :
      ( ~ r2_hidden(A_53,B_31)
      | r1_ordinal1(A_53,k1_ordinal1(B_31))
      | ~ v3_ordinal1(k1_ordinal1(B_31))
      | ~ v3_ordinal1(A_53) ) ),
    inference(resolution,[status(thm)],[c_183,c_91])).

tff(c_423,plain,
    ( ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | k1_ordinal1('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_425,plain,(
    ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_423])).

tff(c_428,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_236,c_425])).

tff(c_433,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_424,c_428])).

tff(c_436,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_433])).

tff(c_439,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_436])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_402,c_439])).

tff(c_442,plain,(
    k1_ordinal1('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_423])).

tff(c_22,plain,(
    ! [B_11] : r2_hidden(B_11,k1_ordinal1(B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_66,plain,(
    ! [B_24,A_25] :
      ( ~ r1_tarski(B_24,A_25)
      | ~ r2_hidden(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_70,plain,(
    ! [B_11] : ~ r1_tarski(k1_ordinal1(B_11),B_11) ),
    inference(resolution,[status(thm)],[c_22,c_66])).

tff(c_264,plain,(
    ! [B_56] :
      ( ~ r1_ordinal1(k1_ordinal1(B_56),B_56)
      | ~ v3_ordinal1(B_56)
      | ~ v3_ordinal1(k1_ordinal1(B_56)) ) ),
    inference(resolution,[status(thm)],[c_247,c_70])).

tff(c_470,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_264])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_442,c_34,c_242,c_470])).

tff(c_529,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_575,plain,
    ( k1_ordinal1('#skF_1') = '#skF_1'
    | ~ r1_ordinal1('#skF_1',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_529,c_401])).

tff(c_576,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_575])).

tff(c_579,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_576])).

tff(c_583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_579])).

tff(c_585,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_575])).

tff(c_533,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_72])).

tff(c_568,plain,
    ( ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_533,c_264])).

tff(c_574,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_568])).

tff(c_587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_574])).

tff(c_588,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_594,plain,(
    ! [B_79,A_80] :
      ( ~ r2_hidden(B_79,A_80)
      | ~ r2_hidden(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_599,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_588,c_594])).

tff(c_722,plain,(
    ! [B_104,A_105] :
      ( r2_hidden(B_104,A_105)
      | r1_ordinal1(A_105,B_104)
      | ~ v3_ordinal1(B_104)
      | ~ v3_ordinal1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_796,plain,(
    ! [A_110,B_111] :
      ( ~ r2_hidden(A_110,B_111)
      | r1_ordinal1(A_110,B_111)
      | ~ v3_ordinal1(B_111)
      | ~ v3_ordinal1(A_110) ) ),
    inference(resolution,[status(thm)],[c_722,c_2])).

tff(c_829,plain,(
    ! [B_112,A_113] :
      ( r1_ordinal1(B_112,A_113)
      | r1_ordinal1(A_113,B_112)
      | ~ v3_ordinal1(B_112)
      | ~ v3_ordinal1(A_113) ) ),
    inference(resolution,[status(thm)],[c_26,c_796])).

tff(c_589,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_839,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_829,c_589])).

tff(c_856,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_839])).

tff(c_864,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_856])).

tff(c_867,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_864])).

tff(c_871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_867])).

tff(c_873,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_856])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | r2_hidden(A_10,B_11)
      | ~ r2_hidden(A_10,k1_ordinal1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_965,plain,(
    ! [B_126,B_125] :
      ( B_126 = B_125
      | r2_hidden(B_126,B_125)
      | r1_ordinal1(k1_ordinal1(B_125),B_126)
      | ~ v3_ordinal1(B_126)
      | ~ v3_ordinal1(k1_ordinal1(B_125)) ) ),
    inference(resolution,[status(thm)],[c_722,c_20])).

tff(c_974,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_965,c_589])).

tff(c_980,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_32,c_974])).

tff(c_981,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_599,c_980])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_593,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_588,c_30])).

tff(c_987,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_593])).

tff(c_992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_987])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.48  
% 3.03/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.48  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 3.03/1.48  
% 3.03/1.48  %Foreground sorts:
% 3.03/1.48  
% 3.03/1.48  
% 3.03/1.48  %Background operators:
% 3.03/1.48  
% 3.03/1.48  
% 3.03/1.48  %Foreground operators:
% 3.03/1.48  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.03/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.03/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.48  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.03/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.03/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.03/1.48  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.03/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.03/1.48  
% 3.03/1.50  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.03/1.50  tff(f_84, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 3.03/1.50  tff(f_69, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 3.03/1.50  tff(f_65, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.03/1.50  tff(f_48, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.03/1.50  tff(f_56, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.03/1.50  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.03/1.50  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.03/1.50  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.03/1.50  tff(c_34, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.03/1.50  tff(c_28, plain, (![A_15]: (v3_ordinal1(k1_ordinal1(A_15)) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.03/1.50  tff(c_32, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.03/1.50  tff(c_183, plain, (![B_52, A_53]: (r2_hidden(B_52, A_53) | r1_ordinal1(A_53, B_52) | ~v3_ordinal1(B_52) | ~v3_ordinal1(A_53))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.03/1.50  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.03/1.50  tff(c_72, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 3.03/1.50  tff(c_36, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.03/1.50  tff(c_79, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_36])).
% 3.03/1.50  tff(c_221, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_183, c_79])).
% 3.03/1.50  tff(c_242, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_221])).
% 3.03/1.50  tff(c_16, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~r1_ordinal1(A_7, B_8) | ~v3_ordinal1(B_8) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.03/1.50  tff(c_247, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~r1_ordinal1(A_55, B_56) | ~v3_ordinal1(B_56) | ~v3_ordinal1(A_55))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.03/1.50  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.03/1.50  tff(c_304, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_ordinal1(A_63, B_62) | ~v3_ordinal1(B_62) | ~v3_ordinal1(A_63))), inference(resolution, [status(thm)], [c_247, c_4])).
% 3.03/1.50  tff(c_372, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_ordinal1(B_73, A_74) | ~r1_ordinal1(A_74, B_73) | ~v3_ordinal1(B_73) | ~v3_ordinal1(A_74))), inference(resolution, [status(thm)], [c_16, c_304])).
% 3.03/1.50  tff(c_384, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_242, c_372])).
% 3.03/1.50  tff(c_396, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_384])).
% 3.03/1.50  tff(c_402, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_396])).
% 3.03/1.50  tff(c_26, plain, (![B_14, A_12]: (r2_hidden(B_14, A_12) | r1_ordinal1(A_12, B_14) | ~v3_ordinal1(B_14) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.03/1.50  tff(c_388, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_372])).
% 3.03/1.50  tff(c_401, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_388])).
% 3.03/1.50  tff(c_415, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_401])).
% 3.03/1.50  tff(c_418, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_415])).
% 3.03/1.50  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_418])).
% 3.03/1.50  tff(c_424, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_401])).
% 3.03/1.50  tff(c_80, plain, (![A_30, B_31]: (~r2_hidden(A_30, B_31) | r2_hidden(A_30, k1_ordinal1(B_31)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.03/1.50  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.03/1.50  tff(c_91, plain, (![B_31, A_30]: (~r2_hidden(k1_ordinal1(B_31), A_30) | ~r2_hidden(A_30, B_31))), inference(resolution, [status(thm)], [c_80, c_2])).
% 3.03/1.50  tff(c_236, plain, (![A_53, B_31]: (~r2_hidden(A_53, B_31) | r1_ordinal1(A_53, k1_ordinal1(B_31)) | ~v3_ordinal1(k1_ordinal1(B_31)) | ~v3_ordinal1(A_53))), inference(resolution, [status(thm)], [c_183, c_91])).
% 3.03/1.50  tff(c_423, plain, (~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | k1_ordinal1('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_401])).
% 3.03/1.50  tff(c_425, plain, (~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_423])).
% 3.03/1.50  tff(c_428, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_236, c_425])).
% 3.03/1.50  tff(c_433, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_424, c_428])).
% 3.03/1.50  tff(c_436, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_433])).
% 3.03/1.50  tff(c_439, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_436])).
% 3.03/1.50  tff(c_441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_402, c_439])).
% 3.03/1.50  tff(c_442, plain, (k1_ordinal1('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_423])).
% 3.03/1.50  tff(c_22, plain, (![B_11]: (r2_hidden(B_11, k1_ordinal1(B_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.03/1.50  tff(c_66, plain, (![B_24, A_25]: (~r1_tarski(B_24, A_25) | ~r2_hidden(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.03/1.50  tff(c_70, plain, (![B_11]: (~r1_tarski(k1_ordinal1(B_11), B_11))), inference(resolution, [status(thm)], [c_22, c_66])).
% 3.03/1.50  tff(c_264, plain, (![B_56]: (~r1_ordinal1(k1_ordinal1(B_56), B_56) | ~v3_ordinal1(B_56) | ~v3_ordinal1(k1_ordinal1(B_56)))), inference(resolution, [status(thm)], [c_247, c_70])).
% 3.03/1.50  tff(c_470, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_442, c_264])).
% 3.03/1.50  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_442, c_34, c_242, c_470])).
% 3.03/1.50  tff(c_529, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_396])).
% 3.03/1.50  tff(c_575, plain, (k1_ordinal1('#skF_1')='#skF_1' | ~r1_ordinal1('#skF_1', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_529, c_401])).
% 3.03/1.50  tff(c_576, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_575])).
% 3.03/1.50  tff(c_579, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_576])).
% 3.03/1.50  tff(c_583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_579])).
% 3.03/1.50  tff(c_585, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_575])).
% 3.03/1.50  tff(c_533, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_529, c_72])).
% 3.03/1.50  tff(c_568, plain, (~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_533, c_264])).
% 3.03/1.50  tff(c_574, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_568])).
% 3.03/1.50  tff(c_587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_585, c_574])).
% 3.03/1.50  tff(c_588, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 3.03/1.50  tff(c_594, plain, (![B_79, A_80]: (~r2_hidden(B_79, A_80) | ~r2_hidden(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.03/1.50  tff(c_599, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_588, c_594])).
% 3.03/1.50  tff(c_722, plain, (![B_104, A_105]: (r2_hidden(B_104, A_105) | r1_ordinal1(A_105, B_104) | ~v3_ordinal1(B_104) | ~v3_ordinal1(A_105))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.03/1.50  tff(c_796, plain, (![A_110, B_111]: (~r2_hidden(A_110, B_111) | r1_ordinal1(A_110, B_111) | ~v3_ordinal1(B_111) | ~v3_ordinal1(A_110))), inference(resolution, [status(thm)], [c_722, c_2])).
% 3.03/1.50  tff(c_829, plain, (![B_112, A_113]: (r1_ordinal1(B_112, A_113) | r1_ordinal1(A_113, B_112) | ~v3_ordinal1(B_112) | ~v3_ordinal1(A_113))), inference(resolution, [status(thm)], [c_26, c_796])).
% 3.03/1.50  tff(c_589, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 3.03/1.50  tff(c_839, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_829, c_589])).
% 3.03/1.50  tff(c_856, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_839])).
% 3.03/1.50  tff(c_864, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_856])).
% 3.03/1.50  tff(c_867, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_864])).
% 3.03/1.50  tff(c_871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_867])).
% 3.03/1.50  tff(c_873, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_856])).
% 3.03/1.50  tff(c_20, plain, (![B_11, A_10]: (B_11=A_10 | r2_hidden(A_10, B_11) | ~r2_hidden(A_10, k1_ordinal1(B_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.03/1.50  tff(c_965, plain, (![B_126, B_125]: (B_126=B_125 | r2_hidden(B_126, B_125) | r1_ordinal1(k1_ordinal1(B_125), B_126) | ~v3_ordinal1(B_126) | ~v3_ordinal1(k1_ordinal1(B_125)))), inference(resolution, [status(thm)], [c_722, c_20])).
% 3.03/1.50  tff(c_974, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_965, c_589])).
% 3.03/1.50  tff(c_980, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_873, c_32, c_974])).
% 3.03/1.50  tff(c_981, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_599, c_980])).
% 3.03/1.50  tff(c_30, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.03/1.50  tff(c_593, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_588, c_30])).
% 3.03/1.50  tff(c_987, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_981, c_593])).
% 3.03/1.50  tff(c_992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_987])).
% 3.03/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.50  
% 3.03/1.50  Inference rules
% 3.03/1.50  ----------------------
% 3.03/1.50  #Ref     : 0
% 3.03/1.50  #Sup     : 181
% 3.03/1.50  #Fact    : 4
% 3.03/1.50  #Define  : 0
% 3.03/1.50  #Split   : 6
% 3.03/1.50  #Chain   : 0
% 3.03/1.50  #Close   : 0
% 3.03/1.50  
% 3.03/1.50  Ordering : KBO
% 3.03/1.50  
% 3.03/1.50  Simplification rules
% 3.03/1.50  ----------------------
% 3.03/1.50  #Subsume      : 30
% 3.03/1.50  #Demod        : 79
% 3.03/1.50  #Tautology    : 39
% 3.03/1.50  #SimpNegUnit  : 2
% 3.03/1.50  #BackRed      : 14
% 3.03/1.50  
% 3.03/1.50  #Partial instantiations: 0
% 3.03/1.50  #Strategies tried      : 1
% 3.03/1.50  
% 3.03/1.50  Timing (in seconds)
% 3.03/1.50  ----------------------
% 3.03/1.50  Preprocessing        : 0.33
% 3.03/1.50  Parsing              : 0.18
% 3.03/1.50  CNF conversion       : 0.02
% 3.03/1.50  Main loop            : 0.39
% 3.03/1.50  Inferencing          : 0.14
% 3.03/1.50  Reduction            : 0.10
% 3.03/1.50  Demodulation         : 0.07
% 3.03/1.50  BG Simplification    : 0.02
% 3.03/1.50  Subsumption          : 0.09
% 3.03/1.50  Abstraction          : 0.02
% 3.03/1.51  MUC search           : 0.00
% 3.03/1.51  Cooper               : 0.00
% 3.03/1.51  Total                : 0.76
% 3.03/1.51  Index Insertion      : 0.00
% 3.03/1.51  Index Deletion       : 0.00
% 3.03/1.51  Index Matching       : 0.00
% 3.03/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
