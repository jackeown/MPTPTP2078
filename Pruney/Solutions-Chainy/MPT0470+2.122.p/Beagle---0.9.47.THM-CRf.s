%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:18 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 115 expanded)
%              Number of leaves         :   36 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 186 expanded)
%              Number of equality atoms :   29 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_102,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_42,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_71,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_26,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),A_21)
      | v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_88,plain,(
    ! [A_60,B_61] :
      ( ~ r2_hidden(A_60,B_61)
      | ~ r1_xboole_0(k1_tarski(A_60),B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    ! [A_63] : ~ r2_hidden(A_63,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_105,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_100])).

tff(c_28,plain,(
    ! [A_39,B_40] :
      ( v1_relat_1(k5_relat_1(A_39,B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_195,plain,(
    ! [A_90,B_91] :
      ( k1_relat_1(k5_relat_1(A_90,B_91)) = k1_relat_1(A_90)
      | ~ r1_tarski(k2_relat_1(A_90),k1_relat_1(B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_204,plain,(
    ! [B_91] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_91)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_195])).

tff(c_262,plain,(
    ! [B_93] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_93)) = k1_xboole_0
      | ~ v1_relat_1(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_6,c_40,c_204])).

tff(c_30,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(k1_relat_1(A_41))
      | ~ v1_relat_1(A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_274,plain,(
    ! [B_93] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_93))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_93))
      | ~ v1_relat_1(B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_30])).

tff(c_289,plain,(
    ! [B_94] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_94))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_94))
      | ~ v1_relat_1(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_274])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_310,plain,(
    ! [B_96] :
      ( k5_relat_1(k1_xboole_0,B_96) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_96))
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_289,c_4])).

tff(c_317,plain,(
    ! [B_40] :
      ( k5_relat_1(k1_xboole_0,B_40) = k1_xboole_0
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_310])).

tff(c_323,plain,(
    ! [B_97] :
      ( k5_relat_1(k1_xboole_0,B_97) = k1_xboole_0
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_317])).

tff(c_332,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_323])).

tff(c_339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_332])).

tff(c_340,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_346,plain,(
    ! [A_98,B_99] :
      ( ~ r2_hidden(A_98,B_99)
      | ~ r1_xboole_0(k1_tarski(A_98),B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_352,plain,(
    ! [A_100] : ~ r2_hidden(A_100,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_346])).

tff(c_357,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_352])).

tff(c_444,plain,(
    ! [B_131,A_132] :
      ( k2_relat_1(k5_relat_1(B_131,A_132)) = k2_relat_1(A_132)
      | ~ r1_tarski(k1_relat_1(A_132),k2_relat_1(B_131))
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_447,plain,(
    ! [B_131] :
      ( k2_relat_1(k5_relat_1(B_131,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_131))
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_444])).

tff(c_482,plain,(
    ! [B_134] :
      ( k2_relat_1(k5_relat_1(B_134,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_6,c_38,c_447])).

tff(c_32,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(k2_relat_1(A_42))
      | ~ v1_relat_1(A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_494,plain,(
    ! [B_134] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_134,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_134,k1_xboole_0))
      | ~ v1_relat_1(B_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_32])).

tff(c_565,plain,(
    ! [B_138] :
      ( ~ v1_relat_1(k5_relat_1(B_138,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_138,k1_xboole_0))
      | ~ v1_relat_1(B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_494])).

tff(c_575,plain,(
    ! [B_139] :
      ( k5_relat_1(B_139,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_139,k1_xboole_0))
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_565,c_4])).

tff(c_582,plain,(
    ! [A_39] :
      ( k5_relat_1(A_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_28,c_575])).

tff(c_588,plain,(
    ! [A_140] :
      ( k5_relat_1(A_140,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_582])).

tff(c_597,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_588])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:20:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.47  
% 2.42/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.77/1.47  
% 2.77/1.47  %Foreground sorts:
% 2.77/1.47  
% 2.77/1.47  
% 2.77/1.47  %Background operators:
% 2.77/1.47  
% 2.77/1.47  
% 2.77/1.47  %Foreground operators:
% 2.77/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.77/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.77/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.77/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.77/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.47  
% 2.79/1.49  tff(f_109, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.79/1.49  tff(f_59, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.79/1.49  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.79/1.49  tff(f_49, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.79/1.49  tff(f_65, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.79/1.49  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.79/1.49  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.79/1.49  tff(f_102, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.79/1.49  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.79/1.49  tff(f_73, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.79/1.49  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.79/1.49  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.79/1.49  tff(f_81, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.79/1.49  tff(c_42, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.79/1.49  tff(c_71, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.79/1.49  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.79/1.49  tff(c_26, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.49  tff(c_8, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.79/1.49  tff(c_88, plain, (![A_60, B_61]: (~r2_hidden(A_60, B_61) | ~r1_xboole_0(k1_tarski(A_60), B_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.79/1.49  tff(c_100, plain, (![A_63]: (~r2_hidden(A_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_88])).
% 2.79/1.49  tff(c_105, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_100])).
% 2.79/1.49  tff(c_28, plain, (![A_39, B_40]: (v1_relat_1(k5_relat_1(A_39, B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.79/1.49  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.79/1.49  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.49  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.79/1.49  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.79/1.49  tff(c_195, plain, (![A_90, B_91]: (k1_relat_1(k5_relat_1(A_90, B_91))=k1_relat_1(A_90) | ~r1_tarski(k2_relat_1(A_90), k1_relat_1(B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.79/1.49  tff(c_204, plain, (![B_91]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_91))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_195])).
% 2.79/1.49  tff(c_262, plain, (![B_93]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_93))=k1_xboole_0 | ~v1_relat_1(B_93))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_6, c_40, c_204])).
% 2.79/1.49  tff(c_30, plain, (![A_41]: (~v1_xboole_0(k1_relat_1(A_41)) | ~v1_relat_1(A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.79/1.49  tff(c_274, plain, (![B_93]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_93)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_93)) | ~v1_relat_1(B_93))), inference(superposition, [status(thm), theory('equality')], [c_262, c_30])).
% 2.79/1.49  tff(c_289, plain, (![B_94]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_94)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_94)) | ~v1_relat_1(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_274])).
% 2.79/1.49  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.79/1.49  tff(c_310, plain, (![B_96]: (k5_relat_1(k1_xboole_0, B_96)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_96)) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_289, c_4])).
% 2.79/1.49  tff(c_317, plain, (![B_40]: (k5_relat_1(k1_xboole_0, B_40)=k1_xboole_0 | ~v1_relat_1(B_40) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_310])).
% 2.79/1.49  tff(c_323, plain, (![B_97]: (k5_relat_1(k1_xboole_0, B_97)=k1_xboole_0 | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_317])).
% 2.79/1.49  tff(c_332, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_323])).
% 2.79/1.49  tff(c_339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_332])).
% 2.79/1.49  tff(c_340, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.79/1.49  tff(c_346, plain, (![A_98, B_99]: (~r2_hidden(A_98, B_99) | ~r1_xboole_0(k1_tarski(A_98), B_99))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.79/1.49  tff(c_352, plain, (![A_100]: (~r2_hidden(A_100, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_346])).
% 2.79/1.49  tff(c_357, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_352])).
% 2.79/1.49  tff(c_444, plain, (![B_131, A_132]: (k2_relat_1(k5_relat_1(B_131, A_132))=k2_relat_1(A_132) | ~r1_tarski(k1_relat_1(A_132), k2_relat_1(B_131)) | ~v1_relat_1(B_131) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.79/1.49  tff(c_447, plain, (![B_131]: (k2_relat_1(k5_relat_1(B_131, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_131)) | ~v1_relat_1(B_131) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_444])).
% 2.79/1.49  tff(c_482, plain, (![B_134]: (k2_relat_1(k5_relat_1(B_134, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_134))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_6, c_38, c_447])).
% 2.79/1.49  tff(c_32, plain, (![A_42]: (~v1_xboole_0(k2_relat_1(A_42)) | ~v1_relat_1(A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.79/1.49  tff(c_494, plain, (![B_134]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_134, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_134, k1_xboole_0)) | ~v1_relat_1(B_134))), inference(superposition, [status(thm), theory('equality')], [c_482, c_32])).
% 2.79/1.49  tff(c_565, plain, (![B_138]: (~v1_relat_1(k5_relat_1(B_138, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_138, k1_xboole_0)) | ~v1_relat_1(B_138))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_494])).
% 2.79/1.49  tff(c_575, plain, (![B_139]: (k5_relat_1(B_139, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_139, k1_xboole_0)) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_565, c_4])).
% 2.79/1.49  tff(c_582, plain, (![A_39]: (k5_relat_1(A_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_28, c_575])).
% 2.79/1.49  tff(c_588, plain, (![A_140]: (k5_relat_1(A_140, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_582])).
% 2.79/1.49  tff(c_597, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_588])).
% 2.79/1.49  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_340, c_597])).
% 2.79/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.49  
% 2.79/1.49  Inference rules
% 2.79/1.49  ----------------------
% 2.79/1.49  #Ref     : 2
% 2.79/1.49  #Sup     : 116
% 2.79/1.49  #Fact    : 0
% 2.79/1.49  #Define  : 0
% 2.79/1.49  #Split   : 1
% 2.79/1.49  #Chain   : 0
% 2.79/1.49  #Close   : 0
% 2.79/1.49  
% 2.79/1.49  Ordering : KBO
% 2.79/1.49  
% 2.79/1.49  Simplification rules
% 2.79/1.49  ----------------------
% 2.79/1.49  #Subsume      : 4
% 2.79/1.49  #Demod        : 104
% 2.79/1.49  #Tautology    : 72
% 2.79/1.49  #SimpNegUnit  : 2
% 2.79/1.49  #BackRed      : 0
% 2.79/1.49  
% 2.79/1.49  #Partial instantiations: 0
% 2.79/1.49  #Strategies tried      : 1
% 2.79/1.49  
% 2.79/1.49  Timing (in seconds)
% 2.79/1.49  ----------------------
% 2.79/1.49  Preprocessing        : 0.37
% 2.79/1.49  Parsing              : 0.20
% 2.79/1.49  CNF conversion       : 0.02
% 2.79/1.49  Main loop            : 0.29
% 2.79/1.49  Inferencing          : 0.12
% 2.79/1.49  Reduction            : 0.09
% 2.79/1.49  Demodulation         : 0.06
% 2.79/1.49  BG Simplification    : 0.02
% 2.79/1.49  Subsumption          : 0.05
% 2.79/1.49  Abstraction          : 0.02
% 2.79/1.49  MUC search           : 0.00
% 2.79/1.49  Cooper               : 0.00
% 2.79/1.49  Total                : 0.70
% 2.79/1.49  Index Insertion      : 0.00
% 2.79/1.49  Index Deletion       : 0.00
% 2.79/1.49  Index Matching       : 0.00
% 2.79/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
