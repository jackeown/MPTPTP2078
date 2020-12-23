%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:48 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 130 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 206 expanded)
%              Number of equality atoms :   33 (  66 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_533,plain,(
    ! [B_127,A_128] :
      ( r1_xboole_0(k1_relat_1(B_127),A_128)
      | k7_relat_1(B_127,A_128) != k1_xboole_0
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_60,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_91,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_234,plain,(
    ! [B_89,A_90] :
      ( k7_relat_1(B_89,A_90) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_89),A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_240,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_234])).

tff(c_248,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_240])).

tff(c_42,plain,(
    ! [B_46,A_45] :
      ( k2_relat_1(k7_relat_1(B_46,A_45)) = k9_relat_1(B_46,A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_253,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_42])).

tff(c_263,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_253])).

tff(c_54,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k9_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_125,plain,(
    k9_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_54])).

tff(c_278,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_125])).

tff(c_77,plain,(
    ! [A_55] :
      ( k9_relat_1(A_55,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_81,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_77])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_301,plain,(
    ! [B_95] :
      ( k7_relat_1(B_95,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_10,c_234])).

tff(c_313,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_301])).

tff(c_317,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_42])).

tff(c_327,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_81,c_317])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_327])).

tff(c_331,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_542,plain,
    ( k7_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_533,c_331])).

tff(c_551,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_542])).

tff(c_40,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k7_relat_1(A_43,B_44))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_494,plain,(
    ! [C_121,D_122,A_123,B_124] :
      ( ~ r1_xboole_0(C_121,D_122)
      | r1_xboole_0(k2_zfmisc_1(A_123,C_121),k2_zfmisc_1(B_124,D_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_520,plain,(
    ! [B_125,D_126] :
      ( k2_zfmisc_1(B_125,D_126) = k1_xboole_0
      | ~ r1_xboole_0(D_126,D_126) ) ),
    inference(resolution,[status(thm)],[c_494,c_14])).

tff(c_532,plain,(
    ! [B_125] : k2_zfmisc_1(B_125,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_520])).

tff(c_330,plain,(
    k9_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_417,plain,(
    ! [A_112] :
      ( r1_tarski(A_112,k2_zfmisc_1(k1_relat_1(A_112),k2_relat_1(A_112)))
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1376,plain,(
    ! [B_294,A_295] :
      ( r1_tarski(k7_relat_1(B_294,A_295),k2_zfmisc_1(k1_relat_1(k7_relat_1(B_294,A_295)),k9_relat_1(B_294,A_295)))
      | ~ v1_relat_1(k7_relat_1(B_294,A_295))
      | ~ v1_relat_1(B_294) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_417])).

tff(c_1405,plain,
    ( r1_tarski(k7_relat_1('#skF_3','#skF_2'),k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),k1_xboole_0))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_1376])).

tff(c_1423,plain,
    ( r1_tarski(k7_relat_1('#skF_3','#skF_2'),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_532,c_1405])).

tff(c_1426,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1423])).

tff(c_1429,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1426])).

tff(c_1433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1429])).

tff(c_1434,plain,(
    r1_tarski(k7_relat_1('#skF_3','#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1423])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_361,plain,(
    ! [B_101,A_102] :
      ( B_101 = A_102
      | ~ r1_tarski(B_101,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_370,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_361])).

tff(c_1446,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1434,c_370])).

tff(c_1452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_1446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.62  
% 3.59/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.59/1.62  
% 3.59/1.62  %Foreground sorts:
% 3.59/1.62  
% 3.59/1.62  
% 3.59/1.62  %Background operators:
% 3.59/1.62  
% 3.59/1.62  
% 3.59/1.62  %Foreground operators:
% 3.59/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.59/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.59/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.59/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.59/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.59/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.59/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.59/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.59/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.59/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.59/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.59/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.59/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.59/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.59/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.59/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.59/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.59/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.59/1.62  
% 3.59/1.64  tff(f_107, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 3.59/1.64  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 3.59/1.64  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.59/1.64  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 3.59/1.64  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.59/1.64  tff(f_82, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.59/1.64  tff(f_65, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 3.59/1.64  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.59/1.64  tff(f_94, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.59/1.64  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.59/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.59/1.64  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.59/1.64  tff(c_533, plain, (![B_127, A_128]: (r1_xboole_0(k1_relat_1(B_127), A_128) | k7_relat_1(B_127, A_128)!=k1_xboole_0 | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.59/1.64  tff(c_60, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.59/1.64  tff(c_91, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 3.59/1.64  tff(c_234, plain, (![B_89, A_90]: (k7_relat_1(B_89, A_90)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_89), A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.59/1.64  tff(c_240, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_91, c_234])).
% 3.59/1.64  tff(c_248, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_240])).
% 3.59/1.64  tff(c_42, plain, (![B_46, A_45]: (k2_relat_1(k7_relat_1(B_46, A_45))=k9_relat_1(B_46, A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.64  tff(c_253, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_248, c_42])).
% 3.59/1.64  tff(c_263, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_253])).
% 3.59/1.64  tff(c_54, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k9_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.59/1.64  tff(c_125, plain, (k9_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_91, c_54])).
% 3.59/1.64  tff(c_278, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_263, c_125])).
% 3.59/1.64  tff(c_77, plain, (![A_55]: (k9_relat_1(A_55, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.59/1.64  tff(c_81, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_77])).
% 3.59/1.64  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.59/1.64  tff(c_301, plain, (![B_95]: (k7_relat_1(B_95, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_10, c_234])).
% 3.59/1.64  tff(c_313, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_301])).
% 3.59/1.64  tff(c_317, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_313, c_42])).
% 3.59/1.64  tff(c_327, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_81, c_317])).
% 3.59/1.64  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_327])).
% 3.59/1.64  tff(c_331, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 3.59/1.64  tff(c_542, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_533, c_331])).
% 3.59/1.64  tff(c_551, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_542])).
% 3.59/1.64  tff(c_40, plain, (![A_43, B_44]: (v1_relat_1(k7_relat_1(A_43, B_44)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.59/1.64  tff(c_494, plain, (![C_121, D_122, A_123, B_124]: (~r1_xboole_0(C_121, D_122) | r1_xboole_0(k2_zfmisc_1(A_123, C_121), k2_zfmisc_1(B_124, D_122)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.59/1.64  tff(c_14, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.59/1.64  tff(c_520, plain, (![B_125, D_126]: (k2_zfmisc_1(B_125, D_126)=k1_xboole_0 | ~r1_xboole_0(D_126, D_126))), inference(resolution, [status(thm)], [c_494, c_14])).
% 3.59/1.64  tff(c_532, plain, (![B_125]: (k2_zfmisc_1(B_125, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_520])).
% 3.59/1.64  tff(c_330, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.59/1.64  tff(c_417, plain, (![A_112]: (r1_tarski(A_112, k2_zfmisc_1(k1_relat_1(A_112), k2_relat_1(A_112))) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.59/1.64  tff(c_1376, plain, (![B_294, A_295]: (r1_tarski(k7_relat_1(B_294, A_295), k2_zfmisc_1(k1_relat_1(k7_relat_1(B_294, A_295)), k9_relat_1(B_294, A_295))) | ~v1_relat_1(k7_relat_1(B_294, A_295)) | ~v1_relat_1(B_294))), inference(superposition, [status(thm), theory('equality')], [c_42, c_417])).
% 3.59/1.64  tff(c_1405, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), k1_xboole_0)) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_330, c_1376])).
% 3.59/1.64  tff(c_1423, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_532, c_1405])).
% 3.59/1.64  tff(c_1426, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1423])).
% 3.59/1.64  tff(c_1429, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1426])).
% 3.59/1.64  tff(c_1433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1429])).
% 3.59/1.64  tff(c_1434, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1423])).
% 3.59/1.64  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.59/1.64  tff(c_361, plain, (![B_101, A_102]: (B_101=A_102 | ~r1_tarski(B_101, A_102) | ~r1_tarski(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.59/1.64  tff(c_370, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_361])).
% 3.59/1.64  tff(c_1446, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1434, c_370])).
% 3.59/1.64  tff(c_1452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_1446])).
% 3.59/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.64  
% 3.59/1.64  Inference rules
% 3.59/1.64  ----------------------
% 3.59/1.64  #Ref     : 0
% 3.59/1.64  #Sup     : 306
% 3.59/1.64  #Fact    : 0
% 3.59/1.64  #Define  : 0
% 3.59/1.64  #Split   : 3
% 3.59/1.64  #Chain   : 0
% 3.59/1.64  #Close   : 0
% 3.59/1.64  
% 3.59/1.64  Ordering : KBO
% 3.59/1.64  
% 3.59/1.64  Simplification rules
% 3.59/1.64  ----------------------
% 3.59/1.64  #Subsume      : 2
% 3.59/1.64  #Demod        : 297
% 3.59/1.64  #Tautology    : 166
% 3.59/1.64  #SimpNegUnit  : 2
% 3.59/1.64  #BackRed      : 1
% 3.59/1.64  
% 3.59/1.64  #Partial instantiations: 0
% 3.59/1.64  #Strategies tried      : 1
% 3.59/1.64  
% 3.59/1.64  Timing (in seconds)
% 3.59/1.64  ----------------------
% 3.59/1.64  Preprocessing        : 0.36
% 3.59/1.64  Parsing              : 0.19
% 3.59/1.64  CNF conversion       : 0.02
% 3.59/1.64  Main loop            : 0.45
% 3.59/1.64  Inferencing          : 0.16
% 3.59/1.64  Reduction            : 0.13
% 3.59/1.64  Demodulation         : 0.10
% 3.59/1.64  BG Simplification    : 0.02
% 3.59/1.64  Subsumption          : 0.10
% 3.59/1.64  Abstraction          : 0.02
% 3.59/1.64  MUC search           : 0.00
% 3.59/1.64  Cooper               : 0.00
% 3.59/1.64  Total                : 0.84
% 3.59/1.64  Index Insertion      : 0.00
% 3.59/1.64  Index Deletion       : 0.00
% 3.59/1.64  Index Matching       : 0.00
% 3.59/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
