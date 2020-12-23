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
% DateTime   : Thu Dec  3 09:59:14 EST 2020

% Result     : Theorem 4.86s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 135 expanded)
%              Number of leaves         :   45 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 194 expanded)
%              Number of equality atoms :   42 (  92 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_209,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_133,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_84,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_202,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_156,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_141,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_165,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_110,plain,
    ( k5_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_167,plain,(
    k5_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_112,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_44,plain,(
    ! [A_45] : k2_zfmisc_1(A_45,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_162,plain,(
    ! [A_136,B_137] : v1_relat_1(k2_zfmisc_1(A_136,B_137)) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_164,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_162])).

tff(c_84,plain,(
    ! [A_97,B_98] :
      ( v1_relat_1(k5_relat_1(A_97,B_98))
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_20,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,(
    ! [B_46] : k2_zfmisc_1(k1_xboole_0,B_46) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1138,plain,(
    ! [A_246,B_247] :
      ( r2_hidden(k4_tarski('#skF_4'(A_246,B_247),'#skF_5'(A_246,B_247)),A_246)
      | r1_tarski(A_246,B_247)
      | ~ v1_relat_1(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_22,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_428,plain,(
    ! [B_174,A_175] :
      ( ~ r2_hidden(B_174,A_175)
      | k4_xboole_0(A_175,k1_tarski(B_174)) != A_175 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_437,plain,(
    ! [B_174] : ~ r2_hidden(B_174,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_428])).

tff(c_1142,plain,(
    ! [B_247] :
      ( r1_tarski(k1_xboole_0,B_247)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1138,c_437])).

tff(c_1145,plain,(
    ! [B_247] : r1_tarski(k1_xboole_0,B_247) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_1142])).

tff(c_108,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_106,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_1560,plain,(
    ! [A_280,B_281] :
      ( k1_relat_1(k5_relat_1(A_280,B_281)) = k1_relat_1(A_280)
      | ~ r1_tarski(k2_relat_1(A_280),k1_relat_1(B_281))
      | ~ v1_relat_1(B_281)
      | ~ v1_relat_1(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1578,plain,(
    ! [B_281] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_281)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_281))
      | ~ v1_relat_1(B_281)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_1560])).

tff(c_1586,plain,(
    ! [B_282] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_282)) = k1_xboole_0
      | ~ v1_relat_1(B_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_1145,c_108,c_1578])).

tff(c_90,plain,(
    ! [A_102] :
      ( k3_xboole_0(A_102,k2_zfmisc_1(k1_relat_1(A_102),k2_relat_1(A_102))) = A_102
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1601,plain,(
    ! [B_282] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_282),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_282)))) = k5_relat_1(k1_xboole_0,B_282)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_282))
      | ~ v1_relat_1(B_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1586,c_90])).

tff(c_1620,plain,(
    ! [B_283] :
      ( k5_relat_1(k1_xboole_0,B_283) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_283))
      | ~ v1_relat_1(B_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_46,c_1601])).

tff(c_1627,plain,(
    ! [B_98] :
      ( k5_relat_1(k1_xboole_0,B_98) = k1_xboole_0
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_84,c_1620])).

tff(c_1633,plain,(
    ! [B_284] :
      ( k5_relat_1(k1_xboole_0,B_284) = k1_xboole_0
      | ~ v1_relat_1(B_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_1627])).

tff(c_1648,plain,(
    k5_relat_1(k1_xboole_0,'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_112,c_1633])).

tff(c_1657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_1648])).

tff(c_1658,plain,(
    k5_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_2736,plain,(
    ! [A_400,B_401] :
      ( r2_hidden(k4_tarski('#skF_4'(A_400,B_401),'#skF_5'(A_400,B_401)),A_400)
      | r1_tarski(A_400,B_401)
      | ~ v1_relat_1(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1969,plain,(
    ! [B_328,A_329] :
      ( ~ r2_hidden(B_328,A_329)
      | k4_xboole_0(A_329,k1_tarski(B_328)) != A_329 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1982,plain,(
    ! [B_328] : ~ r2_hidden(B_328,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1969])).

tff(c_2740,plain,(
    ! [B_401] :
      ( r1_tarski(k1_xboole_0,B_401)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2736,c_1982])).

tff(c_2743,plain,(
    ! [B_401] : r1_tarski(k1_xboole_0,B_401) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_2740])).

tff(c_3374,plain,(
    ! [B_432,A_433] :
      ( k2_relat_1(k5_relat_1(B_432,A_433)) = k2_relat_1(A_433)
      | ~ r1_tarski(k1_relat_1(A_433),k2_relat_1(B_432))
      | ~ v1_relat_1(B_432)
      | ~ v1_relat_1(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3386,plain,(
    ! [B_432] :
      ( k2_relat_1(k5_relat_1(B_432,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_432))
      | ~ v1_relat_1(B_432)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_3374])).

tff(c_3395,plain,(
    ! [B_434] :
      ( k2_relat_1(k5_relat_1(B_434,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_2743,c_106,c_3386])).

tff(c_3407,plain,(
    ! [B_434] :
      ( k3_xboole_0(k5_relat_1(B_434,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_434,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_434,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_434,k1_xboole_0))
      | ~ v1_relat_1(B_434) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3395,c_90])).

tff(c_3419,plain,(
    ! [B_435] :
      ( k5_relat_1(B_435,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_435,k1_xboole_0))
      | ~ v1_relat_1(B_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_44,c_3407])).

tff(c_3423,plain,(
    ! [A_97] :
      ( k5_relat_1(A_97,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_84,c_3419])).

tff(c_3427,plain,(
    ! [A_436] :
      ( k5_relat_1(A_436,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_436) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_3423])).

tff(c_3442,plain,(
    k5_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_112,c_3427])).

tff(c_3450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1658,c_3442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:30:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.86/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.87  
% 4.86/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.87  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 4.86/1.87  
% 4.86/1.87  %Foreground sorts:
% 4.86/1.87  
% 4.86/1.87  
% 4.86/1.87  %Background operators:
% 4.86/1.87  
% 4.86/1.87  
% 4.86/1.87  %Foreground operators:
% 4.86/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.86/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.86/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.86/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.86/1.87  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.86/1.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.86/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.86/1.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.86/1.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.86/1.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.86/1.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.86/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.86/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.86/1.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.86/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.86/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.86/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.86/1.87  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.86/1.87  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.86/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.86/1.87  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.86/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.86/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.86/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.86/1.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.86/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.86/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.86/1.87  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.86/1.87  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.86/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.86/1.87  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.86/1.87  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.86/1.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.86/1.87  
% 4.86/1.89  tff(f_209, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 4.86/1.89  tff(f_73, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.86/1.89  tff(f_133, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.86/1.89  tff(f_131, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.86/1.89  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.86/1.89  tff(f_121, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 4.86/1.89  tff(f_49, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.86/1.89  tff(f_84, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.86/1.89  tff(f_202, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.86/1.89  tff(f_156, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 4.86/1.89  tff(f_141, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 4.86/1.89  tff(f_165, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 4.86/1.89  tff(c_110, plain, (k5_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.86/1.89  tff(c_167, plain, (k5_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_110])).
% 4.86/1.89  tff(c_112, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.86/1.89  tff(c_44, plain, (![A_45]: (k2_zfmisc_1(A_45, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.86/1.89  tff(c_162, plain, (![A_136, B_137]: (v1_relat_1(k2_zfmisc_1(A_136, B_137)))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.86/1.89  tff(c_164, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_162])).
% 4.86/1.89  tff(c_84, plain, (![A_97, B_98]: (v1_relat_1(k5_relat_1(A_97, B_98)) | ~v1_relat_1(B_98) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.86/1.89  tff(c_20, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.86/1.89  tff(c_46, plain, (![B_46]: (k2_zfmisc_1(k1_xboole_0, B_46)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.86/1.89  tff(c_1138, plain, (![A_246, B_247]: (r2_hidden(k4_tarski('#skF_4'(A_246, B_247), '#skF_5'(A_246, B_247)), A_246) | r1_tarski(A_246, B_247) | ~v1_relat_1(A_246))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.86/1.89  tff(c_22, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.86/1.89  tff(c_428, plain, (![B_174, A_175]: (~r2_hidden(B_174, A_175) | k4_xboole_0(A_175, k1_tarski(B_174))!=A_175)), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.86/1.89  tff(c_437, plain, (![B_174]: (~r2_hidden(B_174, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_428])).
% 4.86/1.89  tff(c_1142, plain, (![B_247]: (r1_tarski(k1_xboole_0, B_247) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1138, c_437])).
% 4.86/1.89  tff(c_1145, plain, (![B_247]: (r1_tarski(k1_xboole_0, B_247))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_1142])).
% 4.86/1.89  tff(c_108, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.86/1.89  tff(c_106, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.86/1.89  tff(c_1560, plain, (![A_280, B_281]: (k1_relat_1(k5_relat_1(A_280, B_281))=k1_relat_1(A_280) | ~r1_tarski(k2_relat_1(A_280), k1_relat_1(B_281)) | ~v1_relat_1(B_281) | ~v1_relat_1(A_280))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.86/1.89  tff(c_1578, plain, (![B_281]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_281))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_281)) | ~v1_relat_1(B_281) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_106, c_1560])).
% 4.86/1.89  tff(c_1586, plain, (![B_282]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_282))=k1_xboole_0 | ~v1_relat_1(B_282))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_1145, c_108, c_1578])).
% 4.86/1.89  tff(c_90, plain, (![A_102]: (k3_xboole_0(A_102, k2_zfmisc_1(k1_relat_1(A_102), k2_relat_1(A_102)))=A_102 | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.86/1.89  tff(c_1601, plain, (![B_282]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_282), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_282))))=k5_relat_1(k1_xboole_0, B_282) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_282)) | ~v1_relat_1(B_282))), inference(superposition, [status(thm), theory('equality')], [c_1586, c_90])).
% 4.86/1.89  tff(c_1620, plain, (![B_283]: (k5_relat_1(k1_xboole_0, B_283)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_283)) | ~v1_relat_1(B_283))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_46, c_1601])).
% 4.86/1.89  tff(c_1627, plain, (![B_98]: (k5_relat_1(k1_xboole_0, B_98)=k1_xboole_0 | ~v1_relat_1(B_98) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_84, c_1620])).
% 4.86/1.89  tff(c_1633, plain, (![B_284]: (k5_relat_1(k1_xboole_0, B_284)=k1_xboole_0 | ~v1_relat_1(B_284))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_1627])).
% 4.86/1.89  tff(c_1648, plain, (k5_relat_1(k1_xboole_0, '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_112, c_1633])).
% 4.86/1.89  tff(c_1657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_1648])).
% 4.86/1.89  tff(c_1658, plain, (k5_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_110])).
% 4.86/1.89  tff(c_2736, plain, (![A_400, B_401]: (r2_hidden(k4_tarski('#skF_4'(A_400, B_401), '#skF_5'(A_400, B_401)), A_400) | r1_tarski(A_400, B_401) | ~v1_relat_1(A_400))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.86/1.89  tff(c_1969, plain, (![B_328, A_329]: (~r2_hidden(B_328, A_329) | k4_xboole_0(A_329, k1_tarski(B_328))!=A_329)), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.86/1.89  tff(c_1982, plain, (![B_328]: (~r2_hidden(B_328, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1969])).
% 4.86/1.89  tff(c_2740, plain, (![B_401]: (r1_tarski(k1_xboole_0, B_401) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2736, c_1982])).
% 4.86/1.89  tff(c_2743, plain, (![B_401]: (r1_tarski(k1_xboole_0, B_401))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_2740])).
% 4.86/1.89  tff(c_3374, plain, (![B_432, A_433]: (k2_relat_1(k5_relat_1(B_432, A_433))=k2_relat_1(A_433) | ~r1_tarski(k1_relat_1(A_433), k2_relat_1(B_432)) | ~v1_relat_1(B_432) | ~v1_relat_1(A_433))), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.86/1.89  tff(c_3386, plain, (![B_432]: (k2_relat_1(k5_relat_1(B_432, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_432)) | ~v1_relat_1(B_432) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_108, c_3374])).
% 4.86/1.89  tff(c_3395, plain, (![B_434]: (k2_relat_1(k5_relat_1(B_434, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_434))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_2743, c_106, c_3386])).
% 4.86/1.89  tff(c_3407, plain, (![B_434]: (k3_xboole_0(k5_relat_1(B_434, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_434, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_434, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_434, k1_xboole_0)) | ~v1_relat_1(B_434))), inference(superposition, [status(thm), theory('equality')], [c_3395, c_90])).
% 4.86/1.89  tff(c_3419, plain, (![B_435]: (k5_relat_1(B_435, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_435, k1_xboole_0)) | ~v1_relat_1(B_435))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_44, c_3407])).
% 4.86/1.89  tff(c_3423, plain, (![A_97]: (k5_relat_1(A_97, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_84, c_3419])).
% 4.86/1.89  tff(c_3427, plain, (![A_436]: (k5_relat_1(A_436, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_436))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_3423])).
% 4.86/1.89  tff(c_3442, plain, (k5_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_112, c_3427])).
% 4.86/1.89  tff(c_3450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1658, c_3442])).
% 4.86/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.89  
% 4.86/1.89  Inference rules
% 4.86/1.89  ----------------------
% 4.86/1.89  #Ref     : 2
% 4.86/1.89  #Sup     : 766
% 4.86/1.89  #Fact    : 0
% 4.86/1.89  #Define  : 0
% 4.86/1.89  #Split   : 1
% 4.86/1.89  #Chain   : 0
% 4.86/1.89  #Close   : 0
% 4.86/1.89  
% 4.86/1.89  Ordering : KBO
% 4.86/1.89  
% 4.86/1.89  Simplification rules
% 4.86/1.89  ----------------------
% 4.86/1.89  #Subsume      : 17
% 4.86/1.89  #Demod        : 630
% 4.86/1.89  #Tautology    : 498
% 4.86/1.89  #SimpNegUnit  : 8
% 4.86/1.89  #BackRed      : 8
% 4.86/1.89  
% 4.86/1.89  #Partial instantiations: 0
% 4.86/1.89  #Strategies tried      : 1
% 4.86/1.89  
% 4.86/1.89  Timing (in seconds)
% 4.86/1.89  ----------------------
% 4.86/1.89  Preprocessing        : 0.40
% 4.86/1.89  Parsing              : 0.21
% 4.86/1.89  CNF conversion       : 0.03
% 4.86/1.89  Main loop            : 0.68
% 4.86/1.89  Inferencing          : 0.24
% 4.86/1.89  Reduction            : 0.25
% 4.86/1.89  Demodulation         : 0.19
% 4.86/1.89  BG Simplification    : 0.04
% 4.86/1.89  Subsumption          : 0.10
% 4.86/1.89  Abstraction          : 0.04
% 4.86/1.89  MUC search           : 0.00
% 4.86/1.89  Cooper               : 0.00
% 4.86/1.89  Total                : 1.11
% 4.86/1.89  Index Insertion      : 0.00
% 4.86/1.89  Index Deletion       : 0.00
% 4.86/1.89  Index Matching       : 0.00
% 4.86/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
