%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:19 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 129 expanded)
%              Number of leaves         :   39 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 198 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_106,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_50,plain,
    ( k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_93,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_2'(A_40),A_40)
      | v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,k3_xboole_0(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    ! [A_6,C_86] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_86,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_125])).

tff(c_136,plain,(
    ! [C_87] : ~ r2_hidden(C_87,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_132])).

tff(c_141,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_136])).

tff(c_38,plain,(
    ! [A_58,B_59] :
      ( v1_relat_1(k5_relat_1(A_58,B_59))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [B_37] : k2_zfmisc_1(k1_xboole_0,B_37) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_426,plain,(
    ! [A_131,B_132] :
      ( k1_relat_1(k5_relat_1(A_131,B_132)) = k1_relat_1(A_131)
      | ~ r1_tarski(k2_relat_1(A_131),k1_relat_1(B_132))
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_435,plain,(
    ! [B_132] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_132)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_132))
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_426])).

tff(c_442,plain,(
    ! [B_133] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_133)) = k1_xboole_0
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_8,c_48,c_435])).

tff(c_40,plain,(
    ! [A_60] :
      ( k3_xboole_0(A_60,k2_zfmisc_1(k1_relat_1(A_60),k2_relat_1(A_60))) = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_456,plain,(
    ! [B_133] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_133),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_133)))) = k5_relat_1(k1_xboole_0,B_133)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_133))
      | ~ v1_relat_1(B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_40])).

tff(c_472,plain,(
    ! [B_134] :
      ( k5_relat_1(k1_xboole_0,B_134) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_134))
      | ~ v1_relat_1(B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28,c_456])).

tff(c_479,plain,(
    ! [B_59] :
      ( k5_relat_1(k1_xboole_0,B_59) = k1_xboole_0
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_472])).

tff(c_485,plain,(
    ! [B_135] :
      ( k5_relat_1(k1_xboole_0,B_135) = k1_xboole_0
      | ~ v1_relat_1(B_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_479])).

tff(c_497,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_485])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_497])).

tff(c_506,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_548,plain,(
    ! [A_147,B_148,C_149] :
      ( ~ r1_xboole_0(A_147,B_148)
      | ~ r2_hidden(C_149,k3_xboole_0(A_147,B_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_555,plain,(
    ! [A_6,C_149] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_149,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_548])).

tff(c_559,plain,(
    ! [C_150] : ~ r2_hidden(C_150,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_555])).

tff(c_564,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_559])).

tff(c_26,plain,(
    ! [A_36] : k2_zfmisc_1(A_36,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_665,plain,(
    ! [B_177,A_178] :
      ( k2_relat_1(k5_relat_1(B_177,A_178)) = k2_relat_1(A_178)
      | ~ r1_tarski(k1_relat_1(A_178),k2_relat_1(B_177))
      | ~ v1_relat_1(B_177)
      | ~ v1_relat_1(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_668,plain,(
    ! [B_177] :
      ( k2_relat_1(k5_relat_1(B_177,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_177))
      | ~ v1_relat_1(B_177)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_665])).

tff(c_676,plain,(
    ! [B_179] :
      ( k2_relat_1(k5_relat_1(B_179,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_8,c_46,c_668])).

tff(c_687,plain,(
    ! [B_179] :
      ( k3_xboole_0(k5_relat_1(B_179,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_179,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_179,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_179,k1_xboole_0))
      | ~ v1_relat_1(B_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_40])).

tff(c_705,plain,(
    ! [B_186] :
      ( k5_relat_1(B_186,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_186,k1_xboole_0))
      | ~ v1_relat_1(B_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26,c_687])).

tff(c_709,plain,(
    ! [A_58] :
      ( k5_relat_1(A_58,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_38,c_705])).

tff(c_713,plain,(
    ! [A_187] :
      ( k5_relat_1(A_187,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_709])).

tff(c_725,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_713])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_506,c_725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.39  
% 2.75/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 2.75/1.40  
% 2.75/1.40  %Foreground sorts:
% 2.75/1.40  
% 2.75/1.40  
% 2.75/1.40  %Background operators:
% 2.75/1.40  
% 2.75/1.40  
% 2.75/1.40  %Foreground operators:
% 2.75/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.75/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.75/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.75/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.75/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.75/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.75/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.75/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.75/1.40  
% 2.75/1.41  tff(f_113, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.75/1.41  tff(f_75, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.75/1.41  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.75/1.41  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.75/1.41  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.75/1.41  tff(f_81, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.75/1.41  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.75/1.41  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.75/1.41  tff(f_106, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.75/1.41  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.75/1.41  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 2.75/1.41  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.75/1.41  tff(c_50, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.75/1.41  tff(c_93, plain, (k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 2.75/1.41  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.75/1.41  tff(c_36, plain, (![A_40]: (r2_hidden('#skF_2'(A_40), A_40) | v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.75/1.41  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.75/1.41  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.41  tff(c_125, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, k3_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.41  tff(c_132, plain, (![A_6, C_86]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_125])).
% 2.75/1.41  tff(c_136, plain, (![C_87]: (~r2_hidden(C_87, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_132])).
% 2.75/1.41  tff(c_141, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_136])).
% 2.75/1.41  tff(c_38, plain, (![A_58, B_59]: (v1_relat_1(k5_relat_1(A_58, B_59)) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.75/1.41  tff(c_28, plain, (![B_37]: (k2_zfmisc_1(k1_xboole_0, B_37)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.75/1.41  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.75/1.41  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.75/1.41  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.75/1.41  tff(c_426, plain, (![A_131, B_132]: (k1_relat_1(k5_relat_1(A_131, B_132))=k1_relat_1(A_131) | ~r1_tarski(k2_relat_1(A_131), k1_relat_1(B_132)) | ~v1_relat_1(B_132) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.75/1.41  tff(c_435, plain, (![B_132]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_132))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_132)) | ~v1_relat_1(B_132) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_426])).
% 2.75/1.41  tff(c_442, plain, (![B_133]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_133))=k1_xboole_0 | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_8, c_48, c_435])).
% 2.75/1.41  tff(c_40, plain, (![A_60]: (k3_xboole_0(A_60, k2_zfmisc_1(k1_relat_1(A_60), k2_relat_1(A_60)))=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.75/1.41  tff(c_456, plain, (![B_133]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_133), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_133))))=k5_relat_1(k1_xboole_0, B_133) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_133)) | ~v1_relat_1(B_133))), inference(superposition, [status(thm), theory('equality')], [c_442, c_40])).
% 2.75/1.41  tff(c_472, plain, (![B_134]: (k5_relat_1(k1_xboole_0, B_134)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_134)) | ~v1_relat_1(B_134))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_28, c_456])).
% 2.75/1.41  tff(c_479, plain, (![B_59]: (k5_relat_1(k1_xboole_0, B_59)=k1_xboole_0 | ~v1_relat_1(B_59) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_472])).
% 2.75/1.41  tff(c_485, plain, (![B_135]: (k5_relat_1(k1_xboole_0, B_135)=k1_xboole_0 | ~v1_relat_1(B_135))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_479])).
% 2.75/1.41  tff(c_497, plain, (k5_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_485])).
% 2.75/1.41  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_497])).
% 2.75/1.41  tff(c_506, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.75/1.41  tff(c_548, plain, (![A_147, B_148, C_149]: (~r1_xboole_0(A_147, B_148) | ~r2_hidden(C_149, k3_xboole_0(A_147, B_148)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.41  tff(c_555, plain, (![A_6, C_149]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_149, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_548])).
% 2.75/1.41  tff(c_559, plain, (![C_150]: (~r2_hidden(C_150, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_555])).
% 2.75/1.41  tff(c_564, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_559])).
% 2.75/1.41  tff(c_26, plain, (![A_36]: (k2_zfmisc_1(A_36, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.75/1.41  tff(c_665, plain, (![B_177, A_178]: (k2_relat_1(k5_relat_1(B_177, A_178))=k2_relat_1(A_178) | ~r1_tarski(k1_relat_1(A_178), k2_relat_1(B_177)) | ~v1_relat_1(B_177) | ~v1_relat_1(A_178))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.75/1.41  tff(c_668, plain, (![B_177]: (k2_relat_1(k5_relat_1(B_177, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_177)) | ~v1_relat_1(B_177) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_665])).
% 2.75/1.41  tff(c_676, plain, (![B_179]: (k2_relat_1(k5_relat_1(B_179, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_179))), inference(demodulation, [status(thm), theory('equality')], [c_564, c_8, c_46, c_668])).
% 2.75/1.41  tff(c_687, plain, (![B_179]: (k3_xboole_0(k5_relat_1(B_179, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_179, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_179, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_179, k1_xboole_0)) | ~v1_relat_1(B_179))), inference(superposition, [status(thm), theory('equality')], [c_676, c_40])).
% 2.75/1.41  tff(c_705, plain, (![B_186]: (k5_relat_1(B_186, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_186, k1_xboole_0)) | ~v1_relat_1(B_186))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_26, c_687])).
% 2.75/1.41  tff(c_709, plain, (![A_58]: (k5_relat_1(A_58, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_38, c_705])).
% 2.75/1.41  tff(c_713, plain, (![A_187]: (k5_relat_1(A_187, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_187))), inference(demodulation, [status(thm), theory('equality')], [c_564, c_709])).
% 2.75/1.41  tff(c_725, plain, (k5_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_713])).
% 2.75/1.41  tff(c_732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_506, c_725])).
% 2.75/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.41  
% 2.75/1.41  Inference rules
% 2.75/1.41  ----------------------
% 2.75/1.41  #Ref     : 2
% 2.75/1.41  #Sup     : 149
% 2.75/1.41  #Fact    : 0
% 2.75/1.41  #Define  : 0
% 2.75/1.41  #Split   : 1
% 2.75/1.41  #Chain   : 0
% 2.75/1.41  #Close   : 0
% 2.75/1.41  
% 2.75/1.41  Ordering : KBO
% 2.75/1.41  
% 2.75/1.41  Simplification rules
% 2.75/1.41  ----------------------
% 2.75/1.41  #Subsume      : 12
% 2.75/1.41  #Demod        : 108
% 2.75/1.41  #Tautology    : 97
% 2.75/1.41  #SimpNegUnit  : 4
% 2.75/1.41  #BackRed      : 0
% 2.75/1.41  
% 2.75/1.41  #Partial instantiations: 0
% 2.75/1.41  #Strategies tried      : 1
% 2.75/1.41  
% 2.75/1.41  Timing (in seconds)
% 2.75/1.41  ----------------------
% 2.75/1.42  Preprocessing        : 0.34
% 2.75/1.42  Parsing              : 0.18
% 2.75/1.42  CNF conversion       : 0.03
% 2.75/1.42  Main loop            : 0.30
% 2.75/1.42  Inferencing          : 0.12
% 2.75/1.42  Reduction            : 0.09
% 2.75/1.42  Demodulation         : 0.06
% 2.75/1.42  BG Simplification    : 0.02
% 2.75/1.42  Subsumption          : 0.04
% 2.75/1.42  Abstraction          : 0.02
% 2.75/1.42  MUC search           : 0.00
% 2.75/1.42  Cooper               : 0.00
% 2.75/1.42  Total                : 0.68
% 2.75/1.42  Index Insertion      : 0.00
% 2.75/1.42  Index Deletion       : 0.00
% 2.75/1.42  Index Matching       : 0.00
% 2.75/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
