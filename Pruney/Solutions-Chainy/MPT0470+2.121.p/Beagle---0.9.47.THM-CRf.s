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
% DateTime   : Thu Dec  3 09:59:17 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 127 expanded)
%              Number of leaves         :   40 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 192 expanded)
%              Number of equality atoms :   39 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_36,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_100,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_46,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_77,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_164,plain,(
    ! [A_79,C_80,B_81] :
      ( ~ r2_hidden(A_79,C_80)
      | ~ r1_xboole_0(k2_tarski(A_79,B_81),C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_170,plain,(
    ! [A_82] : ~ r2_hidden(A_82,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_164])).

tff(c_175,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_170])).

tff(c_34,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(k5_relat_1(A_46,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_2] : k3_xboole_0(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_79,plain,(
    ! [A_62,B_63] :
      ( v1_xboole_0(k2_zfmisc_1(A_62,B_63))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_119,plain,(
    ! [A_69,B_70] :
      ( k2_zfmisc_1(A_69,B_70) = k1_xboole_0
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_79,c_4])).

tff(c_128,plain,(
    ! [B_70] : k2_zfmisc_1(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_119])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_506,plain,(
    ! [A_115,B_116] :
      ( k1_relat_1(k5_relat_1(A_115,B_116)) = k1_relat_1(A_115)
      | ~ r1_tarski(k2_relat_1(A_115),k1_relat_1(B_116))
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_512,plain,(
    ! [B_116] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_116)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_116))
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_506])).

tff(c_517,plain,(
    ! [B_117] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_117)) = k1_xboole_0
      | ~ v1_relat_1(B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_8,c_44,c_512])).

tff(c_36,plain,(
    ! [A_48] :
      ( k3_xboole_0(A_48,k2_zfmisc_1(k1_relat_1(A_48),k2_relat_1(A_48))) = A_48
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_526,plain,(
    ! [B_117] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_117),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_117)))) = k5_relat_1(k1_xboole_0,B_117)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_117))
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_36])).

tff(c_533,plain,(
    ! [B_118] :
      ( k5_relat_1(k1_xboole_0,B_118) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_118))
      | ~ v1_relat_1(B_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_128,c_526])).

tff(c_537,plain,(
    ! [B_47] :
      ( k5_relat_1(k1_xboole_0,B_47) = k1_xboole_0
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_533])).

tff(c_541,plain,(
    ! [B_119] :
      ( k5_relat_1(k1_xboole_0,B_119) = k1_xboole_0
      | ~ v1_relat_1(B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_537])).

tff(c_550,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_541])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_550])).

tff(c_557,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_648,plain,(
    ! [A_136,C_137,B_138] :
      ( ~ r2_hidden(A_136,C_137)
      | ~ r1_xboole_0(k2_tarski(A_136,B_138),C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_654,plain,(
    ! [A_139] : ~ r2_hidden(A_139,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_648])).

tff(c_659,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_654])).

tff(c_72,plain,(
    ! [A_59,B_60] :
      ( v1_xboole_0(k2_zfmisc_1(A_59,B_60))
      | ~ v1_xboole_0(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_569,plain,(
    ! [A_123,B_124] :
      ( k2_zfmisc_1(A_123,B_124) = k1_xboole_0
      | ~ v1_xboole_0(B_124) ) ),
    inference(resolution,[status(thm)],[c_72,c_4])).

tff(c_578,plain,(
    ! [A_123] : k2_zfmisc_1(A_123,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_569])).

tff(c_996,plain,(
    ! [B_174,A_175] :
      ( k2_relat_1(k5_relat_1(B_174,A_175)) = k2_relat_1(A_175)
      | ~ r1_tarski(k1_relat_1(A_175),k2_relat_1(B_174))
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_999,plain,(
    ! [B_174] :
      ( k2_relat_1(k5_relat_1(B_174,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_174))
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_996])).

tff(c_1007,plain,(
    ! [B_176] :
      ( k2_relat_1(k5_relat_1(B_176,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_8,c_42,c_999])).

tff(c_1016,plain,(
    ! [B_176] :
      ( k3_xboole_0(k5_relat_1(B_176,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_176,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_176,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_176,k1_xboole_0))
      | ~ v1_relat_1(B_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1007,c_36])).

tff(c_1023,plain,(
    ! [B_177] :
      ( k5_relat_1(B_177,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_177,k1_xboole_0))
      | ~ v1_relat_1(B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_578,c_1016])).

tff(c_1027,plain,(
    ! [A_46] :
      ( k5_relat_1(A_46,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_34,c_1023])).

tff(c_1031,plain,(
    ! [A_178] :
      ( k5_relat_1(A_178,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_1027])).

tff(c_1040,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_1031])).

tff(c_1046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_557,c_1040])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:38:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.50  
% 3.01/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.01/1.50  
% 3.01/1.50  %Foreground sorts:
% 3.01/1.50  
% 3.01/1.50  
% 3.01/1.50  %Background operators:
% 3.01/1.50  
% 3.01/1.50  
% 3.01/1.50  %Foreground operators:
% 3.01/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.01/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.01/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.01/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.01/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.01/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.01/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.01/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.01/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.01/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.01/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.01/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.01/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.01/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.01/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.01/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.01/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.01/1.50  
% 3.01/1.52  tff(f_107, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.01/1.52  tff(f_69, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.01/1.52  tff(f_36, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.01/1.52  tff(f_57, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.01/1.52  tff(f_75, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.01/1.52  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.01/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.01/1.52  tff(f_52, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.01/1.52  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.01/1.52  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.01/1.52  tff(f_100, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.01/1.52  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.01/1.52  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.01/1.52  tff(f_48, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.01/1.52  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.01/1.52  tff(c_46, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.01/1.52  tff(c_77, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 3.01/1.52  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.01/1.52  tff(c_32, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.01/1.52  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.01/1.52  tff(c_164, plain, (![A_79, C_80, B_81]: (~r2_hidden(A_79, C_80) | ~r1_xboole_0(k2_tarski(A_79, B_81), C_80))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.52  tff(c_170, plain, (![A_82]: (~r2_hidden(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_164])).
% 3.01/1.52  tff(c_175, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_170])).
% 3.01/1.52  tff(c_34, plain, (![A_46, B_47]: (v1_relat_1(k5_relat_1(A_46, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.01/1.52  tff(c_6, plain, (![A_2]: (k3_xboole_0(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.01/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.01/1.52  tff(c_79, plain, (![A_62, B_63]: (v1_xboole_0(k2_zfmisc_1(A_62, B_63)) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.01/1.52  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.01/1.52  tff(c_119, plain, (![A_69, B_70]: (k2_zfmisc_1(A_69, B_70)=k1_xboole_0 | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_79, c_4])).
% 3.01/1.52  tff(c_128, plain, (![B_70]: (k2_zfmisc_1(k1_xboole_0, B_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_119])).
% 3.01/1.52  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.01/1.52  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.01/1.52  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.01/1.52  tff(c_506, plain, (![A_115, B_116]: (k1_relat_1(k5_relat_1(A_115, B_116))=k1_relat_1(A_115) | ~r1_tarski(k2_relat_1(A_115), k1_relat_1(B_116)) | ~v1_relat_1(B_116) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.01/1.52  tff(c_512, plain, (![B_116]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_116))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_116)) | ~v1_relat_1(B_116) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_506])).
% 3.01/1.52  tff(c_517, plain, (![B_117]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_117))=k1_xboole_0 | ~v1_relat_1(B_117))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_8, c_44, c_512])).
% 3.01/1.52  tff(c_36, plain, (![A_48]: (k3_xboole_0(A_48, k2_zfmisc_1(k1_relat_1(A_48), k2_relat_1(A_48)))=A_48 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.01/1.52  tff(c_526, plain, (![B_117]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_117), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_117))))=k5_relat_1(k1_xboole_0, B_117) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_117)) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_517, c_36])).
% 3.01/1.52  tff(c_533, plain, (![B_118]: (k5_relat_1(k1_xboole_0, B_118)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_118)) | ~v1_relat_1(B_118))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_128, c_526])).
% 3.01/1.52  tff(c_537, plain, (![B_47]: (k5_relat_1(k1_xboole_0, B_47)=k1_xboole_0 | ~v1_relat_1(B_47) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_533])).
% 3.01/1.52  tff(c_541, plain, (![B_119]: (k5_relat_1(k1_xboole_0, B_119)=k1_xboole_0 | ~v1_relat_1(B_119))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_537])).
% 3.01/1.52  tff(c_550, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_541])).
% 3.01/1.52  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_550])).
% 3.01/1.52  tff(c_557, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 3.01/1.52  tff(c_648, plain, (![A_136, C_137, B_138]: (~r2_hidden(A_136, C_137) | ~r1_xboole_0(k2_tarski(A_136, B_138), C_137))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.52  tff(c_654, plain, (![A_139]: (~r2_hidden(A_139, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_648])).
% 3.01/1.52  tff(c_659, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_654])).
% 3.01/1.52  tff(c_72, plain, (![A_59, B_60]: (v1_xboole_0(k2_zfmisc_1(A_59, B_60)) | ~v1_xboole_0(B_60))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.01/1.52  tff(c_569, plain, (![A_123, B_124]: (k2_zfmisc_1(A_123, B_124)=k1_xboole_0 | ~v1_xboole_0(B_124))), inference(resolution, [status(thm)], [c_72, c_4])).
% 3.01/1.52  tff(c_578, plain, (![A_123]: (k2_zfmisc_1(A_123, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_569])).
% 3.01/1.52  tff(c_996, plain, (![B_174, A_175]: (k2_relat_1(k5_relat_1(B_174, A_175))=k2_relat_1(A_175) | ~r1_tarski(k1_relat_1(A_175), k2_relat_1(B_174)) | ~v1_relat_1(B_174) | ~v1_relat_1(A_175))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.01/1.52  tff(c_999, plain, (![B_174]: (k2_relat_1(k5_relat_1(B_174, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_174)) | ~v1_relat_1(B_174) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_996])).
% 3.01/1.52  tff(c_1007, plain, (![B_176]: (k2_relat_1(k5_relat_1(B_176, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_176))), inference(demodulation, [status(thm), theory('equality')], [c_659, c_8, c_42, c_999])).
% 3.01/1.52  tff(c_1016, plain, (![B_176]: (k3_xboole_0(k5_relat_1(B_176, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_176, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_176, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_176, k1_xboole_0)) | ~v1_relat_1(B_176))), inference(superposition, [status(thm), theory('equality')], [c_1007, c_36])).
% 3.01/1.52  tff(c_1023, plain, (![B_177]: (k5_relat_1(B_177, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_177, k1_xboole_0)) | ~v1_relat_1(B_177))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_578, c_1016])).
% 3.01/1.52  tff(c_1027, plain, (![A_46]: (k5_relat_1(A_46, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_34, c_1023])).
% 3.01/1.52  tff(c_1031, plain, (![A_178]: (k5_relat_1(A_178, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_178))), inference(demodulation, [status(thm), theory('equality')], [c_659, c_1027])).
% 3.01/1.52  tff(c_1040, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_1031])).
% 3.01/1.52  tff(c_1046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_557, c_1040])).
% 3.01/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.52  
% 3.01/1.52  Inference rules
% 3.01/1.52  ----------------------
% 3.01/1.52  #Ref     : 2
% 3.01/1.52  #Sup     : 233
% 3.01/1.52  #Fact    : 0
% 3.01/1.52  #Define  : 0
% 3.01/1.52  #Split   : 1
% 3.01/1.52  #Chain   : 0
% 3.01/1.52  #Close   : 0
% 3.01/1.52  
% 3.01/1.52  Ordering : KBO
% 3.01/1.52  
% 3.01/1.52  Simplification rules
% 3.01/1.52  ----------------------
% 3.01/1.52  #Subsume      : 2
% 3.01/1.52  #Demod        : 125
% 3.01/1.52  #Tautology    : 196
% 3.01/1.52  #SimpNegUnit  : 2
% 3.01/1.52  #BackRed      : 0
% 3.01/1.52  
% 3.01/1.52  #Partial instantiations: 0
% 3.01/1.52  #Strategies tried      : 1
% 3.01/1.52  
% 3.01/1.52  Timing (in seconds)
% 3.01/1.52  ----------------------
% 3.01/1.52  Preprocessing        : 0.33
% 3.01/1.52  Parsing              : 0.18
% 3.01/1.52  CNF conversion       : 0.02
% 3.01/1.52  Main loop            : 0.35
% 3.01/1.52  Inferencing          : 0.14
% 3.01/1.52  Reduction            : 0.10
% 3.01/1.52  Demodulation         : 0.07
% 3.01/1.52  BG Simplification    : 0.02
% 3.01/1.52  Subsumption          : 0.06
% 3.01/1.52  Abstraction          : 0.02
% 3.01/1.52  MUC search           : 0.00
% 3.01/1.52  Cooper               : 0.00
% 3.01/1.52  Total                : 0.71
% 3.01/1.52  Index Insertion      : 0.00
% 3.01/1.52  Index Deletion       : 0.00
% 3.01/1.52  Index Matching       : 0.00
% 3.01/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
