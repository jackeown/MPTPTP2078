%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:01 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 129 expanded)
%              Number of leaves         :   44 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 190 expanded)
%              Number of equality atoms :   37 (  56 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_42,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_104,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_68,plain,
    ( k5_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_95,plain,(
    k5_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_70,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_90,plain,(
    ! [A_75] :
      ( v1_relat_1(A_75)
      | ~ v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_94,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_90])).

tff(c_56,plain,(
    ! [A_62,B_63] :
      ( v1_relat_1(k5_relat_1(A_62,B_63))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_290,plain,(
    ! [A_115,B_116,D_117] :
      ( r2_hidden('#skF_6'(A_115,B_116,k2_zfmisc_1(A_115,B_116),D_117),A_115)
      | ~ r2_hidden(D_117,k2_zfmisc_1(A_115,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_139,plain,(
    ! [A_86,C_87,B_88] :
      ( ~ r2_hidden(A_86,C_87)
      | ~ r1_xboole_0(k2_tarski(A_86,B_88),C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_144,plain,(
    ! [A_86] : ~ r2_hidden(A_86,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_139])).

tff(c_296,plain,(
    ! [D_118,B_119] : ~ r2_hidden(D_118,k2_zfmisc_1(k1_xboole_0,B_119)) ),
    inference(resolution,[status(thm)],[c_290,c_144])).

tff(c_311,plain,(
    ! [B_119] : k2_zfmisc_1(k1_xboole_0,B_119) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_296])).

tff(c_66,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_194,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_98,B_99)),k1_relat_1(A_98))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_199,plain,(
    ! [B_99] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_99)),k1_xboole_0)
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_194])).

tff(c_203,plain,(
    ! [B_100] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_100)),k1_xboole_0)
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_199])).

tff(c_14,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_116,plain,(
    ! [B_83,A_84] :
      ( B_83 = A_84
      | ~ r1_tarski(B_83,A_84)
      | ~ r1_tarski(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_125,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_116])).

tff(c_213,plain,(
    ! [B_101] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_101)) = k1_xboole_0
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_203,c_125])).

tff(c_58,plain,(
    ! [A_64] :
      ( k3_xboole_0(A_64,k2_zfmisc_1(k1_relat_1(A_64),k2_relat_1(A_64))) = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_228,plain,(
    ! [B_101] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_101),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_101)))) = k5_relat_1(k1_xboole_0,B_101)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_58])).

tff(c_668,plain,(
    ! [B_167] :
      ( k5_relat_1(k1_xboole_0,B_167) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_167))
      | ~ v1_relat_1(B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_311,c_228])).

tff(c_672,plain,(
    ! [B_63] :
      ( k5_relat_1(k1_xboole_0,B_63) = k1_xboole_0
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_56,c_668])).

tff(c_676,plain,(
    ! [B_168] :
      ( k5_relat_1(k1_xboole_0,B_168) = k1_xboole_0
      | ~ v1_relat_1(B_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_672])).

tff(c_685,plain,(
    k5_relat_1(k1_xboole_0,'#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_676])).

tff(c_691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_685])).

tff(c_692,plain,(
    k5_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_917,plain,(
    ! [A_208,B_209,D_210] :
      ( r2_hidden('#skF_7'(A_208,B_209,k2_zfmisc_1(A_208,B_209),D_210),B_209)
      | ~ r2_hidden(D_210,k2_zfmisc_1(A_208,B_209)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_723,plain,(
    ! [A_176,C_177,B_178] :
      ( ~ r2_hidden(A_176,C_177)
      | ~ r1_xboole_0(k2_tarski(A_176,B_178),C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_728,plain,(
    ! [A_176] : ~ r2_hidden(A_176,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_723])).

tff(c_923,plain,(
    ! [D_211,A_212] : ~ r2_hidden(D_211,k2_zfmisc_1(A_212,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_917,c_728])).

tff(c_938,plain,(
    ! [A_212] : k2_zfmisc_1(A_212,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_923])).

tff(c_64,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_850,plain,(
    ! [A_191,B_192] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_191,B_192)),k2_relat_1(B_192))
      | ~ v1_relat_1(B_192)
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_858,plain,(
    ! [A_191] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_191,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_850])).

tff(c_864,plain,(
    ! [A_193] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_193,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_858])).

tff(c_736,plain,(
    ! [B_180,A_181] :
      ( B_180 = A_181
      | ~ r1_tarski(B_180,A_181)
      | ~ r1_tarski(A_181,B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_745,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_736])).

tff(c_883,plain,(
    ! [A_198] :
      ( k2_relat_1(k5_relat_1(A_198,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_198) ) ),
    inference(resolution,[status(thm)],[c_864,c_745])).

tff(c_898,plain,(
    ! [A_198] :
      ( k3_xboole_0(k5_relat_1(A_198,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_198,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_198,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_198,k1_xboole_0))
      | ~ v1_relat_1(A_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_883,c_58])).

tff(c_1325,plain,(
    ! [A_259] :
      ( k5_relat_1(A_259,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_259,k1_xboole_0))
      | ~ v1_relat_1(A_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_938,c_898])).

tff(c_1329,plain,(
    ! [A_62] :
      ( k5_relat_1(A_62,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_56,c_1325])).

tff(c_1334,plain,(
    ! [A_265] :
      ( k5_relat_1(A_265,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1329])).

tff(c_1343,plain,(
    k5_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_1334])).

tff(c_1349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_1343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.51  
% 3.20/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_3
% 3.20/1.52  
% 3.20/1.52  %Foreground sorts:
% 3.20/1.52  
% 3.20/1.52  
% 3.20/1.52  %Background operators:
% 3.20/1.52  
% 3.20/1.52  
% 3.20/1.52  %Foreground operators:
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.20/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.20/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.20/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.20/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.20/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.52  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.20/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.20/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.20/1.52  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.20/1.52  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.20/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.52  tff('#skF_8', type, '#skF_8': $i).
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.20/1.52  
% 3.20/1.53  tff(f_111, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.20/1.53  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.20/1.53  tff(f_77, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.20/1.53  tff(f_83, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.20/1.53  tff(f_42, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.20/1.53  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.20/1.53  tff(f_66, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.20/1.53  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.20/1.53  tff(f_71, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.20/1.53  tff(f_104, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.20/1.53  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.20/1.53  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.20/1.53  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.53  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.20/1.53  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.20/1.53  tff(c_68, plain, (k5_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.20/1.53  tff(c_95, plain, (k5_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_68])).
% 3.20/1.53  tff(c_70, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.20/1.53  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.20/1.53  tff(c_90, plain, (![A_75]: (v1_relat_1(A_75) | ~v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.20/1.53  tff(c_94, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_90])).
% 3.20/1.53  tff(c_56, plain, (![A_62, B_63]: (v1_relat_1(k5_relat_1(A_62, B_63)) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.20/1.53  tff(c_12, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.20/1.53  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.20/1.53  tff(c_290, plain, (![A_115, B_116, D_117]: (r2_hidden('#skF_6'(A_115, B_116, k2_zfmisc_1(A_115, B_116), D_117), A_115) | ~r2_hidden(D_117, k2_zfmisc_1(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.20/1.53  tff(c_16, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.53  tff(c_139, plain, (![A_86, C_87, B_88]: (~r2_hidden(A_86, C_87) | ~r1_xboole_0(k2_tarski(A_86, B_88), C_87))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.20/1.53  tff(c_144, plain, (![A_86]: (~r2_hidden(A_86, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_139])).
% 3.20/1.53  tff(c_296, plain, (![D_118, B_119]: (~r2_hidden(D_118, k2_zfmisc_1(k1_xboole_0, B_119)))), inference(resolution, [status(thm)], [c_290, c_144])).
% 3.20/1.53  tff(c_311, plain, (![B_119]: (k2_zfmisc_1(k1_xboole_0, B_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_296])).
% 3.20/1.53  tff(c_66, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.53  tff(c_194, plain, (![A_98, B_99]: (r1_tarski(k1_relat_1(k5_relat_1(A_98, B_99)), k1_relat_1(A_98)) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.20/1.53  tff(c_199, plain, (![B_99]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_99)), k1_xboole_0) | ~v1_relat_1(B_99) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_194])).
% 3.20/1.53  tff(c_203, plain, (![B_100]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_100)), k1_xboole_0) | ~v1_relat_1(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_199])).
% 3.20/1.53  tff(c_14, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.20/1.53  tff(c_116, plain, (![B_83, A_84]: (B_83=A_84 | ~r1_tarski(B_83, A_84) | ~r1_tarski(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.20/1.53  tff(c_125, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_116])).
% 3.20/1.53  tff(c_213, plain, (![B_101]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_101))=k1_xboole_0 | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_203, c_125])).
% 3.20/1.53  tff(c_58, plain, (![A_64]: (k3_xboole_0(A_64, k2_zfmisc_1(k1_relat_1(A_64), k2_relat_1(A_64)))=A_64 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.20/1.53  tff(c_228, plain, (![B_101]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_101), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_101))))=k5_relat_1(k1_xboole_0, B_101) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_101)) | ~v1_relat_1(B_101))), inference(superposition, [status(thm), theory('equality')], [c_213, c_58])).
% 3.20/1.53  tff(c_668, plain, (![B_167]: (k5_relat_1(k1_xboole_0, B_167)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_167)) | ~v1_relat_1(B_167))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_311, c_228])).
% 3.20/1.53  tff(c_672, plain, (![B_63]: (k5_relat_1(k1_xboole_0, B_63)=k1_xboole_0 | ~v1_relat_1(B_63) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_668])).
% 3.20/1.53  tff(c_676, plain, (![B_168]: (k5_relat_1(k1_xboole_0, B_168)=k1_xboole_0 | ~v1_relat_1(B_168))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_672])).
% 3.20/1.53  tff(c_685, plain, (k5_relat_1(k1_xboole_0, '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_676])).
% 3.20/1.53  tff(c_691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_685])).
% 3.20/1.53  tff(c_692, plain, (k5_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 3.20/1.53  tff(c_917, plain, (![A_208, B_209, D_210]: (r2_hidden('#skF_7'(A_208, B_209, k2_zfmisc_1(A_208, B_209), D_210), B_209) | ~r2_hidden(D_210, k2_zfmisc_1(A_208, B_209)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.20/1.53  tff(c_723, plain, (![A_176, C_177, B_178]: (~r2_hidden(A_176, C_177) | ~r1_xboole_0(k2_tarski(A_176, B_178), C_177))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.20/1.53  tff(c_728, plain, (![A_176]: (~r2_hidden(A_176, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_723])).
% 3.20/1.53  tff(c_923, plain, (![D_211, A_212]: (~r2_hidden(D_211, k2_zfmisc_1(A_212, k1_xboole_0)))), inference(resolution, [status(thm)], [c_917, c_728])).
% 3.20/1.53  tff(c_938, plain, (![A_212]: (k2_zfmisc_1(A_212, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_923])).
% 3.20/1.53  tff(c_64, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.53  tff(c_850, plain, (![A_191, B_192]: (r1_tarski(k2_relat_1(k5_relat_1(A_191, B_192)), k2_relat_1(B_192)) | ~v1_relat_1(B_192) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.20/1.53  tff(c_858, plain, (![A_191]: (r1_tarski(k2_relat_1(k5_relat_1(A_191, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_191))), inference(superposition, [status(thm), theory('equality')], [c_64, c_850])).
% 3.20/1.53  tff(c_864, plain, (![A_193]: (r1_tarski(k2_relat_1(k5_relat_1(A_193, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_193))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_858])).
% 3.20/1.53  tff(c_736, plain, (![B_180, A_181]: (B_180=A_181 | ~r1_tarski(B_180, A_181) | ~r1_tarski(A_181, B_180))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.20/1.53  tff(c_745, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_736])).
% 3.20/1.53  tff(c_883, plain, (![A_198]: (k2_relat_1(k5_relat_1(A_198, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_198))), inference(resolution, [status(thm)], [c_864, c_745])).
% 3.20/1.53  tff(c_898, plain, (![A_198]: (k3_xboole_0(k5_relat_1(A_198, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_198, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_198, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_198, k1_xboole_0)) | ~v1_relat_1(A_198))), inference(superposition, [status(thm), theory('equality')], [c_883, c_58])).
% 3.20/1.53  tff(c_1325, plain, (![A_259]: (k5_relat_1(A_259, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_259, k1_xboole_0)) | ~v1_relat_1(A_259))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_938, c_898])).
% 3.20/1.53  tff(c_1329, plain, (![A_62]: (k5_relat_1(A_62, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_56, c_1325])).
% 3.20/1.53  tff(c_1334, plain, (![A_265]: (k5_relat_1(A_265, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_265))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1329])).
% 3.20/1.53  tff(c_1343, plain, (k5_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_1334])).
% 3.20/1.53  tff(c_1349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_692, c_1343])).
% 3.20/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.53  
% 3.20/1.53  Inference rules
% 3.20/1.53  ----------------------
% 3.20/1.53  #Ref     : 0
% 3.20/1.53  #Sup     : 280
% 3.20/1.53  #Fact    : 0
% 3.20/1.53  #Define  : 0
% 3.20/1.53  #Split   : 1
% 3.20/1.53  #Chain   : 0
% 3.20/1.53  #Close   : 0
% 3.20/1.53  
% 3.20/1.53  Ordering : KBO
% 3.20/1.53  
% 3.20/1.53  Simplification rules
% 3.20/1.53  ----------------------
% 3.20/1.53  #Subsume      : 77
% 3.20/1.53  #Demod        : 195
% 3.20/1.53  #Tautology    : 122
% 3.20/1.53  #SimpNegUnit  : 10
% 3.20/1.53  #BackRed      : 6
% 3.20/1.53  
% 3.20/1.53  #Partial instantiations: 0
% 3.20/1.53  #Strategies tried      : 1
% 3.20/1.53  
% 3.20/1.53  Timing (in seconds)
% 3.20/1.53  ----------------------
% 3.20/1.54  Preprocessing        : 0.33
% 3.20/1.54  Parsing              : 0.17
% 3.20/1.54  CNF conversion       : 0.03
% 3.20/1.54  Main loop            : 0.43
% 3.20/1.54  Inferencing          : 0.17
% 3.20/1.54  Reduction            : 0.13
% 3.20/1.54  Demodulation         : 0.09
% 3.20/1.54  BG Simplification    : 0.03
% 3.20/1.54  Subsumption          : 0.07
% 3.20/1.54  Abstraction          : 0.03
% 3.20/1.54  MUC search           : 0.00
% 3.20/1.54  Cooper               : 0.00
% 3.20/1.54  Total                : 0.79
% 3.20/1.54  Index Insertion      : 0.00
% 3.20/1.54  Index Deletion       : 0.00
% 3.20/1.54  Index Matching       : 0.00
% 3.20/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
