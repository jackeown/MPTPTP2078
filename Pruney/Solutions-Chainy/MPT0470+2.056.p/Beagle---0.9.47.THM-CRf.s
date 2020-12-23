%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:08 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 139 expanded)
%              Number of leaves         :   42 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  141 ( 214 expanded)
%              Number of equality atoms :   38 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_58,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_62,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_60,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_117,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_56,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_101,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_58,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,(
    ! [A_66] :
      ( v1_relat_1(A_66)
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_106,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_44,plain,(
    ! [A_52,B_53] :
      ( v1_relat_1(k5_relat_1(A_52,B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_113,plain,(
    ! [B_70,A_71] :
      ( r1_xboole_0(B_70,A_71)
      | ~ r1_xboole_0(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_116,plain,(
    ! [A_17] : r1_xboole_0(k1_xboole_0,A_17) ),
    inference(resolution,[status(thm)],[c_22,c_113])).

tff(c_415,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( ~ r1_xboole_0(A_112,B_113)
      | r1_xboole_0(k2_zfmisc_1(A_112,C_114),k2_zfmisc_1(B_113,D_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,k3_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_171,plain,(
    ! [A_85,B_86] :
      ( ~ r1_xboole_0(A_85,B_86)
      | v1_xboole_0(k3_xboole_0(A_85,B_86)) ) ),
    inference(resolution,[status(thm)],[c_4,c_141])).

tff(c_183,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_171])).

tff(c_453,plain,(
    ! [B_116,D_117] :
      ( v1_xboole_0(k2_zfmisc_1(B_116,D_117))
      | ~ r1_xboole_0(B_116,B_116) ) ),
    inference(resolution,[status(thm)],[c_415,c_183])).

tff(c_470,plain,(
    ! [D_118] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,D_118)) ),
    inference(resolution,[status(thm)],[c_116,c_453])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_481,plain,(
    ! [D_118] : k2_zfmisc_1(k1_xboole_0,D_118) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_470,c_10])).

tff(c_20,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1147,plain,(
    ! [A_171,B_172] :
      ( k1_relat_1(k5_relat_1(A_171,B_172)) = k1_relat_1(A_171)
      | ~ r1_tarski(k2_relat_1(A_171),k1_relat_1(B_172))
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1153,plain,(
    ! [B_172] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_172)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_172))
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1147])).

tff(c_1158,plain,(
    ! [B_173] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_173)) = k1_xboole_0
      | ~ v1_relat_1(B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_20,c_54,c_1153])).

tff(c_46,plain,(
    ! [A_54] :
      ( k3_xboole_0(A_54,k2_zfmisc_1(k1_relat_1(A_54),k2_relat_1(A_54))) = A_54
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1167,plain,(
    ! [B_173] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_173),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_173)))) = k5_relat_1(k1_xboole_0,B_173)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_173))
      | ~ v1_relat_1(B_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_46])).

tff(c_3353,plain,(
    ! [B_294] :
      ( k5_relat_1(k1_xboole_0,B_294) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_294))
      | ~ v1_relat_1(B_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_481,c_1167])).

tff(c_3360,plain,(
    ! [B_53] :
      ( k5_relat_1(k1_xboole_0,B_53) = k1_xboole_0
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_3353])).

tff(c_3366,plain,(
    ! [B_295] :
      ( k5_relat_1(k1_xboole_0,B_295) = k1_xboole_0
      | ~ v1_relat_1(B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3360])).

tff(c_3402,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_3366])).

tff(c_3418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_3402])).

tff(c_3419,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3421,plain,(
    ! [A_296] :
      ( v1_relat_1(A_296)
      | ~ v1_xboole_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3425,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_3421])).

tff(c_3431,plain,(
    ! [B_299,A_300] :
      ( r1_xboole_0(B_299,A_300)
      | ~ r1_xboole_0(A_300,B_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3434,plain,(
    ! [A_17] : r1_xboole_0(k1_xboole_0,A_17) ),
    inference(resolution,[status(thm)],[c_22,c_3431])).

tff(c_3853,plain,(
    ! [C_354,D_355,A_356,B_357] :
      ( ~ r1_xboole_0(C_354,D_355)
      | r1_xboole_0(k2_zfmisc_1(A_356,C_354),k2_zfmisc_1(B_357,D_355)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3469,plain,(
    ! [A_309,B_310,C_311] :
      ( ~ r1_xboole_0(A_309,B_310)
      | ~ r2_hidden(C_311,k3_xboole_0(A_309,B_310)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3499,plain,(
    ! [A_315,B_316] :
      ( ~ r1_xboole_0(A_315,B_316)
      | v1_xboole_0(k3_xboole_0(A_315,B_316)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3469])).

tff(c_3511,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3499])).

tff(c_3906,plain,(
    ! [B_360,D_361] :
      ( v1_xboole_0(k2_zfmisc_1(B_360,D_361))
      | ~ r1_xboole_0(D_361,D_361) ) ),
    inference(resolution,[status(thm)],[c_3853,c_3511])).

tff(c_3926,plain,(
    ! [B_362] : v1_xboole_0(k2_zfmisc_1(B_362,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3434,c_3906])).

tff(c_3940,plain,(
    ! [B_362] : k2_zfmisc_1(B_362,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3926,c_10])).

tff(c_4254,plain,(
    ! [B_395,A_396] :
      ( k2_relat_1(k5_relat_1(B_395,A_396)) = k2_relat_1(A_396)
      | ~ r1_tarski(k1_relat_1(A_396),k2_relat_1(B_395))
      | ~ v1_relat_1(B_395)
      | ~ v1_relat_1(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4260,plain,(
    ! [B_395] :
      ( k2_relat_1(k5_relat_1(B_395,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_395))
      | ~ v1_relat_1(B_395)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_4254])).

tff(c_4270,plain,(
    ! [B_397] :
      ( k2_relat_1(k5_relat_1(B_397,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_397) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3425,c_20,c_52,c_4260])).

tff(c_4282,plain,(
    ! [B_397] :
      ( k3_xboole_0(k5_relat_1(B_397,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_397,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_397,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_397,k1_xboole_0))
      | ~ v1_relat_1(B_397) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4270,c_46])).

tff(c_6780,plain,(
    ! [B_527] :
      ( k5_relat_1(B_527,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_527,k1_xboole_0))
      | ~ v1_relat_1(B_527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3940,c_4282])).

tff(c_6787,plain,(
    ! [A_52] :
      ( k5_relat_1(A_52,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_44,c_6780])).

tff(c_6793,plain,(
    ! [A_528] :
      ( k5_relat_1(A_528,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_528) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3425,c_6787])).

tff(c_6829,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_6793])).

tff(c_6845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3419,c_6829])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.02  
% 5.37/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.02  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 5.37/2.02  
% 5.37/2.02  %Foreground sorts:
% 5.37/2.02  
% 5.37/2.02  
% 5.37/2.02  %Background operators:
% 5.37/2.02  
% 5.37/2.02  
% 5.37/2.02  %Foreground operators:
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.37/2.02  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.37/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.37/2.02  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.37/2.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.37/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.37/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.37/2.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.37/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.37/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.37/2.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.37/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.37/2.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.37/2.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.37/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.37/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.37/2.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.37/2.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.37/2.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.37/2.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.37/2.02  
% 5.63/2.04  tff(f_124, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 5.63/2.04  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.63/2.04  tff(f_86, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 5.63/2.04  tff(f_92, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.63/2.04  tff(f_58, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.63/2.04  tff(f_62, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.63/2.04  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.63/2.04  tff(f_80, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 5.63/2.04  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.63/2.04  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.63/2.04  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.63/2.04  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.63/2.04  tff(f_60, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.63/2.04  tff(f_117, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.63/2.04  tff(f_105, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 5.63/2.04  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 5.63/2.04  tff(f_114, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 5.63/2.04  tff(c_56, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.63/2.04  tff(c_101, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 5.63/2.04  tff(c_58, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.63/2.04  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.63/2.04  tff(c_102, plain, (![A_66]: (v1_relat_1(A_66) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.63/2.04  tff(c_106, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_102])).
% 5.63/2.04  tff(c_44, plain, (![A_52, B_53]: (v1_relat_1(k5_relat_1(A_52, B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.63/2.04  tff(c_18, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.63/2.04  tff(c_22, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.63/2.04  tff(c_113, plain, (![B_70, A_71]: (r1_xboole_0(B_70, A_71) | ~r1_xboole_0(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.63/2.04  tff(c_116, plain, (![A_17]: (r1_xboole_0(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_22, c_113])).
% 5.63/2.04  tff(c_415, plain, (![A_112, B_113, C_114, D_115]: (~r1_xboole_0(A_112, B_113) | r1_xboole_0(k2_zfmisc_1(A_112, C_114), k2_zfmisc_1(B_113, D_115)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.63/2.04  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.63/2.04  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.63/2.04  tff(c_141, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, k3_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.63/2.04  tff(c_171, plain, (![A_85, B_86]: (~r1_xboole_0(A_85, B_86) | v1_xboole_0(k3_xboole_0(A_85, B_86)))), inference(resolution, [status(thm)], [c_4, c_141])).
% 5.63/2.04  tff(c_183, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | v1_xboole_0(A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_171])).
% 5.63/2.04  tff(c_453, plain, (![B_116, D_117]: (v1_xboole_0(k2_zfmisc_1(B_116, D_117)) | ~r1_xboole_0(B_116, B_116))), inference(resolution, [status(thm)], [c_415, c_183])).
% 5.63/2.04  tff(c_470, plain, (![D_118]: (v1_xboole_0(k2_zfmisc_1(k1_xboole_0, D_118)))), inference(resolution, [status(thm)], [c_116, c_453])).
% 5.63/2.04  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.63/2.04  tff(c_481, plain, (![D_118]: (k2_zfmisc_1(k1_xboole_0, D_118)=k1_xboole_0)), inference(resolution, [status(thm)], [c_470, c_10])).
% 5.63/2.04  tff(c_20, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.63/2.04  tff(c_54, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.63/2.04  tff(c_52, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.63/2.04  tff(c_1147, plain, (![A_171, B_172]: (k1_relat_1(k5_relat_1(A_171, B_172))=k1_relat_1(A_171) | ~r1_tarski(k2_relat_1(A_171), k1_relat_1(B_172)) | ~v1_relat_1(B_172) | ~v1_relat_1(A_171))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.63/2.04  tff(c_1153, plain, (![B_172]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_172))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_172)) | ~v1_relat_1(B_172) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1147])).
% 5.63/2.04  tff(c_1158, plain, (![B_173]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_173))=k1_xboole_0 | ~v1_relat_1(B_173))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_20, c_54, c_1153])).
% 5.63/2.04  tff(c_46, plain, (![A_54]: (k3_xboole_0(A_54, k2_zfmisc_1(k1_relat_1(A_54), k2_relat_1(A_54)))=A_54 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.63/2.04  tff(c_1167, plain, (![B_173]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_173), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_173))))=k5_relat_1(k1_xboole_0, B_173) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_173)) | ~v1_relat_1(B_173))), inference(superposition, [status(thm), theory('equality')], [c_1158, c_46])).
% 5.63/2.04  tff(c_3353, plain, (![B_294]: (k5_relat_1(k1_xboole_0, B_294)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_294)) | ~v1_relat_1(B_294))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_481, c_1167])).
% 5.63/2.04  tff(c_3360, plain, (![B_53]: (k5_relat_1(k1_xboole_0, B_53)=k1_xboole_0 | ~v1_relat_1(B_53) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_3353])).
% 5.63/2.04  tff(c_3366, plain, (![B_295]: (k5_relat_1(k1_xboole_0, B_295)=k1_xboole_0 | ~v1_relat_1(B_295))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3360])).
% 5.63/2.04  tff(c_3402, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_3366])).
% 5.63/2.04  tff(c_3418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_3402])).
% 5.63/2.04  tff(c_3419, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 5.63/2.04  tff(c_3421, plain, (![A_296]: (v1_relat_1(A_296) | ~v1_xboole_0(A_296))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.63/2.04  tff(c_3425, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_3421])).
% 5.63/2.04  tff(c_3431, plain, (![B_299, A_300]: (r1_xboole_0(B_299, A_300) | ~r1_xboole_0(A_300, B_299))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.63/2.04  tff(c_3434, plain, (![A_17]: (r1_xboole_0(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_22, c_3431])).
% 5.63/2.04  tff(c_3853, plain, (![C_354, D_355, A_356, B_357]: (~r1_xboole_0(C_354, D_355) | r1_xboole_0(k2_zfmisc_1(A_356, C_354), k2_zfmisc_1(B_357, D_355)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.63/2.04  tff(c_3469, plain, (![A_309, B_310, C_311]: (~r1_xboole_0(A_309, B_310) | ~r2_hidden(C_311, k3_xboole_0(A_309, B_310)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.63/2.04  tff(c_3499, plain, (![A_315, B_316]: (~r1_xboole_0(A_315, B_316) | v1_xboole_0(k3_xboole_0(A_315, B_316)))), inference(resolution, [status(thm)], [c_4, c_3469])).
% 5.63/2.04  tff(c_3511, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | v1_xboole_0(A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3499])).
% 5.63/2.04  tff(c_3906, plain, (![B_360, D_361]: (v1_xboole_0(k2_zfmisc_1(B_360, D_361)) | ~r1_xboole_0(D_361, D_361))), inference(resolution, [status(thm)], [c_3853, c_3511])).
% 5.63/2.04  tff(c_3926, plain, (![B_362]: (v1_xboole_0(k2_zfmisc_1(B_362, k1_xboole_0)))), inference(resolution, [status(thm)], [c_3434, c_3906])).
% 5.63/2.04  tff(c_3940, plain, (![B_362]: (k2_zfmisc_1(B_362, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3926, c_10])).
% 5.63/2.04  tff(c_4254, plain, (![B_395, A_396]: (k2_relat_1(k5_relat_1(B_395, A_396))=k2_relat_1(A_396) | ~r1_tarski(k1_relat_1(A_396), k2_relat_1(B_395)) | ~v1_relat_1(B_395) | ~v1_relat_1(A_396))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.63/2.04  tff(c_4260, plain, (![B_395]: (k2_relat_1(k5_relat_1(B_395, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_395)) | ~v1_relat_1(B_395) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_4254])).
% 5.63/2.04  tff(c_4270, plain, (![B_397]: (k2_relat_1(k5_relat_1(B_397, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_397))), inference(demodulation, [status(thm), theory('equality')], [c_3425, c_20, c_52, c_4260])).
% 5.63/2.04  tff(c_4282, plain, (![B_397]: (k3_xboole_0(k5_relat_1(B_397, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_397, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_397, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_397, k1_xboole_0)) | ~v1_relat_1(B_397))), inference(superposition, [status(thm), theory('equality')], [c_4270, c_46])).
% 5.63/2.04  tff(c_6780, plain, (![B_527]: (k5_relat_1(B_527, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_527, k1_xboole_0)) | ~v1_relat_1(B_527))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3940, c_4282])).
% 5.63/2.04  tff(c_6787, plain, (![A_52]: (k5_relat_1(A_52, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_52))), inference(resolution, [status(thm)], [c_44, c_6780])).
% 5.63/2.04  tff(c_6793, plain, (![A_528]: (k5_relat_1(A_528, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_528))), inference(demodulation, [status(thm), theory('equality')], [c_3425, c_6787])).
% 5.63/2.04  tff(c_6829, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_6793])).
% 5.63/2.04  tff(c_6845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3419, c_6829])).
% 5.63/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.63/2.04  
% 5.63/2.04  Inference rules
% 5.63/2.04  ----------------------
% 5.63/2.04  #Ref     : 0
% 5.63/2.04  #Sup     : 1617
% 5.63/2.04  #Fact    : 0
% 5.63/2.04  #Define  : 0
% 5.63/2.04  #Split   : 3
% 5.63/2.04  #Chain   : 0
% 5.63/2.04  #Close   : 0
% 5.63/2.04  
% 5.63/2.04  Ordering : KBO
% 5.63/2.04  
% 5.63/2.04  Simplification rules
% 5.63/2.04  ----------------------
% 5.63/2.04  #Subsume      : 190
% 5.63/2.04  #Demod        : 1297
% 5.63/2.04  #Tautology    : 996
% 5.63/2.04  #SimpNegUnit  : 8
% 5.63/2.04  #BackRed      : 10
% 5.63/2.04  
% 5.63/2.04  #Partial instantiations: 0
% 5.63/2.04  #Strategies tried      : 1
% 5.63/2.04  
% 5.63/2.04  Timing (in seconds)
% 5.63/2.04  ----------------------
% 5.63/2.04  Preprocessing        : 0.33
% 5.63/2.04  Parsing              : 0.18
% 5.63/2.04  CNF conversion       : 0.02
% 5.63/2.04  Main loop            : 0.95
% 5.63/2.04  Inferencing          : 0.33
% 5.63/2.04  Reduction            : 0.29
% 5.63/2.04  Demodulation         : 0.21
% 5.63/2.04  BG Simplification    : 0.04
% 5.63/2.04  Subsumption          : 0.22
% 5.63/2.05  Abstraction          : 0.05
% 5.63/2.05  MUC search           : 0.00
% 5.63/2.05  Cooper               : 0.00
% 5.63/2.05  Total                : 1.32
% 5.63/2.05  Index Insertion      : 0.00
% 5.63/2.05  Index Deletion       : 0.00
% 5.63/2.05  Index Matching       : 0.00
% 5.63/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
