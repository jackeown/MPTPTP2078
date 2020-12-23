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
% DateTime   : Thu Dec  3 10:17:39 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :  237 ( 968 expanded)
%              Number of leaves         :   44 ( 322 expanded)
%              Depth                    :   14
%              Number of atoms          :  397 (2933 expanded)
%              Number of equality atoms :  102 ( 403 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_8133,plain,(
    ! [A_777,B_778,C_779,D_780] :
      ( k2_partfun1(A_777,B_778,C_779,D_780) = k7_relat_1(C_779,D_780)
      | ~ m1_subset_1(C_779,k1_zfmisc_1(k2_zfmisc_1(A_777,B_778)))
      | ~ v1_funct_1(C_779) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8142,plain,(
    ! [D_780] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_780) = k7_relat_1('#skF_5',D_780)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_8133])).

tff(c_8150,plain,(
    ! [D_780] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_780) = k7_relat_1('#skF_5',D_780) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8142])).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_90])).

tff(c_100,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_96])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6495,plain,(
    ! [A_637,B_638,C_639,D_640] :
      ( k2_partfun1(A_637,B_638,C_639,D_640) = k7_relat_1(C_639,D_640)
      | ~ m1_subset_1(C_639,k1_zfmisc_1(k2_zfmisc_1(A_637,B_638)))
      | ~ v1_funct_1(C_639) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6504,plain,(
    ! [D_640] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_640) = k7_relat_1('#skF_5',D_640)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_6495])).

tff(c_6510,plain,(
    ! [D_640] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_640) = k7_relat_1('#skF_5',D_640) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6504])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k7_relat_1(B_18,A_17),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5448,plain,(
    ! [A_523,B_524] :
      ( v1_relat_1(A_523)
      | ~ v1_relat_1(B_524)
      | ~ r1_tarski(A_523,B_524) ) ),
    inference(resolution,[status(thm)],[c_14,c_90])).

tff(c_5464,plain,(
    ! [B_18,A_17] :
      ( v1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_28,c_5448])).

tff(c_5980,plain,(
    ! [A_573,B_574,C_575,D_576] :
      ( k7_relset_1(A_573,B_574,C_575,D_576) = k9_relat_1(C_575,D_576)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(A_573,B_574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5991,plain,(
    ! [D_577] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_577) = k9_relat_1('#skF_5',D_577) ),
    inference(resolution,[status(thm)],[c_68,c_5980])).

tff(c_66,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4138,plain,(
    ! [A_415,B_416,C_417] :
      ( k1_relset_1(A_415,B_416,C_417) = k1_relat_1(C_417)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4151,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_4138])).

tff(c_4923,plain,(
    ! [B_505,A_506,C_507] :
      ( k1_xboole_0 = B_505
      | k1_relset_1(A_506,B_505,C_507) = A_506
      | ~ v1_funct_2(C_507,A_506,B_505)
      | ~ m1_subset_1(C_507,k1_zfmisc_1(k2_zfmisc_1(A_506,B_505))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4939,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_4923])).

tff(c_4946,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4151,c_4939])).

tff(c_4947,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4946])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( k1_relat_1(k7_relat_1(B_20,A_19)) = A_19
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4970,plain,(
    ! [A_19] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_19)) = A_19
      | ~ r1_tarski(A_19,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4947,c_30])).

tff(c_5158,plain,(
    ! [A_512] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_512)) = A_512
      | ~ r1_tarski(A_512,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_4970])).

tff(c_4796,plain,(
    ! [A_495,B_496,C_497,D_498] :
      ( k2_partfun1(A_495,B_496,C_497,D_498) = k7_relat_1(C_497,D_498)
      | ~ m1_subset_1(C_497,k1_zfmisc_1(k2_zfmisc_1(A_495,B_496)))
      | ~ v1_funct_1(C_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4805,plain,(
    ! [D_498] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_498) = k7_relat_1('#skF_5',D_498)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_4796])).

tff(c_4813,plain,(
    ! [D_498] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_498) = k7_relat_1('#skF_5',D_498) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4805])).

tff(c_1222,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( k7_relset_1(A_162,B_163,C_164,D_165) = k9_relat_1(C_164,D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1232,plain,(
    ! [D_165] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_165) = k9_relat_1('#skF_5',D_165) ),
    inference(resolution,[status(thm)],[c_68,c_1222])).

tff(c_64,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1234,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1232,c_64])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1946,plain,(
    ! [A_246,B_247,C_248,D_249] :
      ( k2_partfun1(A_246,B_247,C_248,D_249) = k7_relat_1(C_248,D_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247)))
      | ~ v1_funct_1(C_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1955,plain,(
    ! [D_249] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_249) = k7_relat_1('#skF_5',D_249)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_1946])).

tff(c_1961,plain,(
    ! [D_249] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_249) = k7_relat_1('#skF_5',D_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1955])).

tff(c_855,plain,(
    ! [A_126,B_127] :
      ( v1_relat_1(A_126)
      | ~ v1_relat_1(B_127)
      | ~ r1_tarski(A_126,B_127) ) ),
    inference(resolution,[status(thm)],[c_14,c_90])).

tff(c_878,plain,(
    ! [B_18,A_17] :
      ( v1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_28,c_855])).

tff(c_1769,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( k2_partfun1(A_231,B_232,C_233,D_234) = k7_relat_1(C_233,D_234)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1778,plain,(
    ! [D_234] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_234) = k7_relat_1('#skF_5',D_234)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_1769])).

tff(c_1784,plain,(
    ! [D_234] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_234) = k7_relat_1('#skF_5',D_234) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1778])).

tff(c_1625,plain,(
    ! [C_216,A_217,B_218] :
      ( m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ r1_tarski(k2_relat_1(C_216),B_218)
      | ~ r1_tarski(k1_relat_1(C_216),A_217)
      | ~ v1_relat_1(C_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_739,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( v1_funct_1(k2_partfun1(A_115,B_116,C_117,D_118))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_746,plain,(
    ! [D_118] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_118))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_739])).

tff(c_751,plain,(
    ! [D_118] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_746])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_124,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_124])).

tff(c_755,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_854,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_755])).

tff(c_1660,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1625,c_854])).

tff(c_1686,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1660])).

tff(c_1785,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1784,c_1686])).

tff(c_1801,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_878,c_1785])).

tff(c_1805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1801])).

tff(c_1806,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1660])).

tff(c_2108,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1961,c_1961,c_1806])).

tff(c_2109,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2108])).

tff(c_2171,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2109])).

tff(c_2177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1234,c_2171])).

tff(c_2178,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2108])).

tff(c_2289,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_2178])).

tff(c_2293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2289])).

tff(c_2294,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_755])).

tff(c_4822,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4813,c_2294])).

tff(c_2295,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_755])).

tff(c_4149,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2295,c_4138])).

tff(c_4817,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4813,c_4813,c_4149])).

tff(c_4821,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4813,c_2295])).

tff(c_5085,plain,(
    ! [B_508,C_509,A_510] :
      ( k1_xboole_0 = B_508
      | v1_funct_2(C_509,A_510,B_508)
      | k1_relset_1(A_510,B_508,C_509) != A_510
      | ~ m1_subset_1(C_509,k1_zfmisc_1(k2_zfmisc_1(A_510,B_508))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5088,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_4821,c_5085])).

tff(c_5103,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4817,c_5088])).

tff(c_5104,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_4822,c_5103])).

tff(c_5111,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5104])).

tff(c_5164,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5158,c_5111])).

tff(c_5235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5164])).

tff(c_5236,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5104])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5314,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5236,c_10])).

tff(c_4453,plain,(
    ! [A_447,B_448,C_449,D_450] :
      ( k7_relset_1(A_447,B_448,C_449,D_450) = k9_relat_1(C_449,D_450)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4466,plain,(
    ! [D_450] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_450) = k9_relat_1('#skF_5',D_450) ),
    inference(resolution,[status(thm)],[c_68,c_4453])).

tff(c_101,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,
    ( k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_101])).

tff(c_775,plain,(
    ~ r1_tarski('#skF_3',k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_4468,plain,(
    ~ r1_tarski('#skF_3',k9_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4466,c_775])).

tff(c_5351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5314,c_4468])).

tff(c_5352,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4946])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_5378,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5352,c_2])).

tff(c_5380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5378])).

tff(c_5381,plain,(
    k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_5997,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5991,c_5381])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5552,plain,(
    ! [B_534,A_535] :
      ( v5_relat_1(B_534,A_535)
      | ~ r1_tarski(k2_relat_1(B_534),A_535)
      | ~ v1_relat_1(B_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5589,plain,(
    ! [B_539] :
      ( v5_relat_1(B_539,k2_relat_1(B_539))
      | ~ v1_relat_1(B_539) ) ),
    inference(resolution,[status(thm)],[c_8,c_5552])).

tff(c_6133,plain,(
    ! [B_607,A_608] :
      ( v5_relat_1(k7_relat_1(B_607,A_608),k9_relat_1(B_607,A_608))
      | ~ v1_relat_1(k7_relat_1(B_607,A_608))
      | ~ v1_relat_1(B_607) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_5589])).

tff(c_6138,plain,
    ( v5_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5997,c_6133])).

tff(c_6147,plain,
    ( v5_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_6138])).

tff(c_6158,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6147])).

tff(c_6161,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5464,c_6158])).

tff(c_6165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_6161])).

tff(c_6166,plain,(
    v5_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_6147])).

tff(c_6375,plain,(
    ! [A_626,B_627,C_628,D_629] :
      ( k2_partfun1(A_626,B_627,C_628,D_629) = k7_relat_1(C_628,D_629)
      | ~ m1_subset_1(C_628,k1_zfmisc_1(k2_zfmisc_1(A_626,B_627)))
      | ~ v1_funct_1(C_628) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6384,plain,(
    ! [D_629] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_629) = k7_relat_1('#skF_5',D_629)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_6375])).

tff(c_6390,plain,(
    ! [D_629] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_629) = k7_relat_1('#skF_5',D_629) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6384])).

tff(c_6167,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6147])).

tff(c_6281,plain,(
    ! [A_617,B_618,C_619,D_620] :
      ( k2_partfun1(A_617,B_618,C_619,D_620) = k7_relat_1(C_619,D_620)
      | ~ m1_subset_1(C_619,k1_zfmisc_1(k2_zfmisc_1(A_617,B_618)))
      | ~ v1_funct_1(C_619) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6290,plain,(
    ! [D_620] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_620) = k7_relat_1('#skF_5',D_620)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_6281])).

tff(c_6296,plain,(
    ! [D_620] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_620) = k7_relat_1('#skF_5',D_620) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6290])).

tff(c_6168,plain,(
    ! [C_609,A_610,B_611] :
      ( m1_subset_1(C_609,k1_zfmisc_1(k2_zfmisc_1(A_610,B_611)))
      | ~ r1_tarski(k2_relat_1(C_609),B_611)
      | ~ r1_tarski(k1_relat_1(C_609),A_610)
      | ~ v1_relat_1(C_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5435,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_755])).

tff(c_6203,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6168,c_5435])).

tff(c_6214,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6203])).

tff(c_6297,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6296,c_6214])).

tff(c_6303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6167,c_6297])).

tff(c_6305,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6203])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6304,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_6203])).

tff(c_6306,plain,(
    ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6304])).

tff(c_6309,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_6306])).

tff(c_6312,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6305,c_6309])).

tff(c_6392,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6390,c_6312])).

tff(c_6400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6166,c_6392])).

tff(c_6401,plain,(
    ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_6304])).

tff(c_6512,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6510,c_6401])).

tff(c_6560,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_6512])).

tff(c_6564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_6560])).

tff(c_6565,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_755])).

tff(c_8159,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8150,c_6565])).

tff(c_8634,plain,(
    ! [A_799,B_800,C_801,D_802] :
      ( m1_subset_1(k2_partfun1(A_799,B_800,C_801,D_802),k1_zfmisc_1(k2_zfmisc_1(A_799,B_800)))
      | ~ m1_subset_1(C_801,k1_zfmisc_1(k2_zfmisc_1(A_799,B_800)))
      | ~ v1_funct_1(C_801) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8655,plain,(
    ! [D_780] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_780),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8150,c_8634])).

tff(c_8756,plain,(
    ! [D_804] : m1_subset_1(k7_relat_1('#skF_5',D_804),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_8655])).

tff(c_16,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8768,plain,(
    ! [D_804] :
      ( v1_relat_1(k7_relat_1('#skF_5',D_804))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8756,c_16])).

tff(c_8782,plain,(
    ! [D_804] : v1_relat_1(k7_relat_1('#skF_5',D_804)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8768])).

tff(c_7163,plain,(
    ! [A_701,B_702,C_703,D_704] :
      ( v1_funct_1(k2_partfun1(A_701,B_702,C_703,D_704))
      | ~ m1_subset_1(C_703,k1_zfmisc_1(k2_zfmisc_1(A_701,B_702)))
      | ~ v1_funct_1(C_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_7172,plain,(
    ! [D_704] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_704))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_7163])).

tff(c_7180,plain,(
    ! [D_704] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_704)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7172])).

tff(c_8152,plain,(
    ! [D_704] : v1_funct_1(k7_relat_1('#skF_5',D_704)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8150,c_7180])).

tff(c_6867,plain,(
    ! [A_671,B_672,C_673] :
      ( k1_relset_1(A_671,B_672,C_673) = k1_relat_1(C_673)
      | ~ m1_subset_1(C_673,k1_zfmisc_1(k2_zfmisc_1(A_671,B_672))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6880,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_6867])).

tff(c_8300,plain,(
    ! [B_790,A_791,C_792] :
      ( k1_xboole_0 = B_790
      | k1_relset_1(A_791,B_790,C_792) = A_791
      | ~ v1_funct_2(C_792,A_791,B_790)
      | ~ m1_subset_1(C_792,k1_zfmisc_1(k2_zfmisc_1(A_791,B_790))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8316,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_8300])).

tff(c_8324,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6880,c_8316])).

tff(c_8325,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8324])).

tff(c_8348,plain,(
    ! [A_19] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_19)) = A_19
      | ~ r1_tarski(A_19,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8325,c_30])).

tff(c_8531,plain,(
    ! [A_798] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_798)) = A_798
      | ~ r1_tarski(A_798,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_8348])).

tff(c_6566,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_755])).

tff(c_6878,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6566,c_6867])).

tff(c_8154,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8150,c_8150,c_6878])).

tff(c_8158,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8150,c_6566])).

tff(c_8460,plain,(
    ! [B_794,C_795,A_796] :
      ( k1_xboole_0 = B_794
      | v1_funct_2(C_795,A_796,B_794)
      | k1_relset_1(A_796,B_794,C_795) != A_796
      | ~ m1_subset_1(C_795,k1_zfmisc_1(k2_zfmisc_1(A_796,B_794))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8466,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_8158,c_8460])).

tff(c_8479,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8154,c_8466])).

tff(c_8480,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_8159,c_8479])).

tff(c_8487,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8480])).

tff(c_8537,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8531,c_8487])).

tff(c_8600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8537])).

tff(c_8602,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8480])).

tff(c_6579,plain,(
    ! [A_644,B_645] :
      ( v1_relat_1(A_644)
      | ~ v1_relat_1(B_645)
      | ~ r1_tarski(A_644,B_645) ) ),
    inference(resolution,[status(thm)],[c_14,c_90])).

tff(c_6595,plain,(
    ! [B_18,A_17] :
      ( v1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_28,c_6579])).

tff(c_7013,plain,(
    ! [A_685,B_686,C_687,D_688] :
      ( k7_relset_1(A_685,B_686,C_687,D_688) = k9_relat_1(C_687,D_688)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(k2_zfmisc_1(A_685,B_686))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7027,plain,(
    ! [D_689] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_689) = k9_relat_1('#skF_5',D_689) ),
    inference(resolution,[status(thm)],[c_68,c_7013])).

tff(c_7033,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7027,c_5381])).

tff(c_6669,plain,(
    ! [B_652,A_653] :
      ( v5_relat_1(B_652,A_653)
      | ~ r1_tarski(k2_relat_1(B_652),A_653)
      | ~ v1_relat_1(B_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6699,plain,(
    ! [B_657] :
      ( v5_relat_1(B_657,k2_relat_1(B_657))
      | ~ v1_relat_1(B_657) ) ),
    inference(resolution,[status(thm)],[c_8,c_6669])).

tff(c_7272,plain,(
    ! [B_721,A_722] :
      ( v5_relat_1(k7_relat_1(B_721,A_722),k9_relat_1(B_721,A_722))
      | ~ v1_relat_1(k7_relat_1(B_721,A_722))
      | ~ v1_relat_1(B_721) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6699])).

tff(c_7277,plain,
    ( v5_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7033,c_7272])).

tff(c_7286,plain,
    ( v5_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_7277])).

tff(c_7303,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7286])).

tff(c_7306,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6595,c_7303])).

tff(c_7310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_7306])).

tff(c_7311,plain,(
    v5_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_7286])).

tff(c_8601,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8480])).

tff(c_6703,plain,(
    ! [B_658,A_659] :
      ( r1_tarski(k2_relat_1(B_658),A_659)
      | ~ v5_relat_1(B_658,A_659)
      | ~ v1_relat_1(B_658) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_6721,plain,(
    ! [B_658] :
      ( k2_relat_1(B_658) = k1_xboole_0
      | ~ v5_relat_1(B_658,k1_xboole_0)
      | ~ v1_relat_1(B_658) ) ),
    inference(resolution,[status(thm)],[c_6703,c_122])).

tff(c_9378,plain,(
    ! [B_831] :
      ( k2_relat_1(B_831) = '#skF_3'
      | ~ v5_relat_1(B_831,'#skF_3')
      | ~ v1_relat_1(B_831) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8601,c_8601,c_6721])).

tff(c_9381,plain,
    ( k2_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_3'
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_7311,c_9378])).

tff(c_9384,plain,(
    k2_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8782,c_9381])).

tff(c_58,plain,(
    ! [A_42] :
      ( v1_funct_2(A_42,k1_relat_1(A_42),k2_relat_1(A_42))
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_9413,plain,
    ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9384,c_58])).

tff(c_9448,plain,(
    v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8782,c_8152,c_8602,c_9413])).

tff(c_9450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8159,c_9448])).

tff(c_9451,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8324])).

tff(c_9503,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9451,c_2])).

tff(c_9505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_9503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:17 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.47/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.68  
% 7.47/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.68  %$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.47/2.68  
% 7.47/2.68  %Foreground sorts:
% 7.47/2.68  
% 7.47/2.68  
% 7.47/2.68  %Background operators:
% 7.47/2.68  
% 7.47/2.68  
% 7.47/2.68  %Foreground operators:
% 7.47/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.47/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.47/2.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.47/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.47/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.47/2.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.47/2.68  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.47/2.68  tff('#skF_5', type, '#skF_5': $i).
% 7.47/2.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.47/2.68  tff('#skF_2', type, '#skF_2': $i).
% 7.47/2.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.47/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.47/2.68  tff('#skF_1', type, '#skF_1': $i).
% 7.47/2.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.47/2.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.47/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.47/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.47/2.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.47/2.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.47/2.68  tff('#skF_4', type, '#skF_4': $i).
% 7.47/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.47/2.68  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.47/2.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.47/2.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.47/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.47/2.68  
% 7.76/2.71  tff(f_150, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_funct_2)).
% 7.76/2.71  tff(f_119, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.76/2.71  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.76/2.71  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.76/2.71  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 7.76/2.71  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 7.76/2.71  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.76/2.71  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.76/2.71  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.76/2.71  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.76/2.71  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 7.76/2.71  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 7.76/2.71  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.76/2.71  tff(f_113, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 7.76/2.71  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.76/2.71  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.76/2.71  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.76/2.71  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.76/2.71  tff(f_129, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.76/2.71  tff(c_74, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.76/2.71  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.76/2.71  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.76/2.71  tff(c_8133, plain, (![A_777, B_778, C_779, D_780]: (k2_partfun1(A_777, B_778, C_779, D_780)=k7_relat_1(C_779, D_780) | ~m1_subset_1(C_779, k1_zfmisc_1(k2_zfmisc_1(A_777, B_778))) | ~v1_funct_1(C_779))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.76/2.71  tff(c_8142, plain, (![D_780]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_780)=k7_relat_1('#skF_5', D_780) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_8133])).
% 7.76/2.71  tff(c_8150, plain, (![D_780]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_780)=k7_relat_1('#skF_5', D_780))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8142])).
% 7.76/2.71  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.76/2.71  tff(c_90, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.76/2.71  tff(c_96, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_90])).
% 7.76/2.71  tff(c_100, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_96])).
% 7.76/2.71  tff(c_26, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.76/2.71  tff(c_6495, plain, (![A_637, B_638, C_639, D_640]: (k2_partfun1(A_637, B_638, C_639, D_640)=k7_relat_1(C_639, D_640) | ~m1_subset_1(C_639, k1_zfmisc_1(k2_zfmisc_1(A_637, B_638))) | ~v1_funct_1(C_639))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.76/2.71  tff(c_6504, plain, (![D_640]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_640)=k7_relat_1('#skF_5', D_640) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_6495])).
% 7.76/2.71  tff(c_6510, plain, (![D_640]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_640)=k7_relat_1('#skF_5', D_640))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6504])).
% 7.76/2.71  tff(c_28, plain, (![B_18, A_17]: (r1_tarski(k7_relat_1(B_18, A_17), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.76/2.71  tff(c_14, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.76/2.71  tff(c_5448, plain, (![A_523, B_524]: (v1_relat_1(A_523) | ~v1_relat_1(B_524) | ~r1_tarski(A_523, B_524))), inference(resolution, [status(thm)], [c_14, c_90])).
% 7.76/2.71  tff(c_5464, plain, (![B_18, A_17]: (v1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_28, c_5448])).
% 7.76/2.71  tff(c_5980, plain, (![A_573, B_574, C_575, D_576]: (k7_relset_1(A_573, B_574, C_575, D_576)=k9_relat_1(C_575, D_576) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1(A_573, B_574))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.76/2.71  tff(c_5991, plain, (![D_577]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_577)=k9_relat_1('#skF_5', D_577))), inference(resolution, [status(thm)], [c_68, c_5980])).
% 7.76/2.71  tff(c_66, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.76/2.71  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.76/2.71  tff(c_4138, plain, (![A_415, B_416, C_417]: (k1_relset_1(A_415, B_416, C_417)=k1_relat_1(C_417) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.76/2.71  tff(c_4151, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_4138])).
% 7.76/2.71  tff(c_4923, plain, (![B_505, A_506, C_507]: (k1_xboole_0=B_505 | k1_relset_1(A_506, B_505, C_507)=A_506 | ~v1_funct_2(C_507, A_506, B_505) | ~m1_subset_1(C_507, k1_zfmisc_1(k2_zfmisc_1(A_506, B_505))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.76/2.71  tff(c_4939, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_4923])).
% 7.76/2.71  tff(c_4946, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4151, c_4939])).
% 7.76/2.71  tff(c_4947, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_4946])).
% 7.76/2.71  tff(c_30, plain, (![B_20, A_19]: (k1_relat_1(k7_relat_1(B_20, A_19))=A_19 | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.76/2.71  tff(c_4970, plain, (![A_19]: (k1_relat_1(k7_relat_1('#skF_5', A_19))=A_19 | ~r1_tarski(A_19, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4947, c_30])).
% 7.76/2.71  tff(c_5158, plain, (![A_512]: (k1_relat_1(k7_relat_1('#skF_5', A_512))=A_512 | ~r1_tarski(A_512, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_4970])).
% 7.76/2.71  tff(c_4796, plain, (![A_495, B_496, C_497, D_498]: (k2_partfun1(A_495, B_496, C_497, D_498)=k7_relat_1(C_497, D_498) | ~m1_subset_1(C_497, k1_zfmisc_1(k2_zfmisc_1(A_495, B_496))) | ~v1_funct_1(C_497))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.76/2.71  tff(c_4805, plain, (![D_498]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_498)=k7_relat_1('#skF_5', D_498) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_4796])).
% 7.76/2.71  tff(c_4813, plain, (![D_498]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_498)=k7_relat_1('#skF_5', D_498))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4805])).
% 7.76/2.71  tff(c_1222, plain, (![A_162, B_163, C_164, D_165]: (k7_relset_1(A_162, B_163, C_164, D_165)=k9_relat_1(C_164, D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.76/2.71  tff(c_1232, plain, (![D_165]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_165)=k9_relat_1('#skF_5', D_165))), inference(resolution, [status(thm)], [c_68, c_1222])).
% 7.76/2.71  tff(c_64, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.76/2.71  tff(c_1234, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1232, c_64])).
% 7.76/2.71  tff(c_24, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.76/2.71  tff(c_1946, plain, (![A_246, B_247, C_248, D_249]: (k2_partfun1(A_246, B_247, C_248, D_249)=k7_relat_1(C_248, D_249) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))) | ~v1_funct_1(C_248))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.76/2.71  tff(c_1955, plain, (![D_249]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_249)=k7_relat_1('#skF_5', D_249) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_1946])).
% 7.76/2.71  tff(c_1961, plain, (![D_249]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_249)=k7_relat_1('#skF_5', D_249))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1955])).
% 7.76/2.71  tff(c_855, plain, (![A_126, B_127]: (v1_relat_1(A_126) | ~v1_relat_1(B_127) | ~r1_tarski(A_126, B_127))), inference(resolution, [status(thm)], [c_14, c_90])).
% 7.76/2.71  tff(c_878, plain, (![B_18, A_17]: (v1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_28, c_855])).
% 7.76/2.71  tff(c_1769, plain, (![A_231, B_232, C_233, D_234]: (k2_partfun1(A_231, B_232, C_233, D_234)=k7_relat_1(C_233, D_234) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))) | ~v1_funct_1(C_233))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.76/2.71  tff(c_1778, plain, (![D_234]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_234)=k7_relat_1('#skF_5', D_234) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_1769])).
% 7.76/2.71  tff(c_1784, plain, (![D_234]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_234)=k7_relat_1('#skF_5', D_234))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1778])).
% 7.76/2.71  tff(c_1625, plain, (![C_216, A_217, B_218]: (m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~r1_tarski(k2_relat_1(C_216), B_218) | ~r1_tarski(k1_relat_1(C_216), A_217) | ~v1_relat_1(C_216))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.76/2.71  tff(c_739, plain, (![A_115, B_116, C_117, D_118]: (v1_funct_1(k2_partfun1(A_115, B_116, C_117, D_118)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(C_117))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.76/2.71  tff(c_746, plain, (![D_118]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_118)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_739])).
% 7.76/2.71  tff(c_751, plain, (![D_118]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_118)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_746])).
% 7.76/2.71  tff(c_62, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.76/2.71  tff(c_124, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_62])).
% 7.76/2.71  tff(c_754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_751, c_124])).
% 7.76/2.71  tff(c_755, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_62])).
% 7.76/2.71  tff(c_854, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_755])).
% 7.76/2.71  tff(c_1660, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_1625, c_854])).
% 7.76/2.71  tff(c_1686, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1660])).
% 7.76/2.71  tff(c_1785, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1784, c_1686])).
% 7.76/2.71  tff(c_1801, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_878, c_1785])).
% 7.76/2.71  tff(c_1805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_1801])).
% 7.76/2.71  tff(c_1806, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_1660])).
% 7.76/2.71  tff(c_2108, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1961, c_1961, c_1806])).
% 7.76/2.71  tff(c_2109, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_2108])).
% 7.76/2.71  tff(c_2171, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_24, c_2109])).
% 7.76/2.71  tff(c_2177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_1234, c_2171])).
% 7.76/2.71  tff(c_2178, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_2108])).
% 7.76/2.71  tff(c_2289, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_2178])).
% 7.76/2.71  tff(c_2293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_2289])).
% 7.76/2.71  tff(c_2294, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_755])).
% 7.76/2.71  tff(c_4822, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4813, c_2294])).
% 7.76/2.71  tff(c_2295, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_755])).
% 7.76/2.71  tff(c_4149, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_2295, c_4138])).
% 7.76/2.71  tff(c_4817, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4813, c_4813, c_4149])).
% 7.76/2.71  tff(c_4821, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4813, c_2295])).
% 7.76/2.71  tff(c_5085, plain, (![B_508, C_509, A_510]: (k1_xboole_0=B_508 | v1_funct_2(C_509, A_510, B_508) | k1_relset_1(A_510, B_508, C_509)!=A_510 | ~m1_subset_1(C_509, k1_zfmisc_1(k2_zfmisc_1(A_510, B_508))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.76/2.72  tff(c_5088, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_4821, c_5085])).
% 7.76/2.72  tff(c_5103, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4817, c_5088])).
% 7.76/2.72  tff(c_5104, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_4822, c_5103])).
% 7.76/2.72  tff(c_5111, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_5104])).
% 7.76/2.72  tff(c_5164, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5158, c_5111])).
% 7.76/2.72  tff(c_5235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_5164])).
% 7.76/2.72  tff(c_5236, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5104])).
% 7.76/2.72  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.76/2.72  tff(c_5314, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5236, c_10])).
% 7.76/2.72  tff(c_4453, plain, (![A_447, B_448, C_449, D_450]: (k7_relset_1(A_447, B_448, C_449, D_450)=k9_relat_1(C_449, D_450) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.76/2.72  tff(c_4466, plain, (![D_450]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_450)=k9_relat_1('#skF_5', D_450))), inference(resolution, [status(thm)], [c_68, c_4453])).
% 7.76/2.72  tff(c_101, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.76/2.72  tff(c_116, plain, (k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_101])).
% 7.76/2.72  tff(c_775, plain, (~r1_tarski('#skF_3', k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_116])).
% 7.76/2.72  tff(c_4468, plain, (~r1_tarski('#skF_3', k9_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4466, c_775])).
% 7.76/2.72  tff(c_5351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5314, c_4468])).
% 7.76/2.72  tff(c_5352, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4946])).
% 7.76/2.72  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.76/2.72  tff(c_5378, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5352, c_2])).
% 7.76/2.72  tff(c_5380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_5378])).
% 7.76/2.72  tff(c_5381, plain, (k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_116])).
% 7.76/2.72  tff(c_5997, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5991, c_5381])).
% 7.76/2.72  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.76/2.72  tff(c_5552, plain, (![B_534, A_535]: (v5_relat_1(B_534, A_535) | ~r1_tarski(k2_relat_1(B_534), A_535) | ~v1_relat_1(B_534))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.76/2.72  tff(c_5589, plain, (![B_539]: (v5_relat_1(B_539, k2_relat_1(B_539)) | ~v1_relat_1(B_539))), inference(resolution, [status(thm)], [c_8, c_5552])).
% 7.76/2.72  tff(c_6133, plain, (![B_607, A_608]: (v5_relat_1(k7_relat_1(B_607, A_608), k9_relat_1(B_607, A_608)) | ~v1_relat_1(k7_relat_1(B_607, A_608)) | ~v1_relat_1(B_607))), inference(superposition, [status(thm), theory('equality')], [c_24, c_5589])).
% 7.76/2.72  tff(c_6138, plain, (v5_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5997, c_6133])).
% 7.76/2.72  tff(c_6147, plain, (v5_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_6138])).
% 7.76/2.72  tff(c_6158, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_6147])).
% 7.76/2.72  tff(c_6161, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5464, c_6158])).
% 7.76/2.72  tff(c_6165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_6161])).
% 7.76/2.72  tff(c_6166, plain, (v5_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_6147])).
% 7.76/2.72  tff(c_6375, plain, (![A_626, B_627, C_628, D_629]: (k2_partfun1(A_626, B_627, C_628, D_629)=k7_relat_1(C_628, D_629) | ~m1_subset_1(C_628, k1_zfmisc_1(k2_zfmisc_1(A_626, B_627))) | ~v1_funct_1(C_628))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.76/2.72  tff(c_6384, plain, (![D_629]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_629)=k7_relat_1('#skF_5', D_629) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_6375])).
% 7.76/2.72  tff(c_6390, plain, (![D_629]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_629)=k7_relat_1('#skF_5', D_629))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6384])).
% 7.76/2.72  tff(c_6167, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitRight, [status(thm)], [c_6147])).
% 7.76/2.72  tff(c_6281, plain, (![A_617, B_618, C_619, D_620]: (k2_partfun1(A_617, B_618, C_619, D_620)=k7_relat_1(C_619, D_620) | ~m1_subset_1(C_619, k1_zfmisc_1(k2_zfmisc_1(A_617, B_618))) | ~v1_funct_1(C_619))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.76/2.72  tff(c_6290, plain, (![D_620]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_620)=k7_relat_1('#skF_5', D_620) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_6281])).
% 7.76/2.72  tff(c_6296, plain, (![D_620]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_620)=k7_relat_1('#skF_5', D_620))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6290])).
% 7.76/2.72  tff(c_6168, plain, (![C_609, A_610, B_611]: (m1_subset_1(C_609, k1_zfmisc_1(k2_zfmisc_1(A_610, B_611))) | ~r1_tarski(k2_relat_1(C_609), B_611) | ~r1_tarski(k1_relat_1(C_609), A_610) | ~v1_relat_1(C_609))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.76/2.72  tff(c_5435, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_755])).
% 7.76/2.72  tff(c_6203, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_6168, c_5435])).
% 7.76/2.72  tff(c_6214, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_6203])).
% 7.76/2.72  tff(c_6297, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6296, c_6214])).
% 7.76/2.72  tff(c_6303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6167, c_6297])).
% 7.76/2.72  tff(c_6305, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitRight, [status(thm)], [c_6203])).
% 7.76/2.72  tff(c_20, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.76/2.72  tff(c_6304, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_6203])).
% 7.76/2.72  tff(c_6306, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_6304])).
% 7.76/2.72  tff(c_6309, plain, (~v5_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_6306])).
% 7.76/2.72  tff(c_6312, plain, (~v5_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6305, c_6309])).
% 7.76/2.72  tff(c_6392, plain, (~v5_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6390, c_6312])).
% 7.76/2.72  tff(c_6400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6166, c_6392])).
% 7.76/2.72  tff(c_6401, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_6304])).
% 7.76/2.72  tff(c_6512, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6510, c_6401])).
% 7.76/2.72  tff(c_6560, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_6512])).
% 7.76/2.72  tff(c_6564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_6560])).
% 7.76/2.72  tff(c_6565, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_755])).
% 7.76/2.72  tff(c_8159, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8150, c_6565])).
% 7.76/2.72  tff(c_8634, plain, (![A_799, B_800, C_801, D_802]: (m1_subset_1(k2_partfun1(A_799, B_800, C_801, D_802), k1_zfmisc_1(k2_zfmisc_1(A_799, B_800))) | ~m1_subset_1(C_801, k1_zfmisc_1(k2_zfmisc_1(A_799, B_800))) | ~v1_funct_1(C_801))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.76/2.72  tff(c_8655, plain, (![D_780]: (m1_subset_1(k7_relat_1('#skF_5', D_780), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8150, c_8634])).
% 7.76/2.72  tff(c_8756, plain, (![D_804]: (m1_subset_1(k7_relat_1('#skF_5', D_804), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_8655])).
% 7.76/2.72  tff(c_16, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.76/2.72  tff(c_8768, plain, (![D_804]: (v1_relat_1(k7_relat_1('#skF_5', D_804)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(resolution, [status(thm)], [c_8756, c_16])).
% 7.76/2.72  tff(c_8782, plain, (![D_804]: (v1_relat_1(k7_relat_1('#skF_5', D_804)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8768])).
% 7.76/2.72  tff(c_7163, plain, (![A_701, B_702, C_703, D_704]: (v1_funct_1(k2_partfun1(A_701, B_702, C_703, D_704)) | ~m1_subset_1(C_703, k1_zfmisc_1(k2_zfmisc_1(A_701, B_702))) | ~v1_funct_1(C_703))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.76/2.72  tff(c_7172, plain, (![D_704]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_704)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_7163])).
% 7.76/2.72  tff(c_7180, plain, (![D_704]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_704)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_7172])).
% 7.76/2.72  tff(c_8152, plain, (![D_704]: (v1_funct_1(k7_relat_1('#skF_5', D_704)))), inference(demodulation, [status(thm), theory('equality')], [c_8150, c_7180])).
% 7.76/2.72  tff(c_6867, plain, (![A_671, B_672, C_673]: (k1_relset_1(A_671, B_672, C_673)=k1_relat_1(C_673) | ~m1_subset_1(C_673, k1_zfmisc_1(k2_zfmisc_1(A_671, B_672))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.76/2.72  tff(c_6880, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_6867])).
% 7.76/2.72  tff(c_8300, plain, (![B_790, A_791, C_792]: (k1_xboole_0=B_790 | k1_relset_1(A_791, B_790, C_792)=A_791 | ~v1_funct_2(C_792, A_791, B_790) | ~m1_subset_1(C_792, k1_zfmisc_1(k2_zfmisc_1(A_791, B_790))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.76/2.72  tff(c_8316, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_8300])).
% 7.76/2.72  tff(c_8324, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6880, c_8316])).
% 7.76/2.72  tff(c_8325, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_8324])).
% 7.76/2.72  tff(c_8348, plain, (![A_19]: (k1_relat_1(k7_relat_1('#skF_5', A_19))=A_19 | ~r1_tarski(A_19, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8325, c_30])).
% 7.76/2.72  tff(c_8531, plain, (![A_798]: (k1_relat_1(k7_relat_1('#skF_5', A_798))=A_798 | ~r1_tarski(A_798, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_8348])).
% 7.76/2.72  tff(c_6566, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_755])).
% 7.76/2.72  tff(c_6878, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_6566, c_6867])).
% 7.76/2.72  tff(c_8154, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8150, c_8150, c_6878])).
% 7.76/2.72  tff(c_8158, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8150, c_6566])).
% 7.76/2.72  tff(c_8460, plain, (![B_794, C_795, A_796]: (k1_xboole_0=B_794 | v1_funct_2(C_795, A_796, B_794) | k1_relset_1(A_796, B_794, C_795)!=A_796 | ~m1_subset_1(C_795, k1_zfmisc_1(k2_zfmisc_1(A_796, B_794))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.76/2.72  tff(c_8466, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_8158, c_8460])).
% 7.76/2.72  tff(c_8479, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8154, c_8466])).
% 7.76/2.72  tff(c_8480, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_8159, c_8479])).
% 7.76/2.72  tff(c_8487, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_8480])).
% 7.76/2.72  tff(c_8537, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8531, c_8487])).
% 7.76/2.72  tff(c_8600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_8537])).
% 7.76/2.72  tff(c_8602, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(splitRight, [status(thm)], [c_8480])).
% 7.76/2.72  tff(c_6579, plain, (![A_644, B_645]: (v1_relat_1(A_644) | ~v1_relat_1(B_645) | ~r1_tarski(A_644, B_645))), inference(resolution, [status(thm)], [c_14, c_90])).
% 7.76/2.72  tff(c_6595, plain, (![B_18, A_17]: (v1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_28, c_6579])).
% 7.76/2.72  tff(c_7013, plain, (![A_685, B_686, C_687, D_688]: (k7_relset_1(A_685, B_686, C_687, D_688)=k9_relat_1(C_687, D_688) | ~m1_subset_1(C_687, k1_zfmisc_1(k2_zfmisc_1(A_685, B_686))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.76/2.72  tff(c_7027, plain, (![D_689]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_689)=k9_relat_1('#skF_5', D_689))), inference(resolution, [status(thm)], [c_68, c_7013])).
% 7.76/2.72  tff(c_7033, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7027, c_5381])).
% 7.76/2.72  tff(c_6669, plain, (![B_652, A_653]: (v5_relat_1(B_652, A_653) | ~r1_tarski(k2_relat_1(B_652), A_653) | ~v1_relat_1(B_652))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.76/2.72  tff(c_6699, plain, (![B_657]: (v5_relat_1(B_657, k2_relat_1(B_657)) | ~v1_relat_1(B_657))), inference(resolution, [status(thm)], [c_8, c_6669])).
% 7.76/2.72  tff(c_7272, plain, (![B_721, A_722]: (v5_relat_1(k7_relat_1(B_721, A_722), k9_relat_1(B_721, A_722)) | ~v1_relat_1(k7_relat_1(B_721, A_722)) | ~v1_relat_1(B_721))), inference(superposition, [status(thm), theory('equality')], [c_24, c_6699])).
% 7.76/2.72  tff(c_7277, plain, (v5_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7033, c_7272])).
% 7.76/2.72  tff(c_7286, plain, (v5_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_7277])).
% 7.76/2.72  tff(c_7303, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_7286])).
% 7.76/2.72  tff(c_7306, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6595, c_7303])).
% 7.76/2.72  tff(c_7310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_7306])).
% 7.76/2.72  tff(c_7311, plain, (v5_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_7286])).
% 7.76/2.72  tff(c_8601, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_8480])).
% 7.76/2.72  tff(c_6703, plain, (![B_658, A_659]: (r1_tarski(k2_relat_1(B_658), A_659) | ~v5_relat_1(B_658, A_659) | ~v1_relat_1(B_658))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.76/2.72  tff(c_122, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_101])).
% 7.76/2.72  tff(c_6721, plain, (![B_658]: (k2_relat_1(B_658)=k1_xboole_0 | ~v5_relat_1(B_658, k1_xboole_0) | ~v1_relat_1(B_658))), inference(resolution, [status(thm)], [c_6703, c_122])).
% 7.76/2.72  tff(c_9378, plain, (![B_831]: (k2_relat_1(B_831)='#skF_3' | ~v5_relat_1(B_831, '#skF_3') | ~v1_relat_1(B_831))), inference(demodulation, [status(thm), theory('equality')], [c_8601, c_8601, c_6721])).
% 7.76/2.72  tff(c_9381, plain, (k2_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_3' | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_7311, c_9378])).
% 7.76/2.72  tff(c_9384, plain, (k2_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8782, c_9381])).
% 7.76/2.72  tff(c_58, plain, (![A_42]: (v1_funct_2(A_42, k1_relat_1(A_42), k2_relat_1(A_42)) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.76/2.72  tff(c_9413, plain, (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~v1_funct_1(k7_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9384, c_58])).
% 7.76/2.72  tff(c_9448, plain, (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8782, c_8152, c_8602, c_9413])).
% 7.76/2.72  tff(c_9450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8159, c_9448])).
% 7.76/2.72  tff(c_9451, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_8324])).
% 7.76/2.72  tff(c_9503, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9451, c_2])).
% 7.76/2.72  tff(c_9505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_9503])).
% 7.76/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/2.72  
% 7.76/2.72  Inference rules
% 7.76/2.72  ----------------------
% 7.76/2.72  #Ref     : 0
% 7.76/2.72  #Sup     : 1987
% 7.76/2.72  #Fact    : 0
% 7.76/2.72  #Define  : 0
% 7.76/2.72  #Split   : 51
% 7.76/2.72  #Chain   : 0
% 7.76/2.72  #Close   : 0
% 7.76/2.72  
% 7.76/2.72  Ordering : KBO
% 7.76/2.72  
% 7.76/2.72  Simplification rules
% 7.76/2.72  ----------------------
% 7.76/2.72  #Subsume      : 208
% 7.76/2.72  #Demod        : 1874
% 7.76/2.72  #Tautology    : 676
% 7.76/2.72  #SimpNegUnit  : 35
% 7.76/2.72  #BackRed      : 295
% 7.76/2.72  
% 7.76/2.72  #Partial instantiations: 0
% 7.76/2.72  #Strategies tried      : 1
% 7.76/2.72  
% 7.76/2.72  Timing (in seconds)
% 7.76/2.72  ----------------------
% 7.76/2.72  Preprocessing        : 0.35
% 7.76/2.72  Parsing              : 0.19
% 7.76/2.72  CNF conversion       : 0.02
% 7.76/2.72  Main loop            : 1.57
% 7.76/2.72  Inferencing          : 0.54
% 7.76/2.72  Reduction            : 0.54
% 7.76/2.72  Demodulation         : 0.39
% 7.76/2.72  BG Simplification    : 0.07
% 7.76/2.72  Subsumption          : 0.29
% 7.76/2.72  Abstraction          : 0.08
% 7.76/2.72  MUC search           : 0.00
% 7.76/2.72  Cooper               : 0.00
% 7.76/2.72  Total                : 1.98
% 7.76/2.72  Index Insertion      : 0.00
% 7.76/2.72  Index Deletion       : 0.00
% 7.76/2.72  Index Matching       : 0.00
% 7.76/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
