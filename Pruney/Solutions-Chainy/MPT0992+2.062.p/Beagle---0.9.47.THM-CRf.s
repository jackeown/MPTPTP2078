%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:40 EST 2020

% Result     : Theorem 16.60s
% Output     : CNFRefutation 16.78s
% Verified   : 
% Statistics : Number of formulae       :  229 (2377 expanded)
%              Number of leaves         :   45 ( 746 expanded)
%              Depth                    :   16
%              Number of atoms          :  390 (7223 expanded)
%              Number of equality atoms :   95 (2617 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_212,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_88,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_144,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_174,axiom,(
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

tff(f_118,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_180,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_140,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_192,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_150,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_94,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_38,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_96,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_33482,plain,(
    ! [B_1082,A_1083] :
      ( v1_relat_1(B_1082)
      | ~ m1_subset_1(B_1082,k1_zfmisc_1(A_1083))
      | ~ v1_relat_1(A_1083) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_33488,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_96,c_33482])).

tff(c_33495,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_33488])).

tff(c_92,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_106,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_98,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_36358,plain,(
    ! [A_1231,B_1232,C_1233] :
      ( k1_relset_1(A_1231,B_1232,C_1233) = k1_relat_1(C_1233)
      | ~ m1_subset_1(C_1233,k1_zfmisc_1(k2_zfmisc_1(A_1231,B_1232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_36381,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_36358])).

tff(c_39256,plain,(
    ! [B_1339,A_1340,C_1341] :
      ( k1_xboole_0 = B_1339
      | k1_relset_1(A_1340,B_1339,C_1341) = A_1340
      | ~ v1_funct_2(C_1341,A_1340,B_1339)
      | ~ m1_subset_1(C_1341,k1_zfmisc_1(k2_zfmisc_1(A_1340,B_1339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_39275,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_39256])).

tff(c_39292,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_36381,c_39275])).

tff(c_39293,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_39292])).

tff(c_50,plain,(
    ! [B_39,A_38] :
      ( k1_relat_1(k7_relat_1(B_39,A_38)) = A_38
      | ~ r1_tarski(A_38,k1_relat_1(B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_39354,plain,(
    ! [A_38] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_38)) = A_38
      | ~ r1_tarski(A_38,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39293,c_50])).

tff(c_39397,plain,(
    ! [A_38] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_38)) = A_38
      | ~ r1_tarski(A_38,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33495,c_39354])).

tff(c_100,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_38779,plain,(
    ! [A_1320,B_1321,C_1322,D_1323] :
      ( k2_partfun1(A_1320,B_1321,C_1322,D_1323) = k7_relat_1(C_1322,D_1323)
      | ~ m1_subset_1(C_1322,k1_zfmisc_1(k2_zfmisc_1(A_1320,B_1321)))
      | ~ v1_funct_1(C_1322) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_38790,plain,(
    ! [D_1323] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1323) = k7_relat_1('#skF_4',D_1323)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_96,c_38779])).

tff(c_38803,plain,(
    ! [D_1323] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1323) = k7_relat_1('#skF_4',D_1323) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_38790])).

tff(c_7009,plain,(
    ! [C_428,B_429,A_430] :
      ( v5_relat_1(C_428,B_429)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_430,B_429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_7028,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_7009])).

tff(c_5812,plain,(
    ! [B_357,A_358] :
      ( v1_relat_1(B_357)
      | ~ m1_subset_1(B_357,k1_zfmisc_1(A_358))
      | ~ v1_relat_1(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5818,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_96,c_5812])).

tff(c_5825,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5818])).

tff(c_46,plain,(
    ! [B_35,A_34] :
      ( r1_tarski(k7_relat_1(B_35,A_34),B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5705,plain,(
    ! [A_345,B_346] :
      ( r1_tarski(A_345,B_346)
      | ~ m1_subset_1(A_345,k1_zfmisc_1(B_346)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5716,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_96,c_5705])).

tff(c_5924,plain,(
    ! [A_370,C_371,B_372] :
      ( r1_tarski(A_370,C_371)
      | ~ r1_tarski(B_372,C_371)
      | ~ r1_tarski(A_370,B_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6190,plain,(
    ! [A_393] :
      ( r1_tarski(A_393,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_393,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5716,c_5924])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5822,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(A_8)
      | ~ v1_relat_1(B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_5812])).

tff(c_6202,plain,(
    ! [A_393] :
      ( v1_relat_1(A_393)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_393,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6190,c_5822])).

tff(c_6244,plain,(
    ! [A_396] :
      ( v1_relat_1(A_396)
      | ~ r1_tarski(A_396,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6202])).

tff(c_6263,plain,(
    ! [A_34] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_34))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_6244])).

tff(c_6274,plain,(
    ! [A_34] : v1_relat_1(k7_relat_1('#skF_4',A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_6263])).

tff(c_5890,plain,(
    ! [C_365,A_366,B_367] :
      ( v4_relat_1(C_365,A_366)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5909,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_96,c_5890])).

tff(c_7817,plain,(
    ! [C_483,A_484,B_485] :
      ( v4_relat_1(k7_relat_1(C_483,A_484),A_484)
      | ~ v4_relat_1(C_483,B_485)
      | ~ v1_relat_1(C_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7847,plain,(
    ! [A_484] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_484),A_484)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5909,c_7817])).

tff(c_7877,plain,(
    ! [A_486] : v4_relat_1(k7_relat_1('#skF_4',A_486),A_486) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_7847])).

tff(c_42,plain,(
    ! [B_31,A_30] :
      ( k7_relat_1(B_31,A_30) = B_31
      | ~ v4_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7890,plain,(
    ! [A_486] :
      ( k7_relat_1(k7_relat_1('#skF_4',A_486),A_486) = k7_relat_1('#skF_4',A_486)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_486)) ) ),
    inference(resolution,[status(thm)],[c_7877,c_42])).

tff(c_8324,plain,(
    ! [A_501] : k7_relat_1(k7_relat_1('#skF_4',A_501),A_501) = k7_relat_1('#skF_4',A_501) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6274,c_7890])).

tff(c_54,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_42,A_41)),k2_relat_1(B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8378,plain,(
    ! [A_501] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_501)),k2_relat_1(k7_relat_1('#skF_4',A_501)))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_501)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8324,c_54])).

tff(c_8438,plain,(
    ! [A_501] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_501)),k2_relat_1(k7_relat_1('#skF_4',A_501))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6274,c_8378])).

tff(c_17362,plain,(
    ! [A_751,B_752,A_753] :
      ( r1_tarski(A_751,k2_relat_1(B_752))
      | ~ r1_tarski(A_751,k2_relat_1(k7_relat_1(B_752,A_753)))
      | ~ v1_relat_1(B_752) ) ),
    inference(resolution,[status(thm)],[c_54,c_5924])).

tff(c_17401,plain,(
    ! [A_501] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_501)),k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8438,c_17362])).

tff(c_17542,plain,(
    ! [A_754] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_754)),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_17401])).

tff(c_7114,plain,(
    ! [B_442,A_443] :
      ( r1_tarski(k2_relat_1(B_442),A_443)
      | ~ v5_relat_1(B_442,A_443)
      | ~ v1_relat_1(B_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7164,plain,(
    ! [A_1,A_443,B_442] :
      ( r1_tarski(A_1,A_443)
      | ~ r1_tarski(A_1,k2_relat_1(B_442))
      | ~ v5_relat_1(B_442,A_443)
      | ~ v1_relat_1(B_442) ) ),
    inference(resolution,[status(thm)],[c_7114,c_2])).

tff(c_17544,plain,(
    ! [A_754,A_443] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_754)),A_443)
      | ~ v5_relat_1('#skF_4',A_443)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_17542,c_7164])).

tff(c_17568,plain,(
    ! [A_754,A_443] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_754)),A_443)
      | ~ v5_relat_1('#skF_4',A_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_17544])).

tff(c_11718,plain,(
    ! [A_618,B_619,C_620,D_621] :
      ( k2_partfun1(A_618,B_619,C_620,D_621) = k7_relat_1(C_620,D_621)
      | ~ m1_subset_1(C_620,k1_zfmisc_1(k2_zfmisc_1(A_618,B_619)))
      | ~ v1_funct_1(C_620) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_11729,plain,(
    ! [D_621] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_621) = k7_relat_1('#skF_4',D_621)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_96,c_11718])).

tff(c_11742,plain,(
    ! [D_621] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_621) = k7_relat_1('#skF_4',D_621) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_11729])).

tff(c_303,plain,(
    ! [B_95,A_96] :
      ( v1_relat_1(B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_96))
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_309,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_96,c_303])).

tff(c_316,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_309])).

tff(c_56,plain,(
    ! [A_43,B_44] :
      ( v1_funct_1(k7_relat_1(A_43,B_44))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_5663,plain,(
    ! [A_340,B_341,C_342,D_343] :
      ( k2_partfun1(A_340,B_341,C_342,D_343) = k7_relat_1(C_342,D_343)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(A_340,B_341)))
      | ~ v1_funct_1(C_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_5672,plain,(
    ! [D_343] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_343) = k7_relat_1('#skF_4',D_343)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_96,c_5663])).

tff(c_5682,plain,(
    ! [D_343] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_343) = k7_relat_1('#skF_4',D_343) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_5672])).

tff(c_90,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_199,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_5685,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5682,c_199])).

tff(c_5697,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_5685])).

tff(c_5701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_100,c_5697])).

tff(c_5703,plain,(
    v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_11748,plain,(
    v1_funct_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11742,c_5703])).

tff(c_8950,plain,(
    ! [A_514,B_515,C_516] :
      ( k1_relset_1(A_514,B_515,C_516) = k1_relat_1(C_516)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(A_514,B_515))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_8969,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_8950])).

tff(c_11812,plain,(
    ! [B_624,A_625,C_626] :
      ( k1_xboole_0 = B_624
      | k1_relset_1(A_625,B_624,C_626) = A_625
      | ~ v1_funct_2(C_626,A_625,B_624)
      | ~ m1_subset_1(C_626,k1_zfmisc_1(k2_zfmisc_1(A_625,B_624))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_11828,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_11812])).

tff(c_11843,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_8969,c_11828])).

tff(c_11844,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_11843])).

tff(c_11900,plain,(
    ! [A_38] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_38)) = A_38
      | ~ r1_tarski(A_38,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11844,c_50])).

tff(c_12273,plain,(
    ! [A_639] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_639)) = A_639
      | ~ r1_tarski(A_639,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_11900])).

tff(c_44,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_33,A_32)),A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12407,plain,(
    ! [A_639] :
      ( r1_tarski(A_639,A_639)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_639,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12273,c_44])).

tff(c_12519,plain,(
    ! [A_640] :
      ( r1_tarski(A_640,A_640)
      | ~ r1_tarski(A_640,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_12407])).

tff(c_12610,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_12519])).

tff(c_7912,plain,(
    ! [A_486] : k7_relat_1(k7_relat_1('#skF_4',A_486),A_486) = k7_relat_1('#skF_4',A_486) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6274,c_7890])).

tff(c_11950,plain,(
    ! [A_38] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_38)) = A_38
      | ~ r1_tarski(A_38,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_11900])).

tff(c_5949,plain,(
    ! [A_373] :
      ( r1_tarski(A_373,'#skF_1')
      | ~ r1_tarski(A_373,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_94,c_5924])).

tff(c_5966,plain,(
    ! [B_33] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_33,'#skF_3')),'#skF_1')
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_44,c_5949])).

tff(c_22218,plain,(
    ! [B_859] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_859,'#skF_3')),k1_relat_1(k7_relat_1(B_859,'#skF_3')))
      | ~ v1_relat_1(B_859) ) ),
    inference(resolution,[status(thm)],[c_5966,c_12519])).

tff(c_22270,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11950,c_22218])).

tff(c_22338,plain,(
    r1_tarski('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_5825,c_22270])).

tff(c_22378,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22338,c_50])).

tff(c_22414,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6274,c_7912,c_22378])).

tff(c_84,plain,(
    ! [B_67,A_66] :
      ( m1_subset_1(B_67,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_67),A_66)))
      | ~ r1_tarski(k2_relat_1(B_67),A_66)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_11348,plain,(
    ! [D_603,B_604,C_605,A_606] :
      ( m1_subset_1(D_603,k1_zfmisc_1(k2_zfmisc_1(B_604,C_605)))
      | ~ r1_tarski(k1_relat_1(D_603),B_604)
      | ~ m1_subset_1(D_603,k1_zfmisc_1(k2_zfmisc_1(A_606,C_605))) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_33318,plain,(
    ! [B_1070,B_1071,A_1072] :
      ( m1_subset_1(B_1070,k1_zfmisc_1(k2_zfmisc_1(B_1071,A_1072)))
      | ~ r1_tarski(k1_relat_1(B_1070),B_1071)
      | ~ r1_tarski(k2_relat_1(B_1070),A_1072)
      | ~ v1_funct_1(B_1070)
      | ~ v1_relat_1(B_1070) ) ),
    inference(resolution,[status(thm)],[c_84,c_11348])).

tff(c_5702,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_5704,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5702])).

tff(c_11747,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11742,c_5704])).

tff(c_33330,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_33318,c_11747])).

tff(c_33377,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6274,c_11748,c_12610,c_22414,c_33330])).

tff(c_33396,plain,(
    ~ v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_17568,c_33377])).

tff(c_33409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7028,c_33396])).

tff(c_33411,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5702])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_33629,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_33411,c_14])).

tff(c_38812,plain,(
    r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38803,c_33629])).

tff(c_40893,plain,(
    ! [A_1390,B_1391,A_1392] :
      ( k1_relset_1(A_1390,B_1391,A_1392) = k1_relat_1(A_1392)
      | ~ r1_tarski(A_1392,k2_zfmisc_1(A_1390,B_1391)) ) ),
    inference(resolution,[status(thm)],[c_16,c_36358])).

tff(c_40974,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38812,c_40893])).

tff(c_33410,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_5702])).

tff(c_38816,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38803,c_33410])).

tff(c_38815,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38803,c_33411])).

tff(c_39088,plain,(
    ! [B_1332,C_1333,A_1334] :
      ( k1_xboole_0 = B_1332
      | v1_funct_2(C_1333,A_1334,B_1332)
      | k1_relset_1(A_1334,B_1332,C_1333) != A_1334
      | ~ m1_subset_1(C_1333,k1_zfmisc_1(k2_zfmisc_1(A_1334,B_1332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_39094,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_38815,c_39088])).

tff(c_39120,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38816,c_106,c_39094])).

tff(c_49791,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40974,c_39120])).

tff(c_49801,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_39397,c_49791])).

tff(c_49805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_49801])).

tff(c_49806,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_8,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49832,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49806,c_49806,c_8])).

tff(c_49807,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_49812,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49806,c_49807])).

tff(c_49813,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49812,c_96])).

tff(c_52618,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49832,c_49813])).

tff(c_52648,plain,(
    ! [A_1815,B_1816] :
      ( r1_tarski(A_1815,B_1816)
      | ~ m1_subset_1(A_1815,k1_zfmisc_1(B_1816)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52655,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_52618,c_52648])).

tff(c_4,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49851,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49806,c_49806,c_4])).

tff(c_52660,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52655,c_49851])).

tff(c_49814,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49812,c_98])).

tff(c_52670,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52660,c_52660,c_49814])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49830,plain,(
    ! [A_7] : m1_subset_1('#skF_1',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49806,c_12])).

tff(c_52656,plain,(
    ! [A_7] : r1_tarski('#skF_1',A_7) ),
    inference(resolution,[status(thm)],[c_49830,c_52648])).

tff(c_52692,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52660,c_52656])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49821,plain,(
    ! [B_1588] : k2_zfmisc_1('#skF_1',B_1588) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49806,c_49806,c_10])).

tff(c_49825,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_49821,c_38])).

tff(c_52623,plain,(
    ! [B_1812,A_1813] :
      ( r1_tarski(k7_relat_1(B_1812,A_1813),B_1812)
      | ~ v1_relat_1(B_1812) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52627,plain,(
    ! [A_1813] :
      ( k7_relat_1('#skF_1',A_1813) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52623,c_49851])).

tff(c_52630,plain,(
    ! [A_1813] : k7_relat_1('#skF_1',A_1813) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49825,c_52627])).

tff(c_52662,plain,(
    ! [A_1813] : k7_relat_1('#skF_4',A_1813) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52660,c_52660,c_52630])).

tff(c_52671,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52660,c_49830])).

tff(c_55165,plain,(
    ! [A_2010,B_2011,C_2012,D_2013] :
      ( k2_partfun1(A_2010,B_2011,C_2012,D_2013) = k7_relat_1(C_2012,D_2013)
      | ~ m1_subset_1(C_2012,k1_zfmisc_1(k2_zfmisc_1(A_2010,B_2011)))
      | ~ v1_funct_1(C_2012) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_55177,plain,(
    ! [A_2010,B_2011,D_2013] :
      ( k2_partfun1(A_2010,B_2011,'#skF_4',D_2013) = k7_relat_1('#skF_4',D_2013)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52671,c_55165])).

tff(c_55182,plain,(
    ! [A_2010,B_2011,D_2013] : k2_partfun1(A_2010,B_2011,'#skF_4',D_2013) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52662,c_55177])).

tff(c_49852,plain,(
    ! [A_1591] :
      ( A_1591 = '#skF_1'
      | ~ r1_tarski(A_1591,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49806,c_49806,c_4])).

tff(c_49856,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_94,c_49852])).

tff(c_52667,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52660,c_49856])).

tff(c_49820,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49806,c_49806,c_10])).

tff(c_49869,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49820,c_49813])).

tff(c_49874,plain,(
    ! [A_1595,B_1596] :
      ( r1_tarski(A_1595,B_1596)
      | ~ m1_subset_1(A_1595,k1_zfmisc_1(B_1596)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_49881,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_49869,c_49874])).

tff(c_49886,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_49881,c_49851])).

tff(c_49897,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49886,c_49825])).

tff(c_49962,plain,(
    ! [A_1603] :
      ( A_1603 = '#skF_4'
      | ~ r1_tarski(A_1603,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49886,c_49886,c_49851])).

tff(c_49966,plain,(
    ! [A_34] :
      ( k7_relat_1('#skF_4',A_34) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_49962])).

tff(c_49973,plain,(
    ! [A_34] : k7_relat_1('#skF_4',A_34) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49897,c_49966])).

tff(c_49896,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49886,c_49830])).

tff(c_52584,plain,(
    ! [A_1805,B_1806,C_1807,D_1808] :
      ( k2_partfun1(A_1805,B_1806,C_1807,D_1808) = k7_relat_1(C_1807,D_1808)
      | ~ m1_subset_1(C_1807,k1_zfmisc_1(k2_zfmisc_1(A_1805,B_1806)))
      | ~ v1_funct_1(C_1807) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_52592,plain,(
    ! [A_1805,B_1806,D_1808] :
      ( k2_partfun1(A_1805,B_1806,'#skF_4',D_1808) = k7_relat_1('#skF_4',D_1808)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_49896,c_52584])).

tff(c_52601,plain,(
    ! [A_1805,B_1806,D_1808] : k2_partfun1(A_1805,B_1806,'#skF_4',D_1808) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_49973,c_52592])).

tff(c_49857,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49812,c_49812,c_49812,c_49832,c_49812,c_49812,c_90])).

tff(c_49858,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_49857])).

tff(c_49873,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49856,c_49858])).

tff(c_49888,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49886,c_49886,c_49886,c_49873])).

tff(c_52602,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52601,c_49888])).

tff(c_52605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52602])).

tff(c_52606,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_49857])).

tff(c_52727,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52667,c_52660,c_52660,c_52660,c_52667,c_52667,c_52660,c_52660,c_52660,c_52606])).

tff(c_52728,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52727])).

tff(c_52825,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_52728])).

tff(c_55183,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55182,c_52825])).

tff(c_55188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52692,c_55183])).

tff(c_55190,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52727])).

tff(c_55381,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_55190,c_14])).

tff(c_52668,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52660,c_52660,c_49851])).

tff(c_55391,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_55381,c_52668])).

tff(c_55189,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52727])).

tff(c_55395,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55391,c_55189])).

tff(c_55402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52670,c_55395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:17:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.60/7.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.60/7.57  
% 16.60/7.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.60/7.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.60/7.57  
% 16.60/7.57  %Foreground sorts:
% 16.60/7.57  
% 16.60/7.57  
% 16.60/7.57  %Background operators:
% 16.60/7.57  
% 16.60/7.57  
% 16.60/7.57  %Foreground operators:
% 16.60/7.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.60/7.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.60/7.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.60/7.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 16.60/7.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.60/7.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.60/7.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.60/7.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.60/7.57  tff('#skF_2', type, '#skF_2': $i).
% 16.60/7.57  tff('#skF_3', type, '#skF_3': $i).
% 16.60/7.57  tff('#skF_1', type, '#skF_1': $i).
% 16.60/7.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 16.60/7.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 16.60/7.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.60/7.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.60/7.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.60/7.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.60/7.57  tff('#skF_4', type, '#skF_4': $i).
% 16.60/7.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.60/7.57  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 16.60/7.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 16.60/7.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.60/7.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.60/7.57  
% 16.78/7.60  tff(f_212, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 16.78/7.60  tff(f_88, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 16.78/7.60  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 16.78/7.60  tff(f_144, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 16.78/7.60  tff(f_174, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 16.78/7.60  tff(f_118, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 16.78/7.60  tff(f_180, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 16.78/7.60  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 16.78/7.60  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 16.78/7.60  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 16.78/7.60  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 16.78/7.60  tff(f_86, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 16.78/7.60  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 16.78/7.60  tff(f_126, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 16.78/7.60  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 16.78/7.60  tff(f_134, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 16.78/7.60  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 16.78/7.60  tff(f_192, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 16.78/7.60  tff(f_150, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 16.78/7.60  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 16.78/7.60  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 16.78/7.60  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 16.78/7.60  tff(c_94, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_212])).
% 16.78/7.60  tff(c_38, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.78/7.60  tff(c_96, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 16.78/7.60  tff(c_33482, plain, (![B_1082, A_1083]: (v1_relat_1(B_1082) | ~m1_subset_1(B_1082, k1_zfmisc_1(A_1083)) | ~v1_relat_1(A_1083))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.78/7.60  tff(c_33488, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_96, c_33482])).
% 16.78/7.60  tff(c_33495, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_33488])).
% 16.78/7.60  tff(c_92, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_212])).
% 16.78/7.60  tff(c_106, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_92])).
% 16.78/7.60  tff(c_98, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 16.78/7.60  tff(c_36358, plain, (![A_1231, B_1232, C_1233]: (k1_relset_1(A_1231, B_1232, C_1233)=k1_relat_1(C_1233) | ~m1_subset_1(C_1233, k1_zfmisc_1(k2_zfmisc_1(A_1231, B_1232))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 16.78/7.60  tff(c_36381, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_36358])).
% 16.78/7.60  tff(c_39256, plain, (![B_1339, A_1340, C_1341]: (k1_xboole_0=B_1339 | k1_relset_1(A_1340, B_1339, C_1341)=A_1340 | ~v1_funct_2(C_1341, A_1340, B_1339) | ~m1_subset_1(C_1341, k1_zfmisc_1(k2_zfmisc_1(A_1340, B_1339))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 16.78/7.60  tff(c_39275, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_39256])).
% 16.78/7.60  tff(c_39292, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_36381, c_39275])).
% 16.78/7.60  tff(c_39293, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_106, c_39292])).
% 16.78/7.60  tff(c_50, plain, (![B_39, A_38]: (k1_relat_1(k7_relat_1(B_39, A_38))=A_38 | ~r1_tarski(A_38, k1_relat_1(B_39)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.78/7.60  tff(c_39354, plain, (![A_38]: (k1_relat_1(k7_relat_1('#skF_4', A_38))=A_38 | ~r1_tarski(A_38, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_39293, c_50])).
% 16.78/7.60  tff(c_39397, plain, (![A_38]: (k1_relat_1(k7_relat_1('#skF_4', A_38))=A_38 | ~r1_tarski(A_38, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_33495, c_39354])).
% 16.78/7.60  tff(c_100, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 16.78/7.60  tff(c_38779, plain, (![A_1320, B_1321, C_1322, D_1323]: (k2_partfun1(A_1320, B_1321, C_1322, D_1323)=k7_relat_1(C_1322, D_1323) | ~m1_subset_1(C_1322, k1_zfmisc_1(k2_zfmisc_1(A_1320, B_1321))) | ~v1_funct_1(C_1322))), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.78/7.60  tff(c_38790, plain, (![D_1323]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1323)=k7_relat_1('#skF_4', D_1323) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_96, c_38779])).
% 16.78/7.60  tff(c_38803, plain, (![D_1323]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1323)=k7_relat_1('#skF_4', D_1323))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_38790])).
% 16.78/7.60  tff(c_7009, plain, (![C_428, B_429, A_430]: (v5_relat_1(C_428, B_429) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_430, B_429))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 16.78/7.60  tff(c_7028, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_7009])).
% 16.78/7.60  tff(c_5812, plain, (![B_357, A_358]: (v1_relat_1(B_357) | ~m1_subset_1(B_357, k1_zfmisc_1(A_358)) | ~v1_relat_1(A_358))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.78/7.60  tff(c_5818, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_96, c_5812])).
% 16.78/7.60  tff(c_5825, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5818])).
% 16.78/7.60  tff(c_46, plain, (![B_35, A_34]: (r1_tarski(k7_relat_1(B_35, A_34), B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_108])).
% 16.78/7.60  tff(c_5705, plain, (![A_345, B_346]: (r1_tarski(A_345, B_346) | ~m1_subset_1(A_345, k1_zfmisc_1(B_346)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.78/7.60  tff(c_5716, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_96, c_5705])).
% 16.78/7.60  tff(c_5924, plain, (![A_370, C_371, B_372]: (r1_tarski(A_370, C_371) | ~r1_tarski(B_372, C_371) | ~r1_tarski(A_370, B_372))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.78/7.60  tff(c_6190, plain, (![A_393]: (r1_tarski(A_393, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_393, '#skF_4'))), inference(resolution, [status(thm)], [c_5716, c_5924])).
% 16.78/7.60  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.78/7.60  tff(c_5822, plain, (![A_8, B_9]: (v1_relat_1(A_8) | ~v1_relat_1(B_9) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_16, c_5812])).
% 16.78/7.60  tff(c_6202, plain, (![A_393]: (v1_relat_1(A_393) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_393, '#skF_4'))), inference(resolution, [status(thm)], [c_6190, c_5822])).
% 16.78/7.60  tff(c_6244, plain, (![A_396]: (v1_relat_1(A_396) | ~r1_tarski(A_396, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6202])).
% 16.78/7.60  tff(c_6263, plain, (![A_34]: (v1_relat_1(k7_relat_1('#skF_4', A_34)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_6244])).
% 16.78/7.60  tff(c_6274, plain, (![A_34]: (v1_relat_1(k7_relat_1('#skF_4', A_34)))), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_6263])).
% 16.78/7.60  tff(c_5890, plain, (![C_365, A_366, B_367]: (v4_relat_1(C_365, A_366) | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 16.78/7.60  tff(c_5909, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_96, c_5890])).
% 16.78/7.60  tff(c_7817, plain, (![C_483, A_484, B_485]: (v4_relat_1(k7_relat_1(C_483, A_484), A_484) | ~v4_relat_1(C_483, B_485) | ~v1_relat_1(C_483))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.78/7.60  tff(c_7847, plain, (![A_484]: (v4_relat_1(k7_relat_1('#skF_4', A_484), A_484) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_5909, c_7817])).
% 16.78/7.60  tff(c_7877, plain, (![A_486]: (v4_relat_1(k7_relat_1('#skF_4', A_486), A_486))), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_7847])).
% 16.78/7.60  tff(c_42, plain, (![B_31, A_30]: (k7_relat_1(B_31, A_30)=B_31 | ~v4_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_100])).
% 16.78/7.60  tff(c_7890, plain, (![A_486]: (k7_relat_1(k7_relat_1('#skF_4', A_486), A_486)=k7_relat_1('#skF_4', A_486) | ~v1_relat_1(k7_relat_1('#skF_4', A_486)))), inference(resolution, [status(thm)], [c_7877, c_42])).
% 16.78/7.60  tff(c_8324, plain, (![A_501]: (k7_relat_1(k7_relat_1('#skF_4', A_501), A_501)=k7_relat_1('#skF_4', A_501))), inference(demodulation, [status(thm), theory('equality')], [c_6274, c_7890])).
% 16.78/7.60  tff(c_54, plain, (![B_42, A_41]: (r1_tarski(k2_relat_1(k7_relat_1(B_42, A_41)), k2_relat_1(B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.78/7.60  tff(c_8378, plain, (![A_501]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_501)), k2_relat_1(k7_relat_1('#skF_4', A_501))) | ~v1_relat_1(k7_relat_1('#skF_4', A_501)))), inference(superposition, [status(thm), theory('equality')], [c_8324, c_54])).
% 16.78/7.60  tff(c_8438, plain, (![A_501]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_501)), k2_relat_1(k7_relat_1('#skF_4', A_501))))), inference(demodulation, [status(thm), theory('equality')], [c_6274, c_8378])).
% 16.78/7.60  tff(c_17362, plain, (![A_751, B_752, A_753]: (r1_tarski(A_751, k2_relat_1(B_752)) | ~r1_tarski(A_751, k2_relat_1(k7_relat_1(B_752, A_753))) | ~v1_relat_1(B_752))), inference(resolution, [status(thm)], [c_54, c_5924])).
% 16.78/7.60  tff(c_17401, plain, (![A_501]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_501)), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8438, c_17362])).
% 16.78/7.60  tff(c_17542, plain, (![A_754]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_754)), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_17401])).
% 16.78/7.60  tff(c_7114, plain, (![B_442, A_443]: (r1_tarski(k2_relat_1(B_442), A_443) | ~v5_relat_1(B_442, A_443) | ~v1_relat_1(B_442))), inference(cnfTransformation, [status(thm)], [f_72])).
% 16.78/7.60  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.78/7.60  tff(c_7164, plain, (![A_1, A_443, B_442]: (r1_tarski(A_1, A_443) | ~r1_tarski(A_1, k2_relat_1(B_442)) | ~v5_relat_1(B_442, A_443) | ~v1_relat_1(B_442))), inference(resolution, [status(thm)], [c_7114, c_2])).
% 16.78/7.60  tff(c_17544, plain, (![A_754, A_443]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_754)), A_443) | ~v5_relat_1('#skF_4', A_443) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_17542, c_7164])).
% 16.78/7.60  tff(c_17568, plain, (![A_754, A_443]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_754)), A_443) | ~v5_relat_1('#skF_4', A_443))), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_17544])).
% 16.78/7.60  tff(c_11718, plain, (![A_618, B_619, C_620, D_621]: (k2_partfun1(A_618, B_619, C_620, D_621)=k7_relat_1(C_620, D_621) | ~m1_subset_1(C_620, k1_zfmisc_1(k2_zfmisc_1(A_618, B_619))) | ~v1_funct_1(C_620))), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.78/7.60  tff(c_11729, plain, (![D_621]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_621)=k7_relat_1('#skF_4', D_621) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_96, c_11718])).
% 16.78/7.60  tff(c_11742, plain, (![D_621]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_621)=k7_relat_1('#skF_4', D_621))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_11729])).
% 16.78/7.60  tff(c_303, plain, (![B_95, A_96]: (v1_relat_1(B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_96)) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.78/7.60  tff(c_309, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_96, c_303])).
% 16.78/7.60  tff(c_316, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_309])).
% 16.78/7.60  tff(c_56, plain, (![A_43, B_44]: (v1_funct_1(k7_relat_1(A_43, B_44)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_134])).
% 16.78/7.60  tff(c_5663, plain, (![A_340, B_341, C_342, D_343]: (k2_partfun1(A_340, B_341, C_342, D_343)=k7_relat_1(C_342, D_343) | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(A_340, B_341))) | ~v1_funct_1(C_342))), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.78/7.60  tff(c_5672, plain, (![D_343]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_343)=k7_relat_1('#skF_4', D_343) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_96, c_5663])).
% 16.78/7.60  tff(c_5682, plain, (![D_343]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_343)=k7_relat_1('#skF_4', D_343))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_5672])).
% 16.78/7.60  tff(c_90, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 16.78/7.60  tff(c_199, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_90])).
% 16.78/7.60  tff(c_5685, plain, (~v1_funct_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5682, c_199])).
% 16.78/7.60  tff(c_5697, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_5685])).
% 16.78/7.60  tff(c_5701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_316, c_100, c_5697])).
% 16.78/7.60  tff(c_5703, plain, (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_90])).
% 16.78/7.60  tff(c_11748, plain, (v1_funct_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11742, c_5703])).
% 16.78/7.60  tff(c_8950, plain, (![A_514, B_515, C_516]: (k1_relset_1(A_514, B_515, C_516)=k1_relat_1(C_516) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(A_514, B_515))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 16.78/7.60  tff(c_8969, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_8950])).
% 16.78/7.60  tff(c_11812, plain, (![B_624, A_625, C_626]: (k1_xboole_0=B_624 | k1_relset_1(A_625, B_624, C_626)=A_625 | ~v1_funct_2(C_626, A_625, B_624) | ~m1_subset_1(C_626, k1_zfmisc_1(k2_zfmisc_1(A_625, B_624))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 16.78/7.60  tff(c_11828, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_11812])).
% 16.78/7.60  tff(c_11843, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_8969, c_11828])).
% 16.78/7.60  tff(c_11844, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_106, c_11843])).
% 16.78/7.60  tff(c_11900, plain, (![A_38]: (k1_relat_1(k7_relat_1('#skF_4', A_38))=A_38 | ~r1_tarski(A_38, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11844, c_50])).
% 16.78/7.60  tff(c_12273, plain, (![A_639]: (k1_relat_1(k7_relat_1('#skF_4', A_639))=A_639 | ~r1_tarski(A_639, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_11900])).
% 16.78/7.60  tff(c_44, plain, (![B_33, A_32]: (r1_tarski(k1_relat_1(k7_relat_1(B_33, A_32)), A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_104])).
% 16.78/7.60  tff(c_12407, plain, (![A_639]: (r1_tarski(A_639, A_639) | ~v1_relat_1('#skF_4') | ~r1_tarski(A_639, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12273, c_44])).
% 16.78/7.60  tff(c_12519, plain, (![A_640]: (r1_tarski(A_640, A_640) | ~r1_tarski(A_640, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_12407])).
% 16.78/7.60  tff(c_12610, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_94, c_12519])).
% 16.78/7.60  tff(c_7912, plain, (![A_486]: (k7_relat_1(k7_relat_1('#skF_4', A_486), A_486)=k7_relat_1('#skF_4', A_486))), inference(demodulation, [status(thm), theory('equality')], [c_6274, c_7890])).
% 16.78/7.60  tff(c_11950, plain, (![A_38]: (k1_relat_1(k7_relat_1('#skF_4', A_38))=A_38 | ~r1_tarski(A_38, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_11900])).
% 16.78/7.60  tff(c_5949, plain, (![A_373]: (r1_tarski(A_373, '#skF_1') | ~r1_tarski(A_373, '#skF_3'))), inference(resolution, [status(thm)], [c_94, c_5924])).
% 16.78/7.60  tff(c_5966, plain, (![B_33]: (r1_tarski(k1_relat_1(k7_relat_1(B_33, '#skF_3')), '#skF_1') | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_44, c_5949])).
% 16.78/7.60  tff(c_22218, plain, (![B_859]: (r1_tarski(k1_relat_1(k7_relat_1(B_859, '#skF_3')), k1_relat_1(k7_relat_1(B_859, '#skF_3'))) | ~v1_relat_1(B_859))), inference(resolution, [status(thm)], [c_5966, c_12519])).
% 16.78/7.60  tff(c_22270, plain, (r1_tarski('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11950, c_22218])).
% 16.78/7.60  tff(c_22338, plain, (r1_tarski('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_5825, c_22270])).
% 16.78/7.60  tff(c_22378, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3'))='#skF_3' | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_22338, c_50])).
% 16.78/7.60  tff(c_22414, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6274, c_7912, c_22378])).
% 16.78/7.60  tff(c_84, plain, (![B_67, A_66]: (m1_subset_1(B_67, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_67), A_66))) | ~r1_tarski(k2_relat_1(B_67), A_66) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_192])).
% 16.78/7.60  tff(c_11348, plain, (![D_603, B_604, C_605, A_606]: (m1_subset_1(D_603, k1_zfmisc_1(k2_zfmisc_1(B_604, C_605))) | ~r1_tarski(k1_relat_1(D_603), B_604) | ~m1_subset_1(D_603, k1_zfmisc_1(k2_zfmisc_1(A_606, C_605))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 16.78/7.60  tff(c_33318, plain, (![B_1070, B_1071, A_1072]: (m1_subset_1(B_1070, k1_zfmisc_1(k2_zfmisc_1(B_1071, A_1072))) | ~r1_tarski(k1_relat_1(B_1070), B_1071) | ~r1_tarski(k2_relat_1(B_1070), A_1072) | ~v1_funct_1(B_1070) | ~v1_relat_1(B_1070))), inference(resolution, [status(thm)], [c_84, c_11348])).
% 16.78/7.60  tff(c_5702, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_90])).
% 16.78/7.60  tff(c_5704, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_5702])).
% 16.78/7.60  tff(c_11747, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_11742, c_5704])).
% 16.78/7.60  tff(c_33330, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~v1_funct_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_33318, c_11747])).
% 16.78/7.60  tff(c_33377, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6274, c_11748, c_12610, c_22414, c_33330])).
% 16.78/7.60  tff(c_33396, plain, (~v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_17568, c_33377])).
% 16.78/7.60  tff(c_33409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7028, c_33396])).
% 16.78/7.60  tff(c_33411, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_5702])).
% 16.78/7.60  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.78/7.60  tff(c_33629, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_33411, c_14])).
% 16.78/7.60  tff(c_38812, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38803, c_33629])).
% 16.78/7.60  tff(c_40893, plain, (![A_1390, B_1391, A_1392]: (k1_relset_1(A_1390, B_1391, A_1392)=k1_relat_1(A_1392) | ~r1_tarski(A_1392, k2_zfmisc_1(A_1390, B_1391)))), inference(resolution, [status(thm)], [c_16, c_36358])).
% 16.78/7.60  tff(c_40974, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_38812, c_40893])).
% 16.78/7.60  tff(c_33410, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_5702])).
% 16.78/7.60  tff(c_38816, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38803, c_33410])).
% 16.78/7.60  tff(c_38815, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38803, c_33411])).
% 16.78/7.60  tff(c_39088, plain, (![B_1332, C_1333, A_1334]: (k1_xboole_0=B_1332 | v1_funct_2(C_1333, A_1334, B_1332) | k1_relset_1(A_1334, B_1332, C_1333)!=A_1334 | ~m1_subset_1(C_1333, k1_zfmisc_1(k2_zfmisc_1(A_1334, B_1332))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 16.78/7.60  tff(c_39094, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_38815, c_39088])).
% 16.78/7.60  tff(c_39120, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38816, c_106, c_39094])).
% 16.78/7.60  tff(c_49791, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40974, c_39120])).
% 16.78/7.60  tff(c_49801, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_39397, c_49791])).
% 16.78/7.60  tff(c_49805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_49801])).
% 16.78/7.60  tff(c_49806, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_92])).
% 16.78/7.60  tff(c_8, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.78/7.60  tff(c_49832, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49806, c_49806, c_8])).
% 16.78/7.60  tff(c_49807, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_92])).
% 16.78/7.60  tff(c_49812, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_49806, c_49807])).
% 16.78/7.60  tff(c_49813, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_49812, c_96])).
% 16.78/7.60  tff(c_52618, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_49832, c_49813])).
% 16.78/7.60  tff(c_52648, plain, (![A_1815, B_1816]: (r1_tarski(A_1815, B_1816) | ~m1_subset_1(A_1815, k1_zfmisc_1(B_1816)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.78/7.60  tff(c_52655, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_52618, c_52648])).
% 16.78/7.60  tff(c_4, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.78/7.60  tff(c_49851, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_49806, c_49806, c_4])).
% 16.78/7.60  tff(c_52660, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_52655, c_49851])).
% 16.78/7.60  tff(c_49814, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49812, c_98])).
% 16.78/7.60  tff(c_52670, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52660, c_52660, c_49814])).
% 16.78/7.60  tff(c_12, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.78/7.60  tff(c_49830, plain, (![A_7]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_49806, c_12])).
% 16.78/7.60  tff(c_52656, plain, (![A_7]: (r1_tarski('#skF_1', A_7))), inference(resolution, [status(thm)], [c_49830, c_52648])).
% 16.78/7.60  tff(c_52692, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_52660, c_52656])).
% 16.78/7.60  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.78/7.60  tff(c_49821, plain, (![B_1588]: (k2_zfmisc_1('#skF_1', B_1588)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49806, c_49806, c_10])).
% 16.78/7.60  tff(c_49825, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_49821, c_38])).
% 16.78/7.60  tff(c_52623, plain, (![B_1812, A_1813]: (r1_tarski(k7_relat_1(B_1812, A_1813), B_1812) | ~v1_relat_1(B_1812))), inference(cnfTransformation, [status(thm)], [f_108])).
% 16.78/7.60  tff(c_52627, plain, (![A_1813]: (k7_relat_1('#skF_1', A_1813)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_52623, c_49851])).
% 16.78/7.60  tff(c_52630, plain, (![A_1813]: (k7_relat_1('#skF_1', A_1813)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49825, c_52627])).
% 16.78/7.60  tff(c_52662, plain, (![A_1813]: (k7_relat_1('#skF_4', A_1813)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52660, c_52660, c_52630])).
% 16.78/7.60  tff(c_52671, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_52660, c_49830])).
% 16.78/7.60  tff(c_55165, plain, (![A_2010, B_2011, C_2012, D_2013]: (k2_partfun1(A_2010, B_2011, C_2012, D_2013)=k7_relat_1(C_2012, D_2013) | ~m1_subset_1(C_2012, k1_zfmisc_1(k2_zfmisc_1(A_2010, B_2011))) | ~v1_funct_1(C_2012))), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.78/7.60  tff(c_55177, plain, (![A_2010, B_2011, D_2013]: (k2_partfun1(A_2010, B_2011, '#skF_4', D_2013)=k7_relat_1('#skF_4', D_2013) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_52671, c_55165])).
% 16.78/7.60  tff(c_55182, plain, (![A_2010, B_2011, D_2013]: (k2_partfun1(A_2010, B_2011, '#skF_4', D_2013)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_52662, c_55177])).
% 16.78/7.60  tff(c_49852, plain, (![A_1591]: (A_1591='#skF_1' | ~r1_tarski(A_1591, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_49806, c_49806, c_4])).
% 16.78/7.60  tff(c_49856, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_94, c_49852])).
% 16.78/7.60  tff(c_52667, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52660, c_49856])).
% 16.78/7.60  tff(c_49820, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49806, c_49806, c_10])).
% 16.78/7.60  tff(c_49869, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_49820, c_49813])).
% 16.78/7.60  tff(c_49874, plain, (![A_1595, B_1596]: (r1_tarski(A_1595, B_1596) | ~m1_subset_1(A_1595, k1_zfmisc_1(B_1596)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.78/7.60  tff(c_49881, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_49869, c_49874])).
% 16.78/7.60  tff(c_49886, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_49881, c_49851])).
% 16.78/7.60  tff(c_49897, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49886, c_49825])).
% 16.78/7.60  tff(c_49962, plain, (![A_1603]: (A_1603='#skF_4' | ~r1_tarski(A_1603, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_49886, c_49886, c_49851])).
% 16.78/7.60  tff(c_49966, plain, (![A_34]: (k7_relat_1('#skF_4', A_34)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_49962])).
% 16.78/7.60  tff(c_49973, plain, (![A_34]: (k7_relat_1('#skF_4', A_34)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49897, c_49966])).
% 16.78/7.60  tff(c_49896, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_49886, c_49830])).
% 16.78/7.60  tff(c_52584, plain, (![A_1805, B_1806, C_1807, D_1808]: (k2_partfun1(A_1805, B_1806, C_1807, D_1808)=k7_relat_1(C_1807, D_1808) | ~m1_subset_1(C_1807, k1_zfmisc_1(k2_zfmisc_1(A_1805, B_1806))) | ~v1_funct_1(C_1807))), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.78/7.60  tff(c_52592, plain, (![A_1805, B_1806, D_1808]: (k2_partfun1(A_1805, B_1806, '#skF_4', D_1808)=k7_relat_1('#skF_4', D_1808) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_49896, c_52584])).
% 16.78/7.60  tff(c_52601, plain, (![A_1805, B_1806, D_1808]: (k2_partfun1(A_1805, B_1806, '#skF_4', D_1808)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_49973, c_52592])).
% 16.78/7.60  tff(c_49857, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_49812, c_49812, c_49812, c_49832, c_49812, c_49812, c_90])).
% 16.78/7.60  tff(c_49858, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_49857])).
% 16.78/7.60  tff(c_49873, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_49856, c_49858])).
% 16.78/7.60  tff(c_49888, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_49886, c_49886, c_49886, c_49873])).
% 16.78/7.60  tff(c_52602, plain, (~v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52601, c_49888])).
% 16.78/7.60  tff(c_52605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_52602])).
% 16.78/7.60  tff(c_52606, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_49857])).
% 16.78/7.60  tff(c_52727, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52667, c_52660, c_52660, c_52660, c_52667, c_52667, c_52660, c_52660, c_52660, c_52606])).
% 16.78/7.60  tff(c_52728, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_52727])).
% 16.78/7.60  tff(c_52825, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_16, c_52728])).
% 16.78/7.60  tff(c_55183, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55182, c_52825])).
% 16.78/7.60  tff(c_55188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52692, c_55183])).
% 16.78/7.60  tff(c_55190, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_52727])).
% 16.78/7.60  tff(c_55381, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_55190, c_14])).
% 16.78/7.60  tff(c_52668, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52660, c_52660, c_49851])).
% 16.78/7.60  tff(c_55391, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_55381, c_52668])).
% 16.78/7.60  tff(c_55189, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_52727])).
% 16.78/7.60  tff(c_55395, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55391, c_55189])).
% 16.78/7.60  tff(c_55402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52670, c_55395])).
% 16.78/7.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.78/7.60  
% 16.78/7.60  Inference rules
% 16.78/7.60  ----------------------
% 16.78/7.60  #Ref     : 0
% 16.78/7.60  #Sup     : 11449
% 16.78/7.60  #Fact    : 0
% 16.78/7.60  #Define  : 0
% 16.78/7.60  #Split   : 48
% 16.78/7.60  #Chain   : 0
% 16.78/7.60  #Close   : 0
% 16.78/7.60  
% 16.78/7.60  Ordering : KBO
% 16.78/7.60  
% 16.78/7.60  Simplification rules
% 16.78/7.60  ----------------------
% 16.78/7.60  #Subsume      : 2928
% 16.78/7.60  #Demod        : 12083
% 16.78/7.60  #Tautology    : 4706
% 16.78/7.60  #SimpNegUnit  : 227
% 16.78/7.60  #BackRed      : 156
% 16.78/7.60  
% 16.78/7.60  #Partial instantiations: 0
% 16.78/7.60  #Strategies tried      : 1
% 16.78/7.60  
% 16.78/7.60  Timing (in seconds)
% 16.78/7.60  ----------------------
% 16.78/7.60  Preprocessing        : 0.40
% 16.78/7.60  Parsing              : 0.22
% 16.78/7.60  CNF conversion       : 0.03
% 16.78/7.60  Main loop            : 6.41
% 16.78/7.60  Inferencing          : 1.49
% 16.78/7.60  Reduction            : 2.82
% 16.78/7.60  Demodulation         : 2.22
% 16.78/7.60  BG Simplification    : 0.12
% 16.78/7.60  Subsumption          : 1.57
% 16.78/7.60  Abstraction          : 0.18
% 16.78/7.60  MUC search           : 0.00
% 16.78/7.60  Cooper               : 0.00
% 16.78/7.60  Total                : 6.87
% 16.78/7.60  Index Insertion      : 0.00
% 16.78/7.60  Index Deletion       : 0.00
% 16.78/7.60  Index Matching       : 0.00
% 16.78/7.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
