%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:42 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  156 (2788 expanded)
%              Number of leaves         :   33 ( 872 expanded)
%              Depth                    :   16
%              Number of atoms          :  248 (8175 expanded)
%              Number of equality atoms :   82 (3119 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_54,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_108,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_114,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_108])).

tff(c_118,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_114])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1890,plain,(
    ! [A_258,B_259,C_260] :
      ( k1_relset_1(A_258,B_259,C_260) = k1_relat_1(C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1909,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1890])).

tff(c_2251,plain,(
    ! [B_302,A_303,C_304] :
      ( k1_xboole_0 = B_302
      | k1_relset_1(A_303,B_302,C_304) = A_303
      | ~ v1_funct_2(C_304,A_303,B_302)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_303,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2264,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_2251])).

tff(c_2279,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1909,c_2264])).

tff(c_2280,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2279])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,A_15)) = A_15
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2294,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2280,c_26])).

tff(c_2300,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2294])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2106,plain,(
    ! [A_289,B_290,C_291,D_292] :
      ( k2_partfun1(A_289,B_290,C_291,D_292) = k7_relat_1(C_291,D_292)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ v1_funct_1(C_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2113,plain,(
    ! [D_292] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_292) = k7_relat_1('#skF_4',D_292)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_2106])).

tff(c_2124,plain,(
    ! [D_292] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_292) = k7_relat_1('#skF_4',D_292) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2113])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_625,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_640,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_625])).

tff(c_955,plain,(
    ! [B_158,A_159,C_160] :
      ( k1_xboole_0 = B_158
      | k1_relset_1(A_159,B_158,C_160) = A_159
      | ~ v1_funct_2(C_160,A_159,B_158)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_159,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_965,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_955])).

tff(c_978,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_640,c_965])).

tff(c_979,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_978])).

tff(c_999,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_26])).

tff(c_1005,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_999])).

tff(c_908,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k2_partfun1(A_143,B_144,C_145,D_146) = k7_relat_1(C_145,D_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_915,plain,(
    ! [D_146] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_146) = k7_relat_1('#skF_4',D_146)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_908])).

tff(c_926,plain,(
    ! [D_146] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_146) = k7_relat_1('#skF_4',D_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_915])).

tff(c_1197,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( m1_subset_1(k2_partfun1(A_173,B_174,C_175,D_176),k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1(C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1221,plain,(
    ! [D_146] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_146),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_1197])).

tff(c_1253,plain,(
    ! [D_177] : m1_subset_1(k7_relat_1('#skF_4',D_177),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1221])).

tff(c_30,plain,(
    ! [D_23,B_21,C_22,A_20] :
      ( m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(B_21,C_22)))
      | ~ r1_tarski(k1_relat_1(D_23),B_21)
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(A_20,C_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1748,plain,(
    ! [D_251,B_252] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_251),k1_zfmisc_1(k2_zfmisc_1(B_252,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_251)),B_252) ) ),
    inference(resolution,[status(thm)],[c_1253,c_30])).

tff(c_413,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( v1_funct_1(k2_partfun1(A_79,B_80,C_81,D_82))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_418,plain,(
    ! [D_82] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_82))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_413])).

tff(c_426,plain,(
    ! [D_82] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_418])).

tff(c_50,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_143,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_143])).

tff(c_430,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_559,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_929,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_559])).

tff(c_1788,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1748,c_929])).

tff(c_1803,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_1788])).

tff(c_1806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6,c_1803])).

tff(c_1808,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_1907,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1808,c_1890])).

tff(c_2127,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2124,c_2124,c_1907])).

tff(c_1807,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_2132,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2124,c_1807])).

tff(c_2131,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2124,c_1808])).

tff(c_2437,plain,(
    ! [B_309,C_310,A_311] :
      ( k1_xboole_0 = B_309
      | v1_funct_2(C_310,A_311,B_309)
      | k1_relset_1(A_311,B_309,C_310) != A_311
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_311,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2443,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_2131,c_2437])).

tff(c_2462,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2132,c_96,c_2443])).

tff(c_2476,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2127,c_2462])).

tff(c_2483,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2300,c_2476])).

tff(c_2487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2483])).

tff(c_2488,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2493,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2488,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2492,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2488,c_2488,c_12])).

tff(c_2489,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2498,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2488,c_2489])).

tff(c_2533,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_2498,c_56])).

tff(c_2534,plain,(
    ! [A_317,B_318] :
      ( r1_tarski(A_317,B_318)
      | ~ m1_subset_1(A_317,k1_zfmisc_1(B_318)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2538,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_2533,c_2534])).

tff(c_2545,plain,(
    ! [B_323,A_324] :
      ( B_323 = A_324
      | ~ r1_tarski(B_323,A_324)
      | ~ r1_tarski(A_324,B_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2549,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_2538,c_2545])).

tff(c_2559,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2493,c_2549])).

tff(c_2499,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2498,c_58])).

tff(c_2576,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2559,c_2499])).

tff(c_69,plain,(
    ! [A_39] : k2_zfmisc_1(A_39,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_22])).

tff(c_2491,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2488,c_73])).

tff(c_2580,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2491])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2560,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2493,c_2545])).

tff(c_3060,plain,(
    ! [A_382] :
      ( A_382 = '#skF_4'
      | ~ r1_tarski(A_382,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2559,c_2560])).

tff(c_3068,plain,(
    ! [A_13] :
      ( k7_relat_1('#skF_4',A_13) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_3060])).

tff(c_3077,plain,(
    ! [A_13] : k7_relat_1('#skF_4',A_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2580,c_3068])).

tff(c_2577,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2533])).

tff(c_2579,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2559,c_2492])).

tff(c_3429,plain,(
    ! [A_430,B_431,C_432,D_433] :
      ( k2_partfun1(A_430,B_431,C_432,D_433) = k7_relat_1(C_432,D_433)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431)))
      | ~ v1_funct_1(C_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3539,plain,(
    ! [A_470,C_471,D_472] :
      ( k2_partfun1(A_470,'#skF_4',C_471,D_472) = k7_relat_1(C_471,D_472)
      | ~ m1_subset_1(C_471,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_471) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2579,c_3429])).

tff(c_3541,plain,(
    ! [A_470,D_472] :
      ( k2_partfun1(A_470,'#skF_4','#skF_4',D_472) = k7_relat_1('#skF_4',D_472)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2577,c_3539])).

tff(c_3547,plain,(
    ! [A_470,D_472] : k2_partfun1(A_470,'#skF_4','#skF_4',D_472) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3077,c_3541])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2490,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2488,c_2488,c_14])).

tff(c_2578,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2559,c_2490])).

tff(c_2582,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2498])).

tff(c_2895,plain,(
    ! [A_358,B_359,C_360,D_361] :
      ( v1_funct_1(k2_partfun1(A_358,B_359,C_360,D_361))
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_358,B_359)))
      | ~ v1_funct_1(C_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2968,plain,(
    ! [A_371,C_372,D_373] :
      ( v1_funct_1(k2_partfun1(A_371,'#skF_4',C_372,D_373))
      | ~ m1_subset_1(C_372,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_372) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2579,c_2895])).

tff(c_2970,plain,(
    ! [A_371,D_373] :
      ( v1_funct_1(k2_partfun1(A_371,'#skF_4','#skF_4',D_373))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2577,c_2968])).

tff(c_2976,plain,(
    ! [A_371,D_373] : v1_funct_1(k2_partfun1(A_371,'#skF_4','#skF_4',D_373)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2970])).

tff(c_2555,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2545])).

tff(c_2567,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2493,c_2555])).

tff(c_2574,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2567])).

tff(c_2593,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2574,c_2559,c_2574,c_2574,c_2559,c_2574,c_2574,c_2559,c_50])).

tff(c_2594,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2593])).

tff(c_2651,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2582,c_2594])).

tff(c_3000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_2651])).

tff(c_3001,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),'#skF_4','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2593])).

tff(c_3203,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2578,c_2582,c_2582,c_2582,c_2582,c_3001])).

tff(c_3204,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3203])).

tff(c_3208,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_3204])).

tff(c_3549,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3547,c_3208])).

tff(c_3553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3549])).

tff(c_3555,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3203])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3579,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3555,c_16])).

tff(c_3059,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2559,c_2560])).

tff(c_3591,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3579,c_3059])).

tff(c_3554,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3203])).

tff(c_3598,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3591,c_3554])).

tff(c_3605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2576,c_3598])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.85  
% 4.71/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.85  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.71/1.85  
% 4.71/1.85  %Foreground sorts:
% 4.71/1.85  
% 4.71/1.85  
% 4.71/1.85  %Background operators:
% 4.71/1.85  
% 4.71/1.85  
% 4.71/1.85  %Foreground operators:
% 4.71/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.71/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.71/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.71/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.71/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.71/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.71/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.71/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.71/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.71/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.71/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.71/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.85  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.71/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.71/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.85  
% 4.71/1.88  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 4.71/1.88  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.71/1.88  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.71/1.88  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.71/1.88  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.71/1.88  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 4.71/1.88  tff(f_104, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.71/1.88  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.71/1.88  tff(f_98, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 4.71/1.88  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 4.71/1.88  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.71/1.88  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.71/1.88  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.71/1.88  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 4.71/1.88  tff(c_54, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.71/1.88  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.71/1.88  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.71/1.88  tff(c_108, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.71/1.88  tff(c_114, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_108])).
% 4.71/1.88  tff(c_118, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_114])).
% 4.71/1.88  tff(c_52, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.71/1.88  tff(c_96, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 4.71/1.88  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.71/1.88  tff(c_1890, plain, (![A_258, B_259, C_260]: (k1_relset_1(A_258, B_259, C_260)=k1_relat_1(C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.71/1.88  tff(c_1909, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1890])).
% 4.71/1.88  tff(c_2251, plain, (![B_302, A_303, C_304]: (k1_xboole_0=B_302 | k1_relset_1(A_303, B_302, C_304)=A_303 | ~v1_funct_2(C_304, A_303, B_302) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_303, B_302))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.71/1.88  tff(c_2264, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_2251])).
% 4.71/1.88  tff(c_2279, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1909, c_2264])).
% 4.71/1.88  tff(c_2280, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_96, c_2279])).
% 4.71/1.88  tff(c_26, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, A_15))=A_15 | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.71/1.88  tff(c_2294, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2280, c_26])).
% 4.71/1.88  tff(c_2300, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_2294])).
% 4.71/1.88  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.71/1.88  tff(c_2106, plain, (![A_289, B_290, C_291, D_292]: (k2_partfun1(A_289, B_290, C_291, D_292)=k7_relat_1(C_291, D_292) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~v1_funct_1(C_291))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.71/1.88  tff(c_2113, plain, (![D_292]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_292)=k7_relat_1('#skF_4', D_292) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_2106])).
% 4.71/1.88  tff(c_2124, plain, (![D_292]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_292)=k7_relat_1('#skF_4', D_292))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2113])).
% 4.71/1.88  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.71/1.88  tff(c_625, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.71/1.88  tff(c_640, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_625])).
% 4.71/1.88  tff(c_955, plain, (![B_158, A_159, C_160]: (k1_xboole_0=B_158 | k1_relset_1(A_159, B_158, C_160)=A_159 | ~v1_funct_2(C_160, A_159, B_158) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_159, B_158))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.71/1.88  tff(c_965, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_955])).
% 4.71/1.88  tff(c_978, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_640, c_965])).
% 4.71/1.88  tff(c_979, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_96, c_978])).
% 4.71/1.88  tff(c_999, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_979, c_26])).
% 4.71/1.88  tff(c_1005, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_999])).
% 4.71/1.88  tff(c_908, plain, (![A_143, B_144, C_145, D_146]: (k2_partfun1(A_143, B_144, C_145, D_146)=k7_relat_1(C_145, D_146) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_1(C_145))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.71/1.88  tff(c_915, plain, (![D_146]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_146)=k7_relat_1('#skF_4', D_146) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_908])).
% 4.71/1.88  tff(c_926, plain, (![D_146]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_146)=k7_relat_1('#skF_4', D_146))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_915])).
% 4.71/1.88  tff(c_1197, plain, (![A_173, B_174, C_175, D_176]: (m1_subset_1(k2_partfun1(A_173, B_174, C_175, D_176), k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1(C_175))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.71/1.88  tff(c_1221, plain, (![D_146]: (m1_subset_1(k7_relat_1('#skF_4', D_146), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_926, c_1197])).
% 4.71/1.88  tff(c_1253, plain, (![D_177]: (m1_subset_1(k7_relat_1('#skF_4', D_177), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1221])).
% 4.71/1.88  tff(c_30, plain, (![D_23, B_21, C_22, A_20]: (m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(B_21, C_22))) | ~r1_tarski(k1_relat_1(D_23), B_21) | ~m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(A_20, C_22))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.71/1.88  tff(c_1748, plain, (![D_251, B_252]: (m1_subset_1(k7_relat_1('#skF_4', D_251), k1_zfmisc_1(k2_zfmisc_1(B_252, '#skF_2'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_251)), B_252))), inference(resolution, [status(thm)], [c_1253, c_30])).
% 4.71/1.88  tff(c_413, plain, (![A_79, B_80, C_81, D_82]: (v1_funct_1(k2_partfun1(A_79, B_80, C_81, D_82)) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.71/1.88  tff(c_418, plain, (![D_82]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_82)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_413])).
% 4.71/1.88  tff(c_426, plain, (![D_82]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_82)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_418])).
% 4.71/1.88  tff(c_50, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.71/1.88  tff(c_143, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 4.71/1.88  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_426, c_143])).
% 4.71/1.88  tff(c_430, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_50])).
% 4.71/1.88  tff(c_559, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_430])).
% 4.71/1.88  tff(c_929, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_926, c_559])).
% 4.71/1.88  tff(c_1788, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_1748, c_929])).
% 4.71/1.88  tff(c_1803, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1005, c_1788])).
% 4.71/1.88  tff(c_1806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_6, c_1803])).
% 4.71/1.88  tff(c_1808, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_430])).
% 4.71/1.88  tff(c_1907, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1808, c_1890])).
% 4.71/1.88  tff(c_2127, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2124, c_2124, c_1907])).
% 4.71/1.88  tff(c_1807, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_430])).
% 4.71/1.88  tff(c_2132, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2124, c_1807])).
% 4.71/1.88  tff(c_2131, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2124, c_1808])).
% 4.71/1.88  tff(c_2437, plain, (![B_309, C_310, A_311]: (k1_xboole_0=B_309 | v1_funct_2(C_310, A_311, B_309) | k1_relset_1(A_311, B_309, C_310)!=A_311 | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_311, B_309))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.71/1.88  tff(c_2443, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_2131, c_2437])).
% 4.71/1.88  tff(c_2462, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2132, c_96, c_2443])).
% 4.71/1.88  tff(c_2476, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2127, c_2462])).
% 4.71/1.88  tff(c_2483, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2300, c_2476])).
% 4.71/1.88  tff(c_2487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_2483])).
% 4.71/1.88  tff(c_2488, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_52])).
% 4.71/1.88  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.71/1.88  tff(c_2493, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2488, c_8])).
% 4.71/1.88  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.71/1.88  tff(c_2492, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2488, c_2488, c_12])).
% 4.71/1.88  tff(c_2489, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 4.71/1.88  tff(c_2498, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2488, c_2489])).
% 4.71/1.88  tff(c_2533, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_2498, c_56])).
% 4.71/1.88  tff(c_2534, plain, (![A_317, B_318]: (r1_tarski(A_317, B_318) | ~m1_subset_1(A_317, k1_zfmisc_1(B_318)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.71/1.88  tff(c_2538, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_2533, c_2534])).
% 4.71/1.88  tff(c_2545, plain, (![B_323, A_324]: (B_323=A_324 | ~r1_tarski(B_323, A_324) | ~r1_tarski(A_324, B_323))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.71/1.88  tff(c_2549, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_2538, c_2545])).
% 4.71/1.88  tff(c_2559, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2493, c_2549])).
% 4.71/1.88  tff(c_2499, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2498, c_58])).
% 4.71/1.88  tff(c_2576, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2559, c_2499])).
% 4.71/1.88  tff(c_69, plain, (![A_39]: (k2_zfmisc_1(A_39, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.71/1.88  tff(c_73, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_69, c_22])).
% 4.71/1.88  tff(c_2491, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2488, c_73])).
% 4.71/1.88  tff(c_2580, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2491])).
% 4.71/1.88  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.71/1.88  tff(c_2560, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(resolution, [status(thm)], [c_2493, c_2545])).
% 4.71/1.88  tff(c_3060, plain, (![A_382]: (A_382='#skF_4' | ~r1_tarski(A_382, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2559, c_2560])).
% 4.71/1.88  tff(c_3068, plain, (![A_13]: (k7_relat_1('#skF_4', A_13)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_3060])).
% 4.71/1.88  tff(c_3077, plain, (![A_13]: (k7_relat_1('#skF_4', A_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2580, c_3068])).
% 4.71/1.88  tff(c_2577, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2533])).
% 4.71/1.88  tff(c_2579, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2559, c_2492])).
% 4.71/1.88  tff(c_3429, plain, (![A_430, B_431, C_432, D_433]: (k2_partfun1(A_430, B_431, C_432, D_433)=k7_relat_1(C_432, D_433) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))) | ~v1_funct_1(C_432))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.71/1.88  tff(c_3539, plain, (![A_470, C_471, D_472]: (k2_partfun1(A_470, '#skF_4', C_471, D_472)=k7_relat_1(C_471, D_472) | ~m1_subset_1(C_471, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_471))), inference(superposition, [status(thm), theory('equality')], [c_2579, c_3429])).
% 4.71/1.88  tff(c_3541, plain, (![A_470, D_472]: (k2_partfun1(A_470, '#skF_4', '#skF_4', D_472)=k7_relat_1('#skF_4', D_472) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2577, c_3539])).
% 4.71/1.88  tff(c_3547, plain, (![A_470, D_472]: (k2_partfun1(A_470, '#skF_4', '#skF_4', D_472)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3077, c_3541])).
% 4.71/1.88  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.71/1.88  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.71/1.88  tff(c_2490, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2488, c_2488, c_14])).
% 4.71/1.88  tff(c_2578, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2559, c_2490])).
% 4.71/1.88  tff(c_2582, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2498])).
% 4.71/1.88  tff(c_2895, plain, (![A_358, B_359, C_360, D_361]: (v1_funct_1(k2_partfun1(A_358, B_359, C_360, D_361)) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_358, B_359))) | ~v1_funct_1(C_360))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.71/1.88  tff(c_2968, plain, (![A_371, C_372, D_373]: (v1_funct_1(k2_partfun1(A_371, '#skF_4', C_372, D_373)) | ~m1_subset_1(C_372, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_372))), inference(superposition, [status(thm), theory('equality')], [c_2579, c_2895])).
% 4.71/1.88  tff(c_2970, plain, (![A_371, D_373]: (v1_funct_1(k2_partfun1(A_371, '#skF_4', '#skF_4', D_373)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2577, c_2968])).
% 4.71/1.88  tff(c_2976, plain, (![A_371, D_373]: (v1_funct_1(k2_partfun1(A_371, '#skF_4', '#skF_4', D_373)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2970])).
% 4.71/1.88  tff(c_2555, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_2545])).
% 4.71/1.88  tff(c_2567, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2493, c_2555])).
% 4.71/1.88  tff(c_2574, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2567])).
% 4.71/1.88  tff(c_2593, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2574, c_2559, c_2574, c_2574, c_2559, c_2574, c_2574, c_2559, c_50])).
% 4.71/1.88  tff(c_2594, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2593])).
% 4.71/1.88  tff(c_2651, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2582, c_2594])).
% 4.71/1.88  tff(c_3000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2976, c_2651])).
% 4.71/1.88  tff(c_3001, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), '#skF_4', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(splitRight, [status(thm)], [c_2593])).
% 4.71/1.88  tff(c_3203, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2578, c_2582, c_2582, c_2582, c_2582, c_3001])).
% 4.71/1.88  tff(c_3204, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3203])).
% 4.71/1.88  tff(c_3208, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_18, c_3204])).
% 4.71/1.88  tff(c_3549, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3547, c_3208])).
% 4.71/1.88  tff(c_3553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3549])).
% 4.71/1.88  tff(c_3555, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3203])).
% 4.71/1.88  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.71/1.88  tff(c_3579, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_3555, c_16])).
% 4.71/1.88  tff(c_3059, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2559, c_2560])).
% 4.71/1.88  tff(c_3591, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_3579, c_3059])).
% 4.71/1.88  tff(c_3554, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_3203])).
% 4.71/1.88  tff(c_3598, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3591, c_3554])).
% 4.71/1.88  tff(c_3605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2576, c_3598])).
% 4.71/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.88  
% 4.71/1.88  Inference rules
% 4.71/1.88  ----------------------
% 4.71/1.88  #Ref     : 0
% 4.71/1.88  #Sup     : 757
% 4.71/1.88  #Fact    : 0
% 4.71/1.88  #Define  : 0
% 4.71/1.88  #Split   : 20
% 4.71/1.88  #Chain   : 0
% 4.71/1.88  #Close   : 0
% 4.71/1.88  
% 4.71/1.88  Ordering : KBO
% 4.71/1.88  
% 4.71/1.88  Simplification rules
% 4.71/1.88  ----------------------
% 4.71/1.88  #Subsume      : 69
% 4.71/1.88  #Demod        : 659
% 4.71/1.88  #Tautology    : 394
% 4.71/1.88  #SimpNegUnit  : 18
% 4.71/1.88  #BackRed      : 53
% 4.71/1.88  
% 4.71/1.88  #Partial instantiations: 0
% 4.71/1.88  #Strategies tried      : 1
% 4.71/1.88  
% 4.71/1.88  Timing (in seconds)
% 4.71/1.88  ----------------------
% 4.71/1.88  Preprocessing        : 0.33
% 4.71/1.88  Parsing              : 0.17
% 4.71/1.88  CNF conversion       : 0.02
% 4.71/1.88  Main loop            : 0.76
% 4.71/1.88  Inferencing          : 0.28
% 4.71/1.88  Reduction            : 0.27
% 4.71/1.88  Demodulation         : 0.18
% 4.71/1.88  BG Simplification    : 0.03
% 4.71/1.88  Subsumption          : 0.13
% 4.71/1.88  Abstraction          : 0.03
% 4.71/1.88  MUC search           : 0.00
% 4.71/1.88  Cooper               : 0.00
% 4.71/1.88  Total                : 1.14
% 4.71/1.88  Index Insertion      : 0.00
% 4.71/1.88  Index Deletion       : 0.00
% 4.71/1.88  Index Matching       : 0.00
% 4.71/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
