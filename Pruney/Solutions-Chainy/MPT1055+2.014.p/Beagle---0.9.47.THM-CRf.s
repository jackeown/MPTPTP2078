%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:20 EST 2020

% Result     : Theorem 13.67s
% Output     : CNFRefutation 13.67s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 191 expanded)
%              Number of leaves         :   46 (  83 expanded)
%              Depth                    :    8
%              Number of atoms          :  176 ( 491 expanded)
%              Number of equality atoms :   24 (  41 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_196,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_159,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_50,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_113,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_136,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(A_100,B_101)
      | ~ m1_subset_1(A_100,k1_zfmisc_1(B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_156,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_136])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28006,plain,(
    k2_xboole_0('#skF_5','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_156,c_4])).

tff(c_28144,plain,(
    ! [A_787,C_788,B_789] :
      ( r1_tarski(A_787,C_788)
      | ~ r1_tarski(k2_xboole_0(A_787,B_789),C_788) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28150,plain,(
    ! [C_788] :
      ( r1_tarski('#skF_5',C_788)
      | ~ r1_tarski('#skF_2',C_788) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28006,c_28144])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_30165,plain,(
    ! [A_920,B_921,C_922,D_923] :
      ( k8_relset_1(A_920,B_921,C_922,D_923) = k10_relat_1(C_922,D_923)
      | ~ m1_subset_1(C_922,k1_zfmisc_1(k2_zfmisc_1(A_920,B_921))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30179,plain,(
    ! [D_923] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_923) = k10_relat_1('#skF_4',D_923) ),
    inference(resolution,[status(thm)],[c_72,c_30165])).

tff(c_32,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_244,plain,(
    ! [B_116,A_117] :
      ( v1_relat_1(B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_117))
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_250,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_244])).

tff(c_264,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_250])).

tff(c_1387,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( k8_relset_1(A_211,B_212,C_213,D_214) = k10_relat_1(C_213,D_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1401,plain,(
    ! [D_214] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_214) = k10_relat_1('#skF_4',D_214) ),
    inference(resolution,[status(thm)],[c_72,c_1387])).

tff(c_82,plain,
    ( ~ r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6'))
    | ~ r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_162,plain,(
    ~ r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_88,plain,
    ( r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_209,plain,(
    r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_88])).

tff(c_1407,plain,(
    r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_209])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_34,plain,(
    ! [C_31,A_29,B_30] :
      ( r1_tarski(k9_relat_1(C_31,A_29),k9_relat_1(C_31,B_30))
      | ~ r1_tarski(A_29,B_30)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_789,plain,(
    ! [B_162,A_163] :
      ( r1_tarski(k9_relat_1(B_162,k10_relat_1(B_162,A_163)),A_163)
      | ~ v1_funct_1(B_162)
      | ~ v1_relat_1(B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6554,plain,(
    ! [A_381,A_382,B_383] :
      ( r1_tarski(A_381,A_382)
      | ~ r1_tarski(A_381,k9_relat_1(B_383,k10_relat_1(B_383,A_382)))
      | ~ v1_funct_1(B_383)
      | ~ v1_relat_1(B_383) ) ),
    inference(resolution,[status(thm)],[c_789,c_6])).

tff(c_27702,plain,(
    ! [C_769,A_770,A_771] :
      ( r1_tarski(k9_relat_1(C_769,A_770),A_771)
      | ~ v1_funct_1(C_769)
      | ~ r1_tarski(A_770,k10_relat_1(C_769,A_771))
      | ~ v1_relat_1(C_769) ) ),
    inference(resolution,[status(thm)],[c_34,c_6554])).

tff(c_1308,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( k7_relset_1(A_200,B_201,C_202,D_203) = k9_relat_1(C_202,D_203)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1322,plain,(
    ! [D_203] : k7_relset_1('#skF_2','#skF_3','#skF_4',D_203) = k9_relat_1('#skF_4',D_203) ),
    inference(resolution,[status(thm)],[c_72,c_1308])).

tff(c_1324,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1322,c_162])).

tff(c_27898,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_27702,c_1324])).

tff(c_28000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_1407,c_76,c_27898])).

tff(c_28001,plain,(
    ~ r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_30182,plain,(
    ~ r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30179,c_28001])).

tff(c_28074,plain,(
    ! [B_780,A_781] :
      ( v1_relat_1(B_780)
      | ~ m1_subset_1(B_780,k1_zfmisc_1(A_781))
      | ~ v1_relat_1(A_781) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28080,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_28074])).

tff(c_28094,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28080])).

tff(c_30298,plain,(
    ! [A_930,B_931,C_932,D_933] :
      ( k7_relset_1(A_930,B_931,C_932,D_933) = k9_relat_1(C_932,D_933)
      | ~ m1_subset_1(C_932,k1_zfmisc_1(k2_zfmisc_1(A_930,B_931))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_30312,plain,(
    ! [D_933] : k7_relset_1('#skF_2','#skF_3','#skF_4',D_933) = k9_relat_1('#skF_4',D_933) ),
    inference(resolution,[status(thm)],[c_72,c_30298])).

tff(c_28015,plain,(
    r1_tarski('#skF_5',k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_28038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28001,c_28015])).

tff(c_28039,plain,(
    r1_tarski(k7_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_30319,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30312,c_28039])).

tff(c_31151,plain,(
    ! [A_965,C_966,B_967] :
      ( r1_tarski(A_965,k10_relat_1(C_966,B_967))
      | ~ r1_tarski(k9_relat_1(C_966,A_965),B_967)
      | ~ r1_tarski(A_965,k1_relat_1(C_966))
      | ~ v1_funct_1(C_966)
      | ~ v1_relat_1(C_966) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_31163,plain,
    ( r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30319,c_31151])).

tff(c_31185,plain,
    ( r1_tarski('#skF_5',k10_relat_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28094,c_76,c_31163])).

tff(c_31186,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_30182,c_31185])).

tff(c_31268,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_28150,c_31186])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_31458,plain,(
    ! [B_979,A_980,C_981] :
      ( k1_xboole_0 = B_979
      | k8_relset_1(A_980,B_979,C_981,B_979) = A_980
      | ~ m1_subset_1(C_981,k1_zfmisc_1(k2_zfmisc_1(A_980,B_979)))
      | ~ v1_funct_2(C_981,A_980,B_979)
      | ~ v1_funct_1(C_981) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_31465,plain,
    ( k1_xboole_0 = '#skF_3'
    | k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_31458])).

tff(c_31477,plain,
    ( k1_xboole_0 = '#skF_3'
    | k10_relat_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_30179,c_31465])).

tff(c_31490,plain,(
    k10_relat_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_31477])).

tff(c_36,plain,(
    ! [B_33,A_32] :
      ( r1_tarski(k10_relat_1(B_33,A_32),k1_relat_1(B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_31497,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_31490,c_36])).

tff(c_31503,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28094,c_31497])).

tff(c_31505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31268,c_31503])).

tff(c_31506,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_31477])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1('#skF_1'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28064,plain,(
    ! [A_776,B_777] :
      ( r2_hidden(A_776,B_777)
      | v1_xboole_0(B_777)
      | ~ m1_subset_1(A_776,B_777) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [B_40,A_39] :
      ( ~ r1_tarski(B_40,A_39)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28705,plain,(
    ! [B_843,A_844] :
      ( ~ r1_tarski(B_843,A_844)
      | v1_xboole_0(B_843)
      | ~ m1_subset_1(A_844,B_843) ) ),
    inference(resolution,[status(thm)],[c_28064,c_42])).

tff(c_28769,plain,(
    ! [A_9] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_28705])).

tff(c_28773,plain,(
    ! [A_845] : ~ m1_subset_1(A_845,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_28769])).

tff(c_28778,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_16,c_28773])).

tff(c_28779,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_28769])).

tff(c_31517,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31506,c_28779])).

tff(c_31538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_31517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:54:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.67/6.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.67/6.11  
% 13.67/6.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.67/6.12  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 13.67/6.12  
% 13.67/6.12  %Foreground sorts:
% 13.67/6.12  
% 13.67/6.12  
% 13.67/6.12  %Background operators:
% 13.67/6.12  
% 13.67/6.12  
% 13.67/6.12  %Foreground operators:
% 13.67/6.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.67/6.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.67/6.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.67/6.12  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 13.67/6.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.67/6.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.67/6.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.67/6.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.67/6.12  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 13.67/6.12  tff('#skF_5', type, '#skF_5': $i).
% 13.67/6.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.67/6.12  tff('#skF_6', type, '#skF_6': $i).
% 13.67/6.12  tff('#skF_2', type, '#skF_2': $i).
% 13.67/6.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.67/6.12  tff('#skF_3', type, '#skF_3': $i).
% 13.67/6.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.67/6.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.67/6.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.67/6.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.67/6.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.67/6.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.67/6.12  tff('#skF_4', type, '#skF_4': $i).
% 13.67/6.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.67/6.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.67/6.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.67/6.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.67/6.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.67/6.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.67/6.12  
% 13.67/6.13  tff(f_196, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 13.67/6.13  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.67/6.13  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.67/6.13  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 13.67/6.13  tff(f_127, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 13.67/6.13  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.67/6.13  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.67/6.13  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 13.67/6.13  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 13.67/6.13  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.67/6.13  tff(f_123, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 13.67/6.13  tff(f_108, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 13.67/6.13  tff(f_159, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 13.67/6.13  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 13.67/6.13  tff(f_50, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 13.67/6.13  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.67/6.13  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 13.67/6.13  tff(f_113, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 13.67/6.13  tff(c_78, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 13.67/6.13  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 13.67/6.13  tff(c_136, plain, (![A_100, B_101]: (r1_tarski(A_100, B_101) | ~m1_subset_1(A_100, k1_zfmisc_1(B_101)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.67/6.13  tff(c_156, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_136])).
% 13.67/6.13  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.67/6.13  tff(c_28006, plain, (k2_xboole_0('#skF_5', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_156, c_4])).
% 13.67/6.13  tff(c_28144, plain, (![A_787, C_788, B_789]: (r1_tarski(A_787, C_788) | ~r1_tarski(k2_xboole_0(A_787, B_789), C_788))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.67/6.13  tff(c_28150, plain, (![C_788]: (r1_tarski('#skF_5', C_788) | ~r1_tarski('#skF_2', C_788))), inference(superposition, [status(thm), theory('equality')], [c_28006, c_28144])).
% 13.67/6.13  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 13.67/6.13  tff(c_30165, plain, (![A_920, B_921, C_922, D_923]: (k8_relset_1(A_920, B_921, C_922, D_923)=k10_relat_1(C_922, D_923) | ~m1_subset_1(C_922, k1_zfmisc_1(k2_zfmisc_1(A_920, B_921))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.67/6.13  tff(c_30179, plain, (![D_923]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_923)=k10_relat_1('#skF_4', D_923))), inference(resolution, [status(thm)], [c_72, c_30165])).
% 13.67/6.13  tff(c_32, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.67/6.13  tff(c_244, plain, (![B_116, A_117]: (v1_relat_1(B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(A_117)) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.67/6.13  tff(c_250, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_244])).
% 13.67/6.13  tff(c_264, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_250])).
% 13.67/6.13  tff(c_1387, plain, (![A_211, B_212, C_213, D_214]: (k8_relset_1(A_211, B_212, C_213, D_214)=k10_relat_1(C_213, D_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.67/6.13  tff(c_1401, plain, (![D_214]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_214)=k10_relat_1('#skF_4', D_214))), inference(resolution, [status(thm)], [c_72, c_1387])).
% 13.67/6.13  tff(c_82, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')) | ~r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_196])).
% 13.67/6.13  tff(c_162, plain, (~r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_82])).
% 13.67/6.13  tff(c_88, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 13.67/6.13  tff(c_209, plain, (r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_162, c_88])).
% 13.67/6.13  tff(c_1407, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_209])).
% 13.67/6.13  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 13.67/6.13  tff(c_34, plain, (![C_31, A_29, B_30]: (r1_tarski(k9_relat_1(C_31, A_29), k9_relat_1(C_31, B_30)) | ~r1_tarski(A_29, B_30) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.67/6.13  tff(c_789, plain, (![B_162, A_163]: (r1_tarski(k9_relat_1(B_162, k10_relat_1(B_162, A_163)), A_163) | ~v1_funct_1(B_162) | ~v1_relat_1(B_162))), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.67/6.13  tff(c_6, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.67/6.13  tff(c_6554, plain, (![A_381, A_382, B_383]: (r1_tarski(A_381, A_382) | ~r1_tarski(A_381, k9_relat_1(B_383, k10_relat_1(B_383, A_382))) | ~v1_funct_1(B_383) | ~v1_relat_1(B_383))), inference(resolution, [status(thm)], [c_789, c_6])).
% 13.67/6.13  tff(c_27702, plain, (![C_769, A_770, A_771]: (r1_tarski(k9_relat_1(C_769, A_770), A_771) | ~v1_funct_1(C_769) | ~r1_tarski(A_770, k10_relat_1(C_769, A_771)) | ~v1_relat_1(C_769))), inference(resolution, [status(thm)], [c_34, c_6554])).
% 13.67/6.13  tff(c_1308, plain, (![A_200, B_201, C_202, D_203]: (k7_relset_1(A_200, B_201, C_202, D_203)=k9_relat_1(C_202, D_203) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 13.67/6.13  tff(c_1322, plain, (![D_203]: (k7_relset_1('#skF_2', '#skF_3', '#skF_4', D_203)=k9_relat_1('#skF_4', D_203))), inference(resolution, [status(thm)], [c_72, c_1308])).
% 13.67/6.13  tff(c_1324, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1322, c_162])).
% 13.67/6.13  tff(c_27898, plain, (~v1_funct_1('#skF_4') | ~r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_27702, c_1324])).
% 13.67/6.13  tff(c_28000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_1407, c_76, c_27898])).
% 13.67/6.13  tff(c_28001, plain, (~r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_82])).
% 13.67/6.13  tff(c_30182, plain, (~r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30179, c_28001])).
% 13.67/6.13  tff(c_28074, plain, (![B_780, A_781]: (v1_relat_1(B_780) | ~m1_subset_1(B_780, k1_zfmisc_1(A_781)) | ~v1_relat_1(A_781))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.67/6.13  tff(c_28080, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_28074])).
% 13.67/6.13  tff(c_28094, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28080])).
% 13.67/6.13  tff(c_30298, plain, (![A_930, B_931, C_932, D_933]: (k7_relset_1(A_930, B_931, C_932, D_933)=k9_relat_1(C_932, D_933) | ~m1_subset_1(C_932, k1_zfmisc_1(k2_zfmisc_1(A_930, B_931))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 13.67/6.13  tff(c_30312, plain, (![D_933]: (k7_relset_1('#skF_2', '#skF_3', '#skF_4', D_933)=k9_relat_1('#skF_4', D_933))), inference(resolution, [status(thm)], [c_72, c_30298])).
% 13.67/6.13  tff(c_28015, plain, (r1_tarski('#skF_5', k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_88])).
% 13.67/6.13  tff(c_28038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28001, c_28015])).
% 13.67/6.13  tff(c_28039, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_88])).
% 13.67/6.13  tff(c_30319, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30312, c_28039])).
% 13.67/6.13  tff(c_31151, plain, (![A_965, C_966, B_967]: (r1_tarski(A_965, k10_relat_1(C_966, B_967)) | ~r1_tarski(k9_relat_1(C_966, A_965), B_967) | ~r1_tarski(A_965, k1_relat_1(C_966)) | ~v1_funct_1(C_966) | ~v1_relat_1(C_966))), inference(cnfTransformation, [status(thm)], [f_108])).
% 13.67/6.13  tff(c_31163, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30319, c_31151])).
% 13.67/6.13  tff(c_31185, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28094, c_76, c_31163])).
% 13.67/6.13  tff(c_31186, plain, (~r1_tarski('#skF_5', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_30182, c_31185])).
% 13.67/6.13  tff(c_31268, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_28150, c_31186])).
% 13.67/6.13  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 13.67/6.13  tff(c_31458, plain, (![B_979, A_980, C_981]: (k1_xboole_0=B_979 | k8_relset_1(A_980, B_979, C_981, B_979)=A_980 | ~m1_subset_1(C_981, k1_zfmisc_1(k2_zfmisc_1(A_980, B_979))) | ~v1_funct_2(C_981, A_980, B_979) | ~v1_funct_1(C_981))), inference(cnfTransformation, [status(thm)], [f_159])).
% 13.67/6.13  tff(c_31465, plain, (k1_xboole_0='#skF_3' | k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_31458])).
% 13.67/6.13  tff(c_31477, plain, (k1_xboole_0='#skF_3' | k10_relat_1('#skF_4', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_30179, c_31465])).
% 13.67/6.13  tff(c_31490, plain, (k10_relat_1('#skF_4', '#skF_3')='#skF_2'), inference(splitLeft, [status(thm)], [c_31477])).
% 13.67/6.13  tff(c_36, plain, (![B_33, A_32]: (r1_tarski(k10_relat_1(B_33, A_32), k1_relat_1(B_33)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.67/6.13  tff(c_31497, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_31490, c_36])).
% 13.67/6.13  tff(c_31503, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28094, c_31497])).
% 13.67/6.13  tff(c_31505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31268, c_31503])).
% 13.67/6.13  tff(c_31506, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_31477])).
% 13.67/6.13  tff(c_16, plain, (![A_12]: (m1_subset_1('#skF_1'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.67/6.13  tff(c_8, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.67/6.13  tff(c_28064, plain, (![A_776, B_777]: (r2_hidden(A_776, B_777) | v1_xboole_0(B_777) | ~m1_subset_1(A_776, B_777))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.67/6.13  tff(c_42, plain, (![B_40, A_39]: (~r1_tarski(B_40, A_39) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.67/6.13  tff(c_28705, plain, (![B_843, A_844]: (~r1_tarski(B_843, A_844) | v1_xboole_0(B_843) | ~m1_subset_1(A_844, B_843))), inference(resolution, [status(thm)], [c_28064, c_42])).
% 13.67/6.13  tff(c_28769, plain, (![A_9]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_28705])).
% 13.67/6.13  tff(c_28773, plain, (![A_845]: (~m1_subset_1(A_845, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_28769])).
% 13.67/6.13  tff(c_28778, plain, $false, inference(resolution, [status(thm)], [c_16, c_28773])).
% 13.67/6.13  tff(c_28779, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_28769])).
% 13.67/6.13  tff(c_31517, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31506, c_28779])).
% 13.67/6.13  tff(c_31538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_31517])).
% 13.67/6.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.67/6.13  
% 13.67/6.13  Inference rules
% 13.67/6.13  ----------------------
% 13.67/6.13  #Ref     : 0
% 13.67/6.13  #Sup     : 6666
% 13.67/6.13  #Fact    : 0
% 13.67/6.13  #Define  : 0
% 13.67/6.13  #Split   : 110
% 13.67/6.13  #Chain   : 0
% 13.67/6.13  #Close   : 0
% 13.67/6.13  
% 13.67/6.13  Ordering : KBO
% 13.67/6.13  
% 13.67/6.13  Simplification rules
% 13.67/6.13  ----------------------
% 13.67/6.13  #Subsume      : 1950
% 13.67/6.13  #Demod        : 2587
% 13.67/6.13  #Tautology    : 2118
% 13.67/6.13  #SimpNegUnit  : 243
% 13.67/6.13  #BackRed      : 323
% 13.67/6.13  
% 13.67/6.13  #Partial instantiations: 0
% 13.67/6.13  #Strategies tried      : 1
% 13.67/6.13  
% 13.67/6.13  Timing (in seconds)
% 13.67/6.13  ----------------------
% 13.67/6.14  Preprocessing        : 0.41
% 13.67/6.14  Parsing              : 0.22
% 13.67/6.14  CNF conversion       : 0.03
% 13.67/6.14  Main loop            : 4.94
% 13.67/6.14  Inferencing          : 1.10
% 13.67/6.14  Reduction            : 2.03
% 13.67/6.14  Demodulation         : 1.49
% 13.67/6.14  BG Simplification    : 0.09
% 13.67/6.14  Subsumption          : 1.34
% 13.67/6.14  Abstraction          : 0.13
% 13.67/6.14  MUC search           : 0.00
% 13.67/6.14  Cooper               : 0.00
% 13.67/6.14  Total                : 5.39
% 13.67/6.14  Index Insertion      : 0.00
% 13.67/6.14  Index Deletion       : 0.00
% 13.67/6.14  Index Matching       : 0.00
% 13.67/6.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
