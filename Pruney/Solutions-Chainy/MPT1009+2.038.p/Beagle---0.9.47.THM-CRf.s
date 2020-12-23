%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:47 EST 2020

% Result     : Theorem 13.37s
% Output     : CNFRefutation 13.37s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 517 expanded)
%              Number of leaves         :   42 ( 202 expanded)
%              Depth                    :   14
%              Number of atoms          :  178 (1314 expanded)
%              Number of equality atoms :   89 ( 612 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_120,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_215,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_228,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_215])).

tff(c_48,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,A_20),k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14390,plain,(
    ! [A_530,B_531,C_532,D_533] :
      ( k7_relset_1(A_530,B_531,C_532,D_533) = k9_relat_1(C_532,D_533)
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k2_zfmisc_1(A_530,B_531))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_14404,plain,(
    ! [D_533] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_533) = k9_relat_1('#skF_4',D_533) ),
    inference(resolution,[status(thm)],[c_72,c_14390])).

tff(c_14300,plain,(
    ! [B_519,A_520] :
      ( k1_tarski(k1_funct_1(B_519,A_520)) = k2_relat_1(B_519)
      | k1_tarski(A_520) != k1_relat_1(B_519)
      | ~ v1_funct_1(B_519)
      | ~ v1_relat_1(B_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_68,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14306,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14300,c_68])).

tff(c_14327,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_76,c_14306])).

tff(c_14421,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14404,c_14327])).

tff(c_14422,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_14421])).

tff(c_418,plain,(
    ! [C_109,A_110,B_111] :
      ( v4_relat_1(C_109,A_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_433,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_418])).

tff(c_46,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14463,plain,(
    ! [A_543,B_544,C_545,D_546] :
      ( k1_enumset1(A_543,B_544,C_545) = D_546
      | k2_tarski(A_543,C_545) = D_546
      | k2_tarski(B_544,C_545) = D_546
      | k2_tarski(A_543,B_544) = D_546
      | k1_tarski(C_545) = D_546
      | k1_tarski(B_544) = D_546
      | k1_tarski(A_543) = D_546
      | k1_xboole_0 = D_546
      | ~ r1_tarski(D_546,k1_enumset1(A_543,B_544,C_545)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14485,plain,(
    ! [A_5,B_6,D_546] :
      ( k1_enumset1(A_5,A_5,B_6) = D_546
      | k2_tarski(A_5,B_6) = D_546
      | k2_tarski(A_5,B_6) = D_546
      | k2_tarski(A_5,A_5) = D_546
      | k1_tarski(B_6) = D_546
      | k1_tarski(A_5) = D_546
      | k1_tarski(A_5) = D_546
      | k1_xboole_0 = D_546
      | ~ r1_tarski(D_546,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_14463])).

tff(c_17699,plain,(
    ! [A_734,B_735,D_736] :
      ( k2_tarski(A_734,B_735) = D_736
      | k2_tarski(A_734,B_735) = D_736
      | k2_tarski(A_734,B_735) = D_736
      | k1_tarski(A_734) = D_736
      | k1_tarski(B_735) = D_736
      | k1_tarski(A_734) = D_736
      | k1_tarski(A_734) = D_736
      | k1_xboole_0 = D_736
      | ~ r1_tarski(D_736,k2_tarski(A_734,B_735)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_14485])).

tff(c_17722,plain,(
    ! [A_4,D_736] :
      ( k2_tarski(A_4,A_4) = D_736
      | k2_tarski(A_4,A_4) = D_736
      | k2_tarski(A_4,A_4) = D_736
      | k1_tarski(A_4) = D_736
      | k1_tarski(A_4) = D_736
      | k1_tarski(A_4) = D_736
      | k1_tarski(A_4) = D_736
      | k1_xboole_0 = D_736
      | ~ r1_tarski(D_736,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_17699])).

tff(c_25828,plain,(
    ! [A_880,D_881] :
      ( k1_tarski(A_880) = D_881
      | k1_tarski(A_880) = D_881
      | k1_tarski(A_880) = D_881
      | k1_tarski(A_880) = D_881
      | k1_tarski(A_880) = D_881
      | k1_tarski(A_880) = D_881
      | k1_tarski(A_880) = D_881
      | k1_xboole_0 = D_881
      | ~ r1_tarski(D_881,k1_tarski(A_880)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_17722])).

tff(c_25863,plain,(
    ! [A_882,B_883] :
      ( k1_tarski(A_882) = k1_relat_1(B_883)
      | k1_relat_1(B_883) = k1_xboole_0
      | ~ v4_relat_1(B_883,k1_tarski(A_882))
      | ~ v1_relat_1(B_883) ) ),
    inference(resolution,[status(thm)],[c_46,c_25828])).

tff(c_25945,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_433,c_25863])).

tff(c_25987,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_25945])).

tff(c_25988,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_14422,c_25987])).

tff(c_14235,plain,(
    ! [A_514] :
      ( m1_subset_1(A_514,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_514),k2_relat_1(A_514))))
      | ~ v1_funct_1(A_514)
      | ~ v1_relat_1(A_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14346,plain,(
    ! [A_525] :
      ( r1_tarski(A_525,k2_zfmisc_1(k1_relat_1(A_525),k2_relat_1(A_525)))
      | ~ v1_funct_1(A_525)
      | ~ v1_relat_1(A_525) ) ),
    inference(resolution,[status(thm)],[c_14235,c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14369,plain,(
    ! [A_525] :
      ( k2_zfmisc_1(k1_relat_1(A_525),k2_relat_1(A_525)) = A_525
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_525),k2_relat_1(A_525)),A_525)
      | ~ v1_funct_1(A_525)
      | ~ v1_relat_1(A_525) ) ),
    inference(resolution,[status(thm)],[c_14346,c_2])).

tff(c_26074,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25988,c_14369])).

tff(c_26224,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_76,c_8,c_20,c_20,c_25988,c_26074])).

tff(c_26377,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26224,c_8])).

tff(c_50,plain,(
    ! [A_22] : k9_relat_1(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26376,plain,(
    ! [A_22] : k9_relat_1('#skF_4',A_22) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26224,c_26224,c_50])).

tff(c_14405,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14404,c_68])).

tff(c_26931,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26376,c_14405])).

tff(c_26935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26377,c_26931])).

tff(c_26937,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_14421])).

tff(c_52,plain,(
    ! [B_24,A_23] :
      ( k1_tarski(k1_funct_1(B_24,A_23)) = k2_relat_1(B_24)
      | k1_tarski(A_23) != k1_relat_1(B_24)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14417,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_14405])).

tff(c_14419,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_76,c_14417])).

tff(c_14420,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_14419])).

tff(c_26972,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26937,c_14420])).

tff(c_26973,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_14419])).

tff(c_27103,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_26973])).

tff(c_27107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_27103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:55:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.37/5.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.37/5.44  
% 13.37/5.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.37/5.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.37/5.44  
% 13.37/5.44  %Foreground sorts:
% 13.37/5.44  
% 13.37/5.44  
% 13.37/5.44  %Background operators:
% 13.37/5.44  
% 13.37/5.44  
% 13.37/5.44  %Foreground operators:
% 13.37/5.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.37/5.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.37/5.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.37/5.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.37/5.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.37/5.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.37/5.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.37/5.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 13.37/5.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.37/5.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.37/5.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.37/5.44  tff('#skF_2', type, '#skF_2': $i).
% 13.37/5.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.37/5.44  tff('#skF_3', type, '#skF_3': $i).
% 13.37/5.44  tff('#skF_1', type, '#skF_1': $i).
% 13.37/5.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.37/5.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.37/5.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.37/5.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.37/5.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.37/5.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.37/5.44  tff('#skF_4', type, '#skF_4': $i).
% 13.37/5.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.37/5.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.37/5.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.37/5.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.37/5.44  
% 13.37/5.45  tff(f_132, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 13.37/5.45  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.37/5.45  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 13.37/5.45  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.37/5.45  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.37/5.45  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 13.37/5.45  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 13.37/5.45  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.37/5.45  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 13.37/5.45  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 13.37/5.45  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 13.37/5.45  tff(f_72, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 13.37/5.45  tff(f_120, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 13.37/5.45  tff(f_76, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.37/5.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.37/5.45  tff(f_88, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 13.37/5.45  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 13.37/5.45  tff(c_215, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.37/5.45  tff(c_228, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_215])).
% 13.37/5.45  tff(c_48, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, A_20), k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.37/5.45  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 13.37/5.45  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.37/5.45  tff(c_20, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.37/5.45  tff(c_14390, plain, (![A_530, B_531, C_532, D_533]: (k7_relset_1(A_530, B_531, C_532, D_533)=k9_relat_1(C_532, D_533) | ~m1_subset_1(C_532, k1_zfmisc_1(k2_zfmisc_1(A_530, B_531))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 13.37/5.45  tff(c_14404, plain, (![D_533]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_533)=k9_relat_1('#skF_4', D_533))), inference(resolution, [status(thm)], [c_72, c_14390])).
% 13.37/5.45  tff(c_14300, plain, (![B_519, A_520]: (k1_tarski(k1_funct_1(B_519, A_520))=k2_relat_1(B_519) | k1_tarski(A_520)!=k1_relat_1(B_519) | ~v1_funct_1(B_519) | ~v1_relat_1(B_519))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.37/5.45  tff(c_68, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 13.37/5.45  tff(c_14306, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14300, c_68])).
% 13.37/5.45  tff(c_14327, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_76, c_14306])).
% 13.37/5.45  tff(c_14421, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14404, c_14327])).
% 13.37/5.45  tff(c_14422, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_14421])).
% 13.37/5.45  tff(c_418, plain, (![C_109, A_110, B_111]: (v4_relat_1(C_109, A_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.37/5.45  tff(c_433, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_72, c_418])).
% 13.37/5.45  tff(c_46, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.37/5.45  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.37/5.45  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.37/5.45  tff(c_14463, plain, (![A_543, B_544, C_545, D_546]: (k1_enumset1(A_543, B_544, C_545)=D_546 | k2_tarski(A_543, C_545)=D_546 | k2_tarski(B_544, C_545)=D_546 | k2_tarski(A_543, B_544)=D_546 | k1_tarski(C_545)=D_546 | k1_tarski(B_544)=D_546 | k1_tarski(A_543)=D_546 | k1_xboole_0=D_546 | ~r1_tarski(D_546, k1_enumset1(A_543, B_544, C_545)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.37/5.45  tff(c_14485, plain, (![A_5, B_6, D_546]: (k1_enumset1(A_5, A_5, B_6)=D_546 | k2_tarski(A_5, B_6)=D_546 | k2_tarski(A_5, B_6)=D_546 | k2_tarski(A_5, A_5)=D_546 | k1_tarski(B_6)=D_546 | k1_tarski(A_5)=D_546 | k1_tarski(A_5)=D_546 | k1_xboole_0=D_546 | ~r1_tarski(D_546, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_14463])).
% 13.37/5.45  tff(c_17699, plain, (![A_734, B_735, D_736]: (k2_tarski(A_734, B_735)=D_736 | k2_tarski(A_734, B_735)=D_736 | k2_tarski(A_734, B_735)=D_736 | k1_tarski(A_734)=D_736 | k1_tarski(B_735)=D_736 | k1_tarski(A_734)=D_736 | k1_tarski(A_734)=D_736 | k1_xboole_0=D_736 | ~r1_tarski(D_736, k2_tarski(A_734, B_735)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_14485])).
% 13.37/5.45  tff(c_17722, plain, (![A_4, D_736]: (k2_tarski(A_4, A_4)=D_736 | k2_tarski(A_4, A_4)=D_736 | k2_tarski(A_4, A_4)=D_736 | k1_tarski(A_4)=D_736 | k1_tarski(A_4)=D_736 | k1_tarski(A_4)=D_736 | k1_tarski(A_4)=D_736 | k1_xboole_0=D_736 | ~r1_tarski(D_736, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_17699])).
% 13.37/5.45  tff(c_25828, plain, (![A_880, D_881]: (k1_tarski(A_880)=D_881 | k1_tarski(A_880)=D_881 | k1_tarski(A_880)=D_881 | k1_tarski(A_880)=D_881 | k1_tarski(A_880)=D_881 | k1_tarski(A_880)=D_881 | k1_tarski(A_880)=D_881 | k1_xboole_0=D_881 | ~r1_tarski(D_881, k1_tarski(A_880)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_10, c_17722])).
% 13.37/5.45  tff(c_25863, plain, (![A_882, B_883]: (k1_tarski(A_882)=k1_relat_1(B_883) | k1_relat_1(B_883)=k1_xboole_0 | ~v4_relat_1(B_883, k1_tarski(A_882)) | ~v1_relat_1(B_883))), inference(resolution, [status(thm)], [c_46, c_25828])).
% 13.37/5.45  tff(c_25945, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_433, c_25863])).
% 13.37/5.45  tff(c_25987, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_228, c_25945])).
% 13.37/5.45  tff(c_25988, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_14422, c_25987])).
% 13.37/5.45  tff(c_14235, plain, (![A_514]: (m1_subset_1(A_514, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_514), k2_relat_1(A_514)))) | ~v1_funct_1(A_514) | ~v1_relat_1(A_514))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.37/5.45  tff(c_40, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.37/5.45  tff(c_14346, plain, (![A_525]: (r1_tarski(A_525, k2_zfmisc_1(k1_relat_1(A_525), k2_relat_1(A_525))) | ~v1_funct_1(A_525) | ~v1_relat_1(A_525))), inference(resolution, [status(thm)], [c_14235, c_40])).
% 13.37/5.45  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.37/5.45  tff(c_14369, plain, (![A_525]: (k2_zfmisc_1(k1_relat_1(A_525), k2_relat_1(A_525))=A_525 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_525), k2_relat_1(A_525)), A_525) | ~v1_funct_1(A_525) | ~v1_relat_1(A_525))), inference(resolution, [status(thm)], [c_14346, c_2])).
% 13.37/5.45  tff(c_26074, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')), '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25988, c_14369])).
% 13.37/5.45  tff(c_26224, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_228, c_76, c_8, c_20, c_20, c_25988, c_26074])).
% 13.37/5.45  tff(c_26377, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_26224, c_8])).
% 13.37/5.45  tff(c_50, plain, (![A_22]: (k9_relat_1(k1_xboole_0, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.37/5.45  tff(c_26376, plain, (![A_22]: (k9_relat_1('#skF_4', A_22)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26224, c_26224, c_50])).
% 13.37/5.45  tff(c_14405, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14404, c_68])).
% 13.37/5.45  tff(c_26931, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26376, c_14405])).
% 13.37/5.45  tff(c_26935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26377, c_26931])).
% 13.37/5.45  tff(c_26937, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_14421])).
% 13.37/5.45  tff(c_52, plain, (![B_24, A_23]: (k1_tarski(k1_funct_1(B_24, A_23))=k2_relat_1(B_24) | k1_tarski(A_23)!=k1_relat_1(B_24) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.37/5.45  tff(c_14417, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_52, c_14405])).
% 13.37/5.45  tff(c_14419, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_76, c_14417])).
% 13.37/5.45  tff(c_14420, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_14419])).
% 13.37/5.45  tff(c_26972, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26937, c_14420])).
% 13.37/5.45  tff(c_26973, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_14419])).
% 13.37/5.45  tff(c_27103, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_26973])).
% 13.37/5.45  tff(c_27107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_27103])).
% 13.37/5.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.37/5.45  
% 13.37/5.45  Inference rules
% 13.37/5.45  ----------------------
% 13.37/5.45  #Ref     : 0
% 13.37/5.45  #Sup     : 5991
% 13.37/5.45  #Fact    : 0
% 13.37/5.45  #Define  : 0
% 13.37/5.45  #Split   : 8
% 13.37/5.45  #Chain   : 0
% 13.37/5.45  #Close   : 0
% 13.37/5.45  
% 13.37/5.45  Ordering : KBO
% 13.37/5.45  
% 13.37/5.45  Simplification rules
% 13.37/5.45  ----------------------
% 13.37/5.45  #Subsume      : 1087
% 13.37/5.45  #Demod        : 9286
% 13.37/5.45  #Tautology    : 2503
% 13.37/5.45  #SimpNegUnit  : 2
% 13.37/5.45  #BackRed      : 212
% 13.37/5.45  
% 13.37/5.45  #Partial instantiations: 0
% 13.37/5.45  #Strategies tried      : 1
% 13.37/5.45  
% 13.37/5.45  Timing (in seconds)
% 13.37/5.45  ----------------------
% 13.37/5.46  Preprocessing        : 0.35
% 13.37/5.46  Parsing              : 0.19
% 13.37/5.46  CNF conversion       : 0.02
% 13.37/5.46  Main loop            : 4.29
% 13.37/5.46  Inferencing          : 0.95
% 13.37/5.46  Reduction            : 1.79
% 13.37/5.46  Demodulation         : 1.46
% 13.37/5.46  BG Simplification    : 0.12
% 13.37/5.46  Subsumption          : 1.23
% 13.37/5.46  Abstraction          : 0.21
% 13.37/5.46  MUC search           : 0.00
% 13.37/5.46  Cooper               : 0.00
% 13.37/5.46  Total                : 4.68
% 13.37/5.46  Index Insertion      : 0.00
% 13.37/5.46  Index Deletion       : 0.00
% 13.37/5.46  Index Matching       : 0.00
% 13.37/5.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
