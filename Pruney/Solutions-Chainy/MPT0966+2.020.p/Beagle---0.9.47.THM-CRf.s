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
% DateTime   : Thu Dec  3 10:11:10 EST 2020

% Result     : Theorem 19.28s
% Output     : CNFRefutation 19.54s
% Verified   : 
% Statistics : Number of formulae       :  322 (2818 expanded)
%              Number of leaves         :   42 ( 917 expanded)
%              Depth                    :   17
%              Number of atoms          :  602 (8083 expanded)
%              Number of equality atoms :  181 (2276 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_127,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_32,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_38447,plain,(
    ! [B_30909,A_30910] :
      ( v1_relat_1(B_30909)
      | ~ m1_subset_1(B_30909,k1_zfmisc_1(A_30910))
      | ~ v1_relat_1(A_30910) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38462,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_38447])).

tff(c_38475,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38462])).

tff(c_38790,plain,(
    ! [C_30946,A_30947,B_30948] :
      ( v4_relat_1(C_30946,A_30947)
      | ~ m1_subset_1(C_30946,k1_zfmisc_1(k2_zfmisc_1(A_30947,B_30948))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38810,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_38790])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38986,plain,(
    ! [A_30970,B_30971,C_30972] :
      ( k2_relset_1(A_30970,B_30971,C_30972) = k2_relat_1(C_30972)
      | ~ m1_subset_1(C_30972,k1_zfmisc_1(k2_zfmisc_1(A_30970,B_30971))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_39005,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_38986])).

tff(c_72,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_39007,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39005,c_72])).

tff(c_39098,plain,(
    ! [C_30983,A_30984,B_30985] :
      ( m1_subset_1(C_30983,k1_zfmisc_1(k2_zfmisc_1(A_30984,B_30985)))
      | ~ r1_tarski(k2_relat_1(C_30983),B_30985)
      | ~ r1_tarski(k1_relat_1(C_30983),A_30984)
      | ~ v1_relat_1(C_30983) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_214,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_229,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_214])).

tff(c_242,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_229])).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13001,plain,(
    ! [C_10152,A_10153,B_10154] :
      ( v4_relat_1(C_10152,A_10153)
      | ~ m1_subset_1(C_10152,k1_zfmisc_1(k2_zfmisc_1(A_10153,B_10154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_13021,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_13001])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12904,plain,(
    ! [C_10137,B_10138,A_10139] :
      ( ~ v1_xboole_0(C_10137)
      | ~ m1_subset_1(B_10138,k1_zfmisc_1(C_10137))
      | ~ r2_hidden(A_10139,B_10138) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12937,plain,(
    ! [B_10141,A_10142,A_10143] :
      ( ~ v1_xboole_0(B_10141)
      | ~ r2_hidden(A_10142,A_10143)
      | ~ r1_tarski(A_10143,B_10141) ) ),
    inference(resolution,[status(thm)],[c_22,c_12904])).

tff(c_12941,plain,(
    ! [B_10144,A_10145] :
      ( ~ v1_xboole_0(B_10144)
      | ~ r1_tarski(A_10145,B_10144)
      | k1_xboole_0 = A_10145 ) ),
    inference(resolution,[status(thm)],[c_4,c_12937])).

tff(c_19863,plain,(
    ! [A_15842,B_15843] :
      ( ~ v1_xboole_0(A_15842)
      | k1_relat_1(B_15843) = k1_xboole_0
      | ~ v4_relat_1(B_15843,A_15842)
      | ~ v1_relat_1(B_15843) ) ),
    inference(resolution,[status(thm)],[c_30,c_12941])).

tff(c_19872,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_13021,c_19863])).

tff(c_19888,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_19872])).

tff(c_19896,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_19888])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_76,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_13202,plain,(
    ! [A_10181,B_10182,C_10183] :
      ( k1_relset_1(A_10181,B_10182,C_10183) = k1_relat_1(C_10183)
      | ~ m1_subset_1(C_10183,k1_zfmisc_1(k2_zfmisc_1(A_10181,B_10182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_13221,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_13202])).

tff(c_20053,plain,(
    ! [B_15855,A_15856,C_15857] :
      ( k1_xboole_0 = B_15855
      | k1_relset_1(A_15856,B_15855,C_15857) = A_15856
      | ~ v1_funct_2(C_15857,A_15856,B_15855)
      | ~ m1_subset_1(C_15857,k1_zfmisc_1(k2_zfmisc_1(A_15856,B_15855))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_20069,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_20053])).

tff(c_20080,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13221,c_20069])).

tff(c_20081,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_20080])).

tff(c_7246,plain,(
    ! [A_5835,B_5836,C_5837] :
      ( k1_relset_1(A_5835,B_5836,C_5837) = k1_relat_1(C_5837)
      | ~ m1_subset_1(C_5837,k1_zfmisc_1(k2_zfmisc_1(A_5835,B_5836))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7265,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_7246])).

tff(c_7437,plain,(
    ! [B_5853,A_5854,C_5855] :
      ( k1_xboole_0 = B_5853
      | k1_relset_1(A_5854,B_5853,C_5855) = A_5854
      | ~ v1_funct_2(C_5855,A_5854,B_5853)
      | ~ m1_subset_1(C_5855,k1_zfmisc_1(k2_zfmisc_1(A_5854,B_5853))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_7453,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_7437])).

tff(c_7464,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7265,c_7453])).

tff(c_7465,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_7464])).

tff(c_7197,plain,(
    ! [A_5830,B_5831,C_5832] :
      ( k2_relset_1(A_5830,B_5831,C_5832) = k2_relat_1(C_5832)
      | ~ m1_subset_1(C_5832,k1_zfmisc_1(k2_zfmisc_1(A_5830,B_5831))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7216,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_7197])).

tff(c_7228,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7216,c_72])).

tff(c_7297,plain,(
    ! [C_5839,A_5840,B_5841] :
      ( m1_subset_1(C_5839,k1_zfmisc_1(k2_zfmisc_1(A_5840,B_5841)))
      | ~ r1_tarski(k2_relat_1(C_5839),B_5841)
      | ~ r1_tarski(k1_relat_1(C_5839),A_5840)
      | ~ v1_relat_1(C_5839) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9090,plain,(
    ! [C_6006,A_6007,B_6008] :
      ( r1_tarski(C_6006,k2_zfmisc_1(A_6007,B_6008))
      | ~ r1_tarski(k2_relat_1(C_6006),B_6008)
      | ~ r1_tarski(k1_relat_1(C_6006),A_6007)
      | ~ v1_relat_1(C_6006) ) ),
    inference(resolution,[status(thm)],[c_7297,c_20])).

tff(c_9098,plain,(
    ! [A_6007] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_6007,'#skF_5'))
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_6007)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7228,c_9090])).

tff(c_9108,plain,(
    ! [A_6009] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_6009,'#skF_5'))
      | ~ r1_tarski('#skF_3',A_6009) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_7465,c_9098])).

tff(c_7264,plain,(
    ! [A_5835,B_5836,A_8] :
      ( k1_relset_1(A_5835,B_5836,A_8) = k1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_5835,B_5836)) ) ),
    inference(resolution,[status(thm)],[c_22,c_7246])).

tff(c_9114,plain,(
    ! [A_6009] :
      ( k1_relset_1(A_6009,'#skF_5','#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_3',A_6009) ) ),
    inference(resolution,[status(thm)],[c_9108,c_7264])).

tff(c_9149,plain,(
    ! [A_6010] :
      ( k1_relset_1(A_6010,'#skF_5','#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_6010) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7465,c_9114])).

tff(c_9164,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_9149])).

tff(c_7060,plain,(
    ! [C_5812,B_5813,A_5814] :
      ( ~ v1_xboole_0(C_5812)
      | ~ m1_subset_1(B_5813,k1_zfmisc_1(C_5812))
      | ~ r2_hidden(A_5814,B_5813) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7125,plain,(
    ! [B_5821,A_5822,A_5823] :
      ( ~ v1_xboole_0(B_5821)
      | ~ r2_hidden(A_5822,A_5823)
      | ~ r1_tarski(A_5823,B_5821) ) ),
    inference(resolution,[status(thm)],[c_22,c_7060])).

tff(c_7129,plain,(
    ! [B_5824,A_5825] :
      ( ~ v1_xboole_0(B_5824)
      | ~ r1_tarski(A_5825,B_5824)
      | k1_xboole_0 = A_5825 ) ),
    inference(resolution,[status(thm)],[c_4,c_7125])).

tff(c_7151,plain,
    ( ~ v1_xboole_0('#skF_5')
    | k2_relset_1('#skF_3','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_7129])).

tff(c_7163,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7151])).

tff(c_9106,plain,(
    ! [A_6007] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_6007,'#skF_5'))
      | ~ r1_tarski('#skF_3',A_6007) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_7465,c_9098])).

tff(c_7566,plain,(
    ! [B_5864,C_5865,A_5866] :
      ( k1_xboole_0 = B_5864
      | v1_funct_2(C_5865,A_5866,B_5864)
      | k1_relset_1(A_5866,B_5864,C_5865) != A_5866
      | ~ m1_subset_1(C_5865,k1_zfmisc_1(k2_zfmisc_1(A_5866,B_5864))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10692,plain,(
    ! [B_8029,A_8030,A_8031] :
      ( k1_xboole_0 = B_8029
      | v1_funct_2(A_8030,A_8031,B_8029)
      | k1_relset_1(A_8031,B_8029,A_8030) != A_8031
      | ~ r1_tarski(A_8030,k2_zfmisc_1(A_8031,B_8029)) ) ),
    inference(resolution,[status(thm)],[c_22,c_7566])).

tff(c_10724,plain,(
    ! [A_6007] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6',A_6007,'#skF_5')
      | k1_relset_1(A_6007,'#skF_5','#skF_6') != A_6007
      | ~ r1_tarski('#skF_3',A_6007) ) ),
    inference(resolution,[status(thm)],[c_9106,c_10692])).

tff(c_10805,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_10724])).

tff(c_10893,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10805,c_2])).

tff(c_10896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7163,c_10893])).

tff(c_10898,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10724])).

tff(c_42,plain,(
    ! [C_31,A_29,B_30] :
      ( m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ r1_tarski(k2_relat_1(C_31),B_30)
      | ~ r1_tarski(k1_relat_1(C_31),A_29)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12210,plain,(
    ! [B_10104,C_10105,A_10106] :
      ( k1_xboole_0 = B_10104
      | v1_funct_2(C_10105,A_10106,B_10104)
      | k1_relset_1(A_10106,B_10104,C_10105) != A_10106
      | ~ r1_tarski(k2_relat_1(C_10105),B_10104)
      | ~ r1_tarski(k1_relat_1(C_10105),A_10106)
      | ~ v1_relat_1(C_10105) ) ),
    inference(resolution,[status(thm)],[c_42,c_7566])).

tff(c_12218,plain,(
    ! [A_10106] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6',A_10106,'#skF_5')
      | k1_relset_1(A_10106,'#skF_5','#skF_6') != A_10106
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_10106)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7228,c_12210])).

tff(c_12226,plain,(
    ! [A_10106] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6',A_10106,'#skF_5')
      | k1_relset_1(A_10106,'#skF_5','#skF_6') != A_10106
      | ~ r1_tarski('#skF_3',A_10106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_7465,c_12218])).

tff(c_12670,plain,(
    ! [A_10116] :
      ( v1_funct_2('#skF_6',A_10116,'#skF_5')
      | k1_relset_1(A_10116,'#skF_5','#skF_6') != A_10116
      | ~ r1_tarski('#skF_3',A_10116) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10898,c_12226])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_68])).

tff(c_122,plain,(
    ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_12679,plain,
    ( k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_12670,c_122])).

tff(c_12685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9164,c_12679])).

tff(c_12687,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_7151])).

tff(c_7152,plain,(
    ! [B_4] :
      ( ~ v1_xboole_0(B_4)
      | k1_xboole_0 = B_4 ) ),
    inference(resolution,[status(thm)],[c_10,c_7129])).

tff(c_12691,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12687,c_7152])).

tff(c_12,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12714,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12691,c_12])).

tff(c_156,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_171,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_72,c_156])).

tff(c_245,plain,(
    ~ r1_tarski('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_12741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12714,c_245])).

tff(c_12742,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_13086,plain,(
    ! [A_10168,B_10169,C_10170] :
      ( k2_relset_1(A_10168,B_10169,C_10170) = k2_relat_1(C_10170)
      | ~ m1_subset_1(C_10170,k1_zfmisc_1(k2_zfmisc_1(A_10168,B_10169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13099,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_13086])).

tff(c_13106,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12742,c_13099])).

tff(c_13246,plain,(
    ! [C_10185,A_10186,B_10187] :
      ( m1_subset_1(C_10185,k1_zfmisc_1(k2_zfmisc_1(A_10186,B_10187)))
      | ~ r1_tarski(k2_relat_1(C_10185),B_10187)
      | ~ r1_tarski(k1_relat_1(C_10185),A_10186)
      | ~ v1_relat_1(C_10185) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [A_23,B_24,C_25] :
      ( k1_relset_1(A_23,B_24,C_25) = k1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22159,plain,(
    ! [A_17204,B_17205,C_17206] :
      ( k1_relset_1(A_17204,B_17205,C_17206) = k1_relat_1(C_17206)
      | ~ r1_tarski(k2_relat_1(C_17206),B_17205)
      | ~ r1_tarski(k1_relat_1(C_17206),A_17204)
      | ~ v1_relat_1(C_17206) ) ),
    inference(resolution,[status(thm)],[c_13246,c_38])).

tff(c_22167,plain,(
    ! [A_17204,B_17205] :
      ( k1_relset_1(A_17204,B_17205,'#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_5',B_17205)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_17204)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13106,c_22159])).

tff(c_22227,plain,(
    ! [A_17208,B_17209] :
      ( k1_relset_1(A_17208,B_17209,'#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_5',B_17209)
      | ~ r1_tarski('#skF_3',A_17208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_20081,c_20081,c_22167])).

tff(c_22240,plain,(
    ! [A_17210] :
      ( k1_relset_1(A_17210,'#skF_5','#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_17210) ) ),
    inference(resolution,[status(thm)],[c_10,c_22227])).

tff(c_22255,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_22240])).

tff(c_13405,plain,(
    ! [B_10205,C_10206,A_10207] :
      ( k1_xboole_0 = B_10205
      | v1_funct_2(C_10206,A_10207,B_10205)
      | k1_relset_1(A_10207,B_10205,C_10206) != A_10207
      | ~ m1_subset_1(C_10206,k1_zfmisc_1(k2_zfmisc_1(A_10207,B_10205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_24473,plain,(
    ! [B_21200,C_21201,A_21202] :
      ( k1_xboole_0 = B_21200
      | v1_funct_2(C_21201,A_21202,B_21200)
      | k1_relset_1(A_21202,B_21200,C_21201) != A_21202
      | ~ r1_tarski(k2_relat_1(C_21201),B_21200)
      | ~ r1_tarski(k1_relat_1(C_21201),A_21202)
      | ~ v1_relat_1(C_21201) ) ),
    inference(resolution,[status(thm)],[c_42,c_13405])).

tff(c_24481,plain,(
    ! [B_21200,A_21202] :
      ( k1_xboole_0 = B_21200
      | v1_funct_2('#skF_6',A_21202,B_21200)
      | k1_relset_1(A_21202,B_21200,'#skF_6') != A_21202
      | ~ r1_tarski('#skF_5',B_21200)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_21202)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13106,c_24473])).

tff(c_24564,plain,(
    ! [B_21205,A_21206] :
      ( k1_xboole_0 = B_21205
      | v1_funct_2('#skF_6',A_21206,B_21205)
      | k1_relset_1(A_21206,B_21205,'#skF_6') != A_21206
      | ~ r1_tarski('#skF_5',B_21205)
      | ~ r1_tarski('#skF_3',A_21206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_20081,c_24481])).

tff(c_24573,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_24564,c_122])).

tff(c_24578,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_22255,c_24573])).

tff(c_16,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21446,plain,(
    ! [C_17148,A_17149] :
      ( m1_subset_1(C_17148,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_17148),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_17148),A_17149)
      | ~ v1_relat_1(C_17148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_13246])).

tff(c_21451,plain,(
    ! [A_17149] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_5',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_17149)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13106,c_21446])).

tff(c_21454,plain,(
    ! [A_17149] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_5',k1_xboole_0)
      | ~ r1_tarski('#skF_3',A_17149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_20081,c_21451])).

tff(c_21525,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_21454])).

tff(c_24614,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24578,c_21525])).

tff(c_24679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24614])).

tff(c_24681,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_21454])).

tff(c_12940,plain,(
    ! [B_10141,A_1] :
      ( ~ v1_xboole_0(B_10141)
      | ~ r1_tarski(A_1,B_10141)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_12937])).

tff(c_24698,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_24681,c_12940])).

tff(c_24717,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24698])).

tff(c_13071,plain,(
    ! [C_10164,A_10165] :
      ( v4_relat_1(C_10164,A_10165)
      | ~ m1_subset_1(C_10164,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_13001])).

tff(c_13079,plain,(
    ! [A_8,A_10165] :
      ( v4_relat_1(A_8,A_10165)
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_13071])).

tff(c_20095,plain,(
    ! [A_16] :
      ( r1_tarski('#skF_3',A_16)
      | ~ v4_relat_1('#skF_6',A_16)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20081,c_30])).

tff(c_20128,plain,(
    ! [A_15859] :
      ( r1_tarski('#skF_3',A_15859)
      | ~ v4_relat_1('#skF_6',A_15859) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_20095])).

tff(c_20144,plain,(
    ! [A_10165] :
      ( r1_tarski('#skF_3',A_10165)
      | ~ r1_tarski('#skF_6',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_13079,c_20128])).

tff(c_20150,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_20144])).

tff(c_24744,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24717,c_20150])).

tff(c_24680,plain,(
    ! [A_17149] :
      ( ~ r1_tarski('#skF_3',A_17149)
      | m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_21454])).

tff(c_24950,plain,(
    ! [A_17149] :
      ( ~ r1_tarski('#skF_3',A_17149)
      | m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24717,c_24680])).

tff(c_24953,plain,(
    ! [A_21216] : ~ r1_tarski('#skF_3',A_21216) ),
    inference(splitLeft,[status(thm)],[c_24950])).

tff(c_24963,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_24953])).

tff(c_24964,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_24950])).

tff(c_25064,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_24964,c_20])).

tff(c_25075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24744,c_25064])).

tff(c_25081,plain,(
    ! [A_21225] : r1_tarski('#skF_3',A_21225) ),
    inference(splitRight,[status(thm)],[c_20144])).

tff(c_176,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_156])).

tff(c_25130,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_25081,c_176])).

tff(c_25180,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25130,c_2])).

tff(c_25184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19896,c_25180])).

tff(c_25186,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_19888])).

tff(c_12960,plain,(
    ! [B_4] :
      ( ~ v1_xboole_0(B_4)
      | k1_xboole_0 = B_4 ) ),
    inference(resolution,[status(thm)],[c_10,c_12941])).

tff(c_25190,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_25186,c_12960])).

tff(c_18,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_25231,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_3',B_7) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25190,c_25190,c_18])).

tff(c_12918,plain,(
    ! [A_10139] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_10139,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_12904])).

tff(c_12936,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_12918])).

tff(c_25427,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25231,c_12936])).

tff(c_25433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25186,c_25427])).

tff(c_25435,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_12918])).

tff(c_25436,plain,(
    ! [A_21237] : ~ r2_hidden(A_21237,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_12918])).

tff(c_25441,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4,c_25436])).

tff(c_25455,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25441,c_4])).

tff(c_25929,plain,(
    ! [B_21289,A_21290,A_21291] :
      ( ~ v1_xboole_0(B_21289)
      | ~ r2_hidden(A_21290,A_21291)
      | ~ r1_tarski(A_21291,B_21289) ) ),
    inference(resolution,[status(thm)],[c_22,c_12904])).

tff(c_25933,plain,(
    ! [B_21292,A_21293] :
      ( ~ v1_xboole_0(B_21292)
      | ~ r1_tarski(A_21293,B_21292)
      | A_21293 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_25455,c_25929])).

tff(c_25951,plain,(
    ! [B_21294] :
      ( ~ v1_xboole_0(B_21294)
      | B_21294 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_10,c_25933])).

tff(c_25958,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_25435,c_25951])).

tff(c_125,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_133,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_125])).

tff(c_170,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_133,c_156])).

tff(c_12833,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_25962,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25958,c_12833])).

tff(c_25967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_25962])).

tff(c_25968,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_25980,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25968,c_74])).

tff(c_26177,plain,(
    ! [C_21316,A_21317,B_21318] :
      ( v4_relat_1(C_21316,A_21317)
      | ~ m1_subset_1(C_21316,k1_zfmisc_1(k2_zfmisc_1(A_21317,B_21318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26218,plain,(
    ! [C_21320] :
      ( v4_relat_1(C_21320,'#skF_3')
      | ~ m1_subset_1(C_21320,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25968,c_26177])).

tff(c_26231,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_25980,c_26218])).

tff(c_26254,plain,(
    ! [C_21327,B_21328,A_21329] :
      ( ~ v1_xboole_0(C_21327)
      | ~ m1_subset_1(B_21328,k1_zfmisc_1(C_21327))
      | ~ r2_hidden(A_21329,B_21328) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26280,plain,(
    ! [B_21331,A_21332,A_21333] :
      ( ~ v1_xboole_0(B_21331)
      | ~ r2_hidden(A_21332,A_21333)
      | ~ r1_tarski(A_21333,B_21331) ) ),
    inference(resolution,[status(thm)],[c_22,c_26254])).

tff(c_26284,plain,(
    ! [B_21334,A_21335] :
      ( ~ v1_xboole_0(B_21334)
      | ~ r1_tarski(A_21335,B_21334)
      | k1_xboole_0 = A_21335 ) ),
    inference(resolution,[status(thm)],[c_4,c_26280])).

tff(c_33610,plain,(
    ! [A_27570,B_27571] :
      ( ~ v1_xboole_0(A_27570)
      | k1_relat_1(B_27571) = k1_xboole_0
      | ~ v4_relat_1(B_27571,A_27570)
      | ~ v1_relat_1(B_27571) ) ),
    inference(resolution,[status(thm)],[c_30,c_26284])).

tff(c_33625,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26231,c_33610])).

tff(c_33640,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_33625])).

tff(c_33665,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_33640])).

tff(c_33277,plain,(
    ! [A_27534,B_27535,C_27536] :
      ( k1_relset_1(A_27534,B_27535,C_27536) = k1_relat_1(C_27536)
      | ~ m1_subset_1(C_27536,k1_zfmisc_1(k2_zfmisc_1(A_27534,B_27535))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_33326,plain,(
    ! [C_27542] :
      ( k1_relset_1('#skF_3','#skF_4',C_27542) = k1_relat_1(C_27542)
      | ~ m1_subset_1(C_27542,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25968,c_33277])).

tff(c_33338,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_25980,c_33326])).

tff(c_34188,plain,(
    ! [B_27620,A_27621,C_27622] :
      ( k1_xboole_0 = B_27620
      | k1_relset_1(A_27621,B_27620,C_27622) = A_27621
      | ~ v1_funct_2(C_27622,A_27621,B_27620)
      | ~ m1_subset_1(C_27622,k1_zfmisc_1(k2_zfmisc_1(A_27621,B_27620))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34194,plain,(
    ! [C_27622] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_27622) = '#skF_3'
      | ~ v1_funct_2(C_27622,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_27622,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25968,c_34188])).

tff(c_34700,plain,(
    ! [C_29054] :
      ( k1_relset_1('#skF_3','#skF_4',C_29054) = '#skF_3'
      | ~ v1_funct_2(C_29054,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_29054,k1_zfmisc_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_34194])).

tff(c_34706,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_25980,c_34700])).

tff(c_34716,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_33338,c_34706])).

tff(c_26467,plain,(
    ! [A_21353,B_21354,C_21355] :
      ( k2_relset_1(A_21353,B_21354,C_21355) = k2_relat_1(C_21355)
      | ~ m1_subset_1(C_21355,k1_zfmisc_1(k2_zfmisc_1(A_21353,B_21354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_33461,plain,(
    ! [C_27553] :
      ( k2_relset_1('#skF_3','#skF_4',C_27553) = k2_relat_1(C_27553)
      | ~ m1_subset_1(C_27553,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25968,c_26467])).

tff(c_33467,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_25980,c_33461])).

tff(c_33475,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12742,c_33467])).

tff(c_33981,plain,(
    ! [B_27598,C_27599,A_27600] :
      ( k1_xboole_0 = B_27598
      | v1_funct_2(C_27599,A_27600,B_27598)
      | k1_relset_1(A_27600,B_27598,C_27599) != A_27600
      | ~ m1_subset_1(C_27599,k1_zfmisc_1(k2_zfmisc_1(A_27600,B_27598))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_37064,plain,(
    ! [B_30832,C_30833,A_30834] :
      ( k1_xboole_0 = B_30832
      | v1_funct_2(C_30833,A_30834,B_30832)
      | k1_relset_1(A_30834,B_30832,C_30833) != A_30834
      | ~ r1_tarski(k2_relat_1(C_30833),B_30832)
      | ~ r1_tarski(k1_relat_1(C_30833),A_30834)
      | ~ v1_relat_1(C_30833) ) ),
    inference(resolution,[status(thm)],[c_42,c_33981])).

tff(c_37072,plain,(
    ! [B_30832,A_30834] :
      ( k1_xboole_0 = B_30832
      | v1_funct_2('#skF_6',A_30834,B_30832)
      | k1_relset_1(A_30834,B_30832,'#skF_6') != A_30834
      | ~ r1_tarski('#skF_5',B_30832)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_30834)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33475,c_37064])).

tff(c_37112,plain,(
    ! [B_30841,A_30842] :
      ( k1_xboole_0 = B_30841
      | v1_funct_2('#skF_6',A_30842,B_30841)
      | k1_relset_1(A_30842,B_30841,'#skF_6') != A_30842
      | ~ r1_tarski('#skF_5',B_30841)
      | ~ r1_tarski('#skF_3',A_30842) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_34716,c_37072])).

tff(c_37125,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_37112,c_122])).

tff(c_37135,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_37125])).

tff(c_37136,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_37135])).

tff(c_33840,plain,(
    ! [C_27586,A_27587,B_27588] :
      ( m1_subset_1(C_27586,k1_zfmisc_1(k2_zfmisc_1(A_27587,B_27588)))
      | ~ r1_tarski(k2_relat_1(C_27586),B_27588)
      | ~ r1_tarski(k1_relat_1(C_27586),A_27587)
      | ~ v1_relat_1(C_27586) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36141,plain,(
    ! [A_30756,B_30757,C_30758] :
      ( k1_relset_1(A_30756,B_30757,C_30758) = k1_relat_1(C_30758)
      | ~ r1_tarski(k2_relat_1(C_30758),B_30757)
      | ~ r1_tarski(k1_relat_1(C_30758),A_30756)
      | ~ v1_relat_1(C_30758) ) ),
    inference(resolution,[status(thm)],[c_33840,c_38])).

tff(c_36146,plain,(
    ! [A_30756,B_30757] :
      ( k1_relset_1(A_30756,B_30757,'#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_5',B_30757)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_30756)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33475,c_36141])).

tff(c_36795,plain,(
    ! [A_30809,B_30810] :
      ( k1_relset_1(A_30809,B_30810,'#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_5',B_30810)
      | ~ r1_tarski('#skF_3',A_30809) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_34716,c_34716,c_36146])).

tff(c_37137,plain,(
    ! [A_30843] :
      ( k1_relset_1(A_30843,'#skF_5','#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_30843) ) ),
    inference(resolution,[status(thm)],[c_10,c_36795])).

tff(c_37149,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_37137])).

tff(c_37155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37136,c_37149])).

tff(c_37156,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_37135])).

tff(c_35690,plain,(
    ! [C_30723,A_30724] :
      ( m1_subset_1(C_30723,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_30723),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_30723),A_30724)
      | ~ v1_relat_1(C_30723) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_33840])).

tff(c_35692,plain,(
    ! [A_30724] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_5',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_30724)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33475,c_35690])).

tff(c_35694,plain,(
    ! [A_30724] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_5',k1_xboole_0)
      | ~ r1_tarski('#skF_3',A_30724) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_34716,c_35692])).

tff(c_36125,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_35694])).

tff(c_37179,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37156,c_36125])).

tff(c_37243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_37179])).

tff(c_37245,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_35694])).

tff(c_26283,plain,(
    ! [B_21331,A_1] :
      ( ~ v1_xboole_0(B_21331)
      | ~ r1_tarski(A_1,B_21331)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_26280])).

tff(c_37275,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_37245,c_26283])).

tff(c_37294,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_37275])).

tff(c_26239,plain,(
    ! [C_21323,A_21324] :
      ( v4_relat_1(C_21323,A_21324)
      | ~ m1_subset_1(C_21323,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_26177])).

tff(c_26247,plain,(
    ! [A_8,A_21324] :
      ( v4_relat_1(A_8,A_21324)
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_26239])).

tff(c_34736,plain,(
    ! [A_16] :
      ( r1_tarski('#skF_3',A_16)
      | ~ v4_relat_1('#skF_6',A_16)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34716,c_30])).

tff(c_34886,plain,(
    ! [A_29059] :
      ( r1_tarski('#skF_3',A_29059)
      | ~ v4_relat_1('#skF_6',A_29059) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_34736])).

tff(c_34909,plain,(
    ! [A_21324] :
      ( r1_tarski('#skF_3',A_21324)
      | ~ r1_tarski('#skF_6',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26247,c_34886])).

tff(c_34915,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_34909])).

tff(c_37315,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37294,c_34915])).

tff(c_37626,plain,(
    ! [A_30862] : k2_zfmisc_1(A_30862,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37294,c_37294,c_16])).

tff(c_37363,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37294,c_12])).

tff(c_36033,plain,(
    ! [C_30746,A_30747,B_30748] :
      ( r1_tarski(C_30746,k2_zfmisc_1(A_30747,B_30748))
      | ~ r1_tarski(k2_relat_1(C_30746),B_30748)
      | ~ r1_tarski(k1_relat_1(C_30746),A_30747)
      | ~ v1_relat_1(C_30746) ) ),
    inference(resolution,[status(thm)],[c_33840,c_20])).

tff(c_36038,plain,(
    ! [A_30747,B_30748] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_30747,B_30748))
      | ~ r1_tarski('#skF_5',B_30748)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_30747)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33475,c_36033])).

tff(c_36044,plain,(
    ! [A_30747,B_30748] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_30747,B_30748))
      | ~ r1_tarski('#skF_5',B_30748)
      | ~ r1_tarski('#skF_3',A_30747) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_34716,c_36038])).

tff(c_37576,plain,(
    ! [A_30747,B_30748] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_30747,B_30748))
      | ~ r1_tarski('#skF_3',A_30747) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37363,c_36044])).

tff(c_37631,plain,(
    ! [A_30862] :
      ( r1_tarski('#skF_6','#skF_5')
      | ~ r1_tarski('#skF_3',A_30862) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37626,c_37576])).

tff(c_37731,plain,(
    ! [A_30863] : ~ r1_tarski('#skF_3',A_30863) ),
    inference(negUnitSimplification,[status(thm)],[c_37315,c_37631])).

tff(c_37741,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_37731])).

tff(c_37755,plain,(
    ! [A_30866] : r1_tarski('#skF_3',A_30866) ),
    inference(splitRight,[status(thm)],[c_34909])).

tff(c_37829,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_37755,c_176])).

tff(c_37880,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37829,c_2])).

tff(c_37884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33665,c_37880])).

tff(c_37886,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_33640])).

tff(c_26303,plain,(
    ! [B_4] :
      ( ~ v1_xboole_0(B_4)
      | k1_xboole_0 = B_4 ) ),
    inference(resolution,[status(thm)],[c_10,c_26284])).

tff(c_37890,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_37886,c_26303])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_25985,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_25968,c_14])).

tff(c_25993,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_25985])).

tff(c_26007,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_25993])).

tff(c_37949,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37890,c_26007])).

tff(c_37962,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_3',B_7) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37890,c_37890,c_18])).

tff(c_38191,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37962,c_25968])).

tff(c_38193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37949,c_38191])).

tff(c_38194,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_25993])).

tff(c_134,plain,(
    ! [A_59,B_60] : m1_subset_1('#skF_2'(A_59,B_60),k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_145,plain,(
    ! [B_61] : m1_subset_1('#skF_2'(k1_xboole_0,B_61),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_134])).

tff(c_149,plain,(
    ! [B_61] : r1_tarski('#skF_2'(k1_xboole_0,B_61),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_145,c_20])).

tff(c_158,plain,(
    ! [B_61] :
      ( '#skF_2'(k1_xboole_0,B_61) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,'#skF_2'(k1_xboole_0,B_61)) ) ),
    inference(resolution,[status(thm)],[c_149,c_156])).

tff(c_180,plain,(
    ! [B_66] : '#skF_2'(k1_xboole_0,B_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_158])).

tff(c_56,plain,(
    ! [A_35,B_36] : v1_funct_2('#skF_2'(A_35,B_36),A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_191,plain,(
    ! [B_66] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_56])).

tff(c_38201,plain,(
    ! [B_66] : v1_funct_2('#skF_3','#skF_3',B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38194,c_38194,c_191])).

tff(c_38195,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_25993])).

tff(c_38217,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38194,c_38195])).

tff(c_38222,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38217,c_122])).

tff(c_38396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38201,c_38222])).

tff(c_38397,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_39121,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_39098,c_38397])).

tff(c_39139,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38475,c_39007,c_39121])).

tff(c_39142,plain,
    ( ~ v4_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_39139])).

tff(c_39146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38475,c_38810,c_39142])).

tff(c_39148,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_39182,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_4',B_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39148,c_39148,c_18])).

tff(c_39219,plain,(
    ! [A_31004,B_31005] : m1_subset_1('#skF_2'(A_31004,B_31005),k1_zfmisc_1(k2_zfmisc_1(A_31004,B_31005))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_39230,plain,(
    ! [B_31006] : m1_subset_1('#skF_2'('#skF_4',B_31006),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_39182,c_39219])).

tff(c_39282,plain,(
    ! [B_31010] : r1_tarski('#skF_2'('#skF_4',B_31010),'#skF_4') ),
    inference(resolution,[status(thm)],[c_39230,c_20])).

tff(c_39147,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_39156,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39148,c_39147])).

tff(c_39150,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39147,c_12])).

tff(c_39167,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39156,c_39150])).

tff(c_39235,plain,(
    ! [B_31007,A_31008] :
      ( B_31007 = A_31008
      | ~ r1_tarski(B_31007,A_31008)
      | ~ r1_tarski(A_31008,B_31007) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_39248,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ r1_tarski(A_5,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_39167,c_39235])).

tff(c_39296,plain,(
    ! [B_31011] : '#skF_2'('#skF_4',B_31011) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_39282,c_39248])).

tff(c_39304,plain,(
    ! [B_31011] : v1_funct_2('#skF_4','#skF_4',B_31011) ),
    inference(superposition,[status(thm),theory(equality)],[c_39296,c_56])).

tff(c_39149,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39147,c_39147,c_16])).

tff(c_39170,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39156,c_39156,c_39149])).

tff(c_39178,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39170,c_39156,c_74])).

tff(c_39210,plain,(
    ! [A_31002,B_31003] :
      ( r1_tarski(A_31002,B_31003)
      | ~ m1_subset_1(A_31002,k1_zfmisc_1(B_31003)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_39218,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_39178,c_39210])).

tff(c_39237,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_39218,c_39235])).

tff(c_39246,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39167,c_39237])).

tff(c_39208,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39156,c_39178,c_39182,c_39156,c_80])).

tff(c_39254,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39246,c_39208])).

tff(c_39339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39304,c_39254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:58:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.28/8.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.28/8.49  
% 19.28/8.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.28/8.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 19.28/8.49  
% 19.28/8.49  %Foreground sorts:
% 19.28/8.49  
% 19.28/8.49  
% 19.28/8.49  %Background operators:
% 19.28/8.49  
% 19.28/8.49  
% 19.28/8.49  %Foreground operators:
% 19.28/8.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 19.28/8.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.28/8.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.28/8.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.28/8.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 19.28/8.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.28/8.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.28/8.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.28/8.49  tff('#skF_5', type, '#skF_5': $i).
% 19.28/8.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 19.28/8.49  tff('#skF_6', type, '#skF_6': $i).
% 19.28/8.49  tff('#skF_3', type, '#skF_3': $i).
% 19.28/8.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 19.28/8.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 19.28/8.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.28/8.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.28/8.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.28/8.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 19.28/8.49  tff('#skF_4', type, '#skF_4': $i).
% 19.28/8.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.28/8.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 19.28/8.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 19.28/8.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.28/8.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.28/8.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.28/8.49  
% 19.54/8.53  tff(f_74, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 19.54/8.53  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 19.54/8.53  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 19.54/8.53  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 19.54/8.53  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 19.54/8.53  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 19.54/8.53  tff(f_96, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 19.54/8.53  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 19.54/8.53  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 19.54/8.53  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 19.54/8.53  tff(f_59, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 19.54/8.53  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 19.54/8.53  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 19.54/8.53  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 19.54/8.53  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 19.54/8.53  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 19.54/8.53  tff(f_127, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 19.54/8.53  tff(c_32, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 19.54/8.53  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 19.54/8.53  tff(c_38447, plain, (![B_30909, A_30910]: (v1_relat_1(B_30909) | ~m1_subset_1(B_30909, k1_zfmisc_1(A_30910)) | ~v1_relat_1(A_30910))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.54/8.53  tff(c_38462, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_38447])).
% 19.54/8.53  tff(c_38475, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38462])).
% 19.54/8.53  tff(c_38790, plain, (![C_30946, A_30947, B_30948]: (v4_relat_1(C_30946, A_30947) | ~m1_subset_1(C_30946, k1_zfmisc_1(k2_zfmisc_1(A_30947, B_30948))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 19.54/8.53  tff(c_38810, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_38790])).
% 19.54/8.53  tff(c_30, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 19.54/8.53  tff(c_38986, plain, (![A_30970, B_30971, C_30972]: (k2_relset_1(A_30970, B_30971, C_30972)=k2_relat_1(C_30972) | ~m1_subset_1(C_30972, k1_zfmisc_1(k2_zfmisc_1(A_30970, B_30971))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 19.54/8.53  tff(c_39005, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_38986])).
% 19.54/8.53  tff(c_72, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 19.54/8.53  tff(c_39007, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_39005, c_72])).
% 19.54/8.53  tff(c_39098, plain, (![C_30983, A_30984, B_30985]: (m1_subset_1(C_30983, k1_zfmisc_1(k2_zfmisc_1(A_30984, B_30985))) | ~r1_tarski(k2_relat_1(C_30983), B_30985) | ~r1_tarski(k1_relat_1(C_30983), A_30984) | ~v1_relat_1(C_30983))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.54/8.53  tff(c_214, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.54/8.53  tff(c_229, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_214])).
% 19.54/8.53  tff(c_242, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_229])).
% 19.54/8.53  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 19.54/8.53  tff(c_13001, plain, (![C_10152, A_10153, B_10154]: (v4_relat_1(C_10152, A_10153) | ~m1_subset_1(C_10152, k1_zfmisc_1(k2_zfmisc_1(A_10153, B_10154))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 19.54/8.53  tff(c_13021, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_13001])).
% 19.54/8.53  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 19.54/8.53  tff(c_22, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.54/8.53  tff(c_12904, plain, (![C_10137, B_10138, A_10139]: (~v1_xboole_0(C_10137) | ~m1_subset_1(B_10138, k1_zfmisc_1(C_10137)) | ~r2_hidden(A_10139, B_10138))), inference(cnfTransformation, [status(thm)], [f_59])).
% 19.54/8.53  tff(c_12937, plain, (![B_10141, A_10142, A_10143]: (~v1_xboole_0(B_10141) | ~r2_hidden(A_10142, A_10143) | ~r1_tarski(A_10143, B_10141))), inference(resolution, [status(thm)], [c_22, c_12904])).
% 19.54/8.53  tff(c_12941, plain, (![B_10144, A_10145]: (~v1_xboole_0(B_10144) | ~r1_tarski(A_10145, B_10144) | k1_xboole_0=A_10145)), inference(resolution, [status(thm)], [c_4, c_12937])).
% 19.54/8.53  tff(c_19863, plain, (![A_15842, B_15843]: (~v1_xboole_0(A_15842) | k1_relat_1(B_15843)=k1_xboole_0 | ~v4_relat_1(B_15843, A_15842) | ~v1_relat_1(B_15843))), inference(resolution, [status(thm)], [c_30, c_12941])).
% 19.54/8.53  tff(c_19872, plain, (~v1_xboole_0('#skF_3') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_13021, c_19863])).
% 19.54/8.53  tff(c_19888, plain, (~v1_xboole_0('#skF_3') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_242, c_19872])).
% 19.54/8.53  tff(c_19896, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_19888])).
% 19.54/8.53  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 19.54/8.53  tff(c_70, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_147])).
% 19.54/8.53  tff(c_96, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_70])).
% 19.54/8.53  tff(c_76, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 19.54/8.53  tff(c_13202, plain, (![A_10181, B_10182, C_10183]: (k1_relset_1(A_10181, B_10182, C_10183)=k1_relat_1(C_10183) | ~m1_subset_1(C_10183, k1_zfmisc_1(k2_zfmisc_1(A_10181, B_10182))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.54/8.53  tff(c_13221, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_13202])).
% 19.54/8.53  tff(c_20053, plain, (![B_15855, A_15856, C_15857]: (k1_xboole_0=B_15855 | k1_relset_1(A_15856, B_15855, C_15857)=A_15856 | ~v1_funct_2(C_15857, A_15856, B_15855) | ~m1_subset_1(C_15857, k1_zfmisc_1(k2_zfmisc_1(A_15856, B_15855))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 19.54/8.53  tff(c_20069, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_20053])).
% 19.54/8.53  tff(c_20080, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_13221, c_20069])).
% 19.54/8.53  tff(c_20081, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_96, c_20080])).
% 19.54/8.53  tff(c_7246, plain, (![A_5835, B_5836, C_5837]: (k1_relset_1(A_5835, B_5836, C_5837)=k1_relat_1(C_5837) | ~m1_subset_1(C_5837, k1_zfmisc_1(k2_zfmisc_1(A_5835, B_5836))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.54/8.53  tff(c_7265, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_7246])).
% 19.54/8.53  tff(c_7437, plain, (![B_5853, A_5854, C_5855]: (k1_xboole_0=B_5853 | k1_relset_1(A_5854, B_5853, C_5855)=A_5854 | ~v1_funct_2(C_5855, A_5854, B_5853) | ~m1_subset_1(C_5855, k1_zfmisc_1(k2_zfmisc_1(A_5854, B_5853))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 19.54/8.53  tff(c_7453, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_7437])).
% 19.54/8.53  tff(c_7464, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7265, c_7453])).
% 19.54/8.53  tff(c_7465, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_96, c_7464])).
% 19.54/8.53  tff(c_7197, plain, (![A_5830, B_5831, C_5832]: (k2_relset_1(A_5830, B_5831, C_5832)=k2_relat_1(C_5832) | ~m1_subset_1(C_5832, k1_zfmisc_1(k2_zfmisc_1(A_5830, B_5831))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 19.54/8.53  tff(c_7216, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_7197])).
% 19.54/8.53  tff(c_7228, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7216, c_72])).
% 19.54/8.53  tff(c_7297, plain, (![C_5839, A_5840, B_5841]: (m1_subset_1(C_5839, k1_zfmisc_1(k2_zfmisc_1(A_5840, B_5841))) | ~r1_tarski(k2_relat_1(C_5839), B_5841) | ~r1_tarski(k1_relat_1(C_5839), A_5840) | ~v1_relat_1(C_5839))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.54/8.53  tff(c_20, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.54/8.53  tff(c_9090, plain, (![C_6006, A_6007, B_6008]: (r1_tarski(C_6006, k2_zfmisc_1(A_6007, B_6008)) | ~r1_tarski(k2_relat_1(C_6006), B_6008) | ~r1_tarski(k1_relat_1(C_6006), A_6007) | ~v1_relat_1(C_6006))), inference(resolution, [status(thm)], [c_7297, c_20])).
% 19.54/8.53  tff(c_9098, plain, (![A_6007]: (r1_tarski('#skF_6', k2_zfmisc_1(A_6007, '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_6'), A_6007) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7228, c_9090])).
% 19.54/8.53  tff(c_9108, plain, (![A_6009]: (r1_tarski('#skF_6', k2_zfmisc_1(A_6009, '#skF_5')) | ~r1_tarski('#skF_3', A_6009))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_7465, c_9098])).
% 19.54/8.53  tff(c_7264, plain, (![A_5835, B_5836, A_8]: (k1_relset_1(A_5835, B_5836, A_8)=k1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_5835, B_5836)))), inference(resolution, [status(thm)], [c_22, c_7246])).
% 19.54/8.53  tff(c_9114, plain, (![A_6009]: (k1_relset_1(A_6009, '#skF_5', '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski('#skF_3', A_6009))), inference(resolution, [status(thm)], [c_9108, c_7264])).
% 19.54/8.53  tff(c_9149, plain, (![A_6010]: (k1_relset_1(A_6010, '#skF_5', '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_6010))), inference(demodulation, [status(thm), theory('equality')], [c_7465, c_9114])).
% 19.54/8.53  tff(c_9164, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_10, c_9149])).
% 19.54/8.53  tff(c_7060, plain, (![C_5812, B_5813, A_5814]: (~v1_xboole_0(C_5812) | ~m1_subset_1(B_5813, k1_zfmisc_1(C_5812)) | ~r2_hidden(A_5814, B_5813))), inference(cnfTransformation, [status(thm)], [f_59])).
% 19.54/8.53  tff(c_7125, plain, (![B_5821, A_5822, A_5823]: (~v1_xboole_0(B_5821) | ~r2_hidden(A_5822, A_5823) | ~r1_tarski(A_5823, B_5821))), inference(resolution, [status(thm)], [c_22, c_7060])).
% 19.54/8.53  tff(c_7129, plain, (![B_5824, A_5825]: (~v1_xboole_0(B_5824) | ~r1_tarski(A_5825, B_5824) | k1_xboole_0=A_5825)), inference(resolution, [status(thm)], [c_4, c_7125])).
% 19.54/8.53  tff(c_7151, plain, (~v1_xboole_0('#skF_5') | k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_7129])).
% 19.54/8.53  tff(c_7163, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_7151])).
% 19.54/8.53  tff(c_9106, plain, (![A_6007]: (r1_tarski('#skF_6', k2_zfmisc_1(A_6007, '#skF_5')) | ~r1_tarski('#skF_3', A_6007))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_7465, c_9098])).
% 19.54/8.53  tff(c_7566, plain, (![B_5864, C_5865, A_5866]: (k1_xboole_0=B_5864 | v1_funct_2(C_5865, A_5866, B_5864) | k1_relset_1(A_5866, B_5864, C_5865)!=A_5866 | ~m1_subset_1(C_5865, k1_zfmisc_1(k2_zfmisc_1(A_5866, B_5864))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 19.54/8.53  tff(c_10692, plain, (![B_8029, A_8030, A_8031]: (k1_xboole_0=B_8029 | v1_funct_2(A_8030, A_8031, B_8029) | k1_relset_1(A_8031, B_8029, A_8030)!=A_8031 | ~r1_tarski(A_8030, k2_zfmisc_1(A_8031, B_8029)))), inference(resolution, [status(thm)], [c_22, c_7566])).
% 19.54/8.53  tff(c_10724, plain, (![A_6007]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', A_6007, '#skF_5') | k1_relset_1(A_6007, '#skF_5', '#skF_6')!=A_6007 | ~r1_tarski('#skF_3', A_6007))), inference(resolution, [status(thm)], [c_9106, c_10692])).
% 19.54/8.53  tff(c_10805, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_10724])).
% 19.54/8.53  tff(c_10893, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10805, c_2])).
% 19.54/8.53  tff(c_10896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7163, c_10893])).
% 19.54/8.53  tff(c_10898, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_10724])).
% 19.54/8.53  tff(c_42, plain, (![C_31, A_29, B_30]: (m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~r1_tarski(k2_relat_1(C_31), B_30) | ~r1_tarski(k1_relat_1(C_31), A_29) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.54/8.53  tff(c_12210, plain, (![B_10104, C_10105, A_10106]: (k1_xboole_0=B_10104 | v1_funct_2(C_10105, A_10106, B_10104) | k1_relset_1(A_10106, B_10104, C_10105)!=A_10106 | ~r1_tarski(k2_relat_1(C_10105), B_10104) | ~r1_tarski(k1_relat_1(C_10105), A_10106) | ~v1_relat_1(C_10105))), inference(resolution, [status(thm)], [c_42, c_7566])).
% 19.54/8.53  tff(c_12218, plain, (![A_10106]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', A_10106, '#skF_5') | k1_relset_1(A_10106, '#skF_5', '#skF_6')!=A_10106 | ~r1_tarski(k1_relat_1('#skF_6'), A_10106) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7228, c_12210])).
% 19.54/8.53  tff(c_12226, plain, (![A_10106]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', A_10106, '#skF_5') | k1_relset_1(A_10106, '#skF_5', '#skF_6')!=A_10106 | ~r1_tarski('#skF_3', A_10106))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_7465, c_12218])).
% 19.54/8.53  tff(c_12670, plain, (![A_10116]: (v1_funct_2('#skF_6', A_10116, '#skF_5') | k1_relset_1(A_10116, '#skF_5', '#skF_6')!=A_10116 | ~r1_tarski('#skF_3', A_10116))), inference(negUnitSimplification, [status(thm)], [c_10898, c_12226])).
% 19.54/8.53  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 19.54/8.53  tff(c_68, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 19.54/8.53  tff(c_80, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_68])).
% 19.54/8.53  tff(c_122, plain, (~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_80])).
% 19.54/8.53  tff(c_12679, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_12670, c_122])).
% 19.54/8.53  tff(c_12685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_9164, c_12679])).
% 19.54/8.53  tff(c_12687, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_7151])).
% 19.54/8.53  tff(c_7152, plain, (![B_4]: (~v1_xboole_0(B_4) | k1_xboole_0=B_4)), inference(resolution, [status(thm)], [c_10, c_7129])).
% 19.54/8.53  tff(c_12691, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_12687, c_7152])).
% 19.54/8.53  tff(c_12, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 19.54/8.53  tff(c_12714, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_12691, c_12])).
% 19.54/8.53  tff(c_156, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_40])).
% 19.54/8.53  tff(c_171, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_5' | ~r1_tarski('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_156])).
% 19.54/8.53  tff(c_245, plain, (~r1_tarski('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_171])).
% 19.54/8.53  tff(c_12741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12714, c_245])).
% 19.54/8.53  tff(c_12742, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_171])).
% 19.54/8.53  tff(c_13086, plain, (![A_10168, B_10169, C_10170]: (k2_relset_1(A_10168, B_10169, C_10170)=k2_relat_1(C_10170) | ~m1_subset_1(C_10170, k1_zfmisc_1(k2_zfmisc_1(A_10168, B_10169))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 19.54/8.53  tff(c_13099, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_13086])).
% 19.54/8.53  tff(c_13106, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12742, c_13099])).
% 19.54/8.53  tff(c_13246, plain, (![C_10185, A_10186, B_10187]: (m1_subset_1(C_10185, k1_zfmisc_1(k2_zfmisc_1(A_10186, B_10187))) | ~r1_tarski(k2_relat_1(C_10185), B_10187) | ~r1_tarski(k1_relat_1(C_10185), A_10186) | ~v1_relat_1(C_10185))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.54/8.53  tff(c_38, plain, (![A_23, B_24, C_25]: (k1_relset_1(A_23, B_24, C_25)=k1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.54/8.53  tff(c_22159, plain, (![A_17204, B_17205, C_17206]: (k1_relset_1(A_17204, B_17205, C_17206)=k1_relat_1(C_17206) | ~r1_tarski(k2_relat_1(C_17206), B_17205) | ~r1_tarski(k1_relat_1(C_17206), A_17204) | ~v1_relat_1(C_17206))), inference(resolution, [status(thm)], [c_13246, c_38])).
% 19.54/8.53  tff(c_22167, plain, (![A_17204, B_17205]: (k1_relset_1(A_17204, B_17205, '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski('#skF_5', B_17205) | ~r1_tarski(k1_relat_1('#skF_6'), A_17204) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13106, c_22159])).
% 19.54/8.53  tff(c_22227, plain, (![A_17208, B_17209]: (k1_relset_1(A_17208, B_17209, '#skF_6')='#skF_3' | ~r1_tarski('#skF_5', B_17209) | ~r1_tarski('#skF_3', A_17208))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_20081, c_20081, c_22167])).
% 19.54/8.53  tff(c_22240, plain, (![A_17210]: (k1_relset_1(A_17210, '#skF_5', '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_17210))), inference(resolution, [status(thm)], [c_10, c_22227])).
% 19.54/8.53  tff(c_22255, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_10, c_22240])).
% 19.54/8.53  tff(c_13405, plain, (![B_10205, C_10206, A_10207]: (k1_xboole_0=B_10205 | v1_funct_2(C_10206, A_10207, B_10205) | k1_relset_1(A_10207, B_10205, C_10206)!=A_10207 | ~m1_subset_1(C_10206, k1_zfmisc_1(k2_zfmisc_1(A_10207, B_10205))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 19.54/8.53  tff(c_24473, plain, (![B_21200, C_21201, A_21202]: (k1_xboole_0=B_21200 | v1_funct_2(C_21201, A_21202, B_21200) | k1_relset_1(A_21202, B_21200, C_21201)!=A_21202 | ~r1_tarski(k2_relat_1(C_21201), B_21200) | ~r1_tarski(k1_relat_1(C_21201), A_21202) | ~v1_relat_1(C_21201))), inference(resolution, [status(thm)], [c_42, c_13405])).
% 19.54/8.53  tff(c_24481, plain, (![B_21200, A_21202]: (k1_xboole_0=B_21200 | v1_funct_2('#skF_6', A_21202, B_21200) | k1_relset_1(A_21202, B_21200, '#skF_6')!=A_21202 | ~r1_tarski('#skF_5', B_21200) | ~r1_tarski(k1_relat_1('#skF_6'), A_21202) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13106, c_24473])).
% 19.54/8.53  tff(c_24564, plain, (![B_21205, A_21206]: (k1_xboole_0=B_21205 | v1_funct_2('#skF_6', A_21206, B_21205) | k1_relset_1(A_21206, B_21205, '#skF_6')!=A_21206 | ~r1_tarski('#skF_5', B_21205) | ~r1_tarski('#skF_3', A_21206))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_20081, c_24481])).
% 19.54/8.53  tff(c_24573, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_5', '#skF_5') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_24564, c_122])).
% 19.54/8.53  tff(c_24578, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_22255, c_24573])).
% 19.54/8.53  tff(c_16, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 19.54/8.53  tff(c_21446, plain, (![C_17148, A_17149]: (m1_subset_1(C_17148, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_17148), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_17148), A_17149) | ~v1_relat_1(C_17148))), inference(superposition, [status(thm), theory('equality')], [c_16, c_13246])).
% 19.54/8.53  tff(c_21451, plain, (![A_17149]: (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_6'), A_17149) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13106, c_21446])).
% 19.54/8.53  tff(c_21454, plain, (![A_17149]: (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski('#skF_3', A_17149))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_20081, c_21451])).
% 19.54/8.53  tff(c_21525, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_21454])).
% 19.54/8.53  tff(c_24614, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24578, c_21525])).
% 19.54/8.53  tff(c_24679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_24614])).
% 19.54/8.53  tff(c_24681, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_21454])).
% 19.54/8.53  tff(c_12940, plain, (![B_10141, A_1]: (~v1_xboole_0(B_10141) | ~r1_tarski(A_1, B_10141) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_12937])).
% 19.54/8.53  tff(c_24698, plain, (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_24681, c_12940])).
% 19.54/8.53  tff(c_24717, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24698])).
% 19.54/8.53  tff(c_13071, plain, (![C_10164, A_10165]: (v4_relat_1(C_10164, A_10165) | ~m1_subset_1(C_10164, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_13001])).
% 19.54/8.53  tff(c_13079, plain, (![A_8, A_10165]: (v4_relat_1(A_8, A_10165) | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_13071])).
% 19.54/8.53  tff(c_20095, plain, (![A_16]: (r1_tarski('#skF_3', A_16) | ~v4_relat_1('#skF_6', A_16) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20081, c_30])).
% 19.54/8.53  tff(c_20128, plain, (![A_15859]: (r1_tarski('#skF_3', A_15859) | ~v4_relat_1('#skF_6', A_15859))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_20095])).
% 19.54/8.53  tff(c_20144, plain, (![A_10165]: (r1_tarski('#skF_3', A_10165) | ~r1_tarski('#skF_6', k1_xboole_0))), inference(resolution, [status(thm)], [c_13079, c_20128])).
% 19.54/8.53  tff(c_20150, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_20144])).
% 19.54/8.53  tff(c_24744, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24717, c_20150])).
% 19.54/8.53  tff(c_24680, plain, (![A_17149]: (~r1_tarski('#skF_3', A_17149) | m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_21454])).
% 19.54/8.53  tff(c_24950, plain, (![A_17149]: (~r1_tarski('#skF_3', A_17149) | m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_24717, c_24680])).
% 19.54/8.53  tff(c_24953, plain, (![A_21216]: (~r1_tarski('#skF_3', A_21216))), inference(splitLeft, [status(thm)], [c_24950])).
% 19.54/8.53  tff(c_24963, plain, $false, inference(resolution, [status(thm)], [c_10, c_24953])).
% 19.54/8.53  tff(c_24964, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_24950])).
% 19.54/8.53  tff(c_25064, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_24964, c_20])).
% 19.54/8.53  tff(c_25075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24744, c_25064])).
% 19.54/8.53  tff(c_25081, plain, (![A_21225]: (r1_tarski('#skF_3', A_21225))), inference(splitRight, [status(thm)], [c_20144])).
% 19.54/8.53  tff(c_176, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_156])).
% 19.54/8.53  tff(c_25130, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_25081, c_176])).
% 19.54/8.53  tff(c_25180, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25130, c_2])).
% 19.54/8.53  tff(c_25184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19896, c_25180])).
% 19.54/8.53  tff(c_25186, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_19888])).
% 19.54/8.53  tff(c_12960, plain, (![B_4]: (~v1_xboole_0(B_4) | k1_xboole_0=B_4)), inference(resolution, [status(thm)], [c_10, c_12941])).
% 19.54/8.53  tff(c_25190, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_25186, c_12960])).
% 19.54/8.53  tff(c_18, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 19.54/8.53  tff(c_25231, plain, (![B_7]: (k2_zfmisc_1('#skF_3', B_7)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25190, c_25190, c_18])).
% 19.54/8.53  tff(c_12918, plain, (![A_10139]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_10139, '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_12904])).
% 19.54/8.53  tff(c_12936, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_12918])).
% 19.54/8.53  tff(c_25427, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25231, c_12936])).
% 19.54/8.53  tff(c_25433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25186, c_25427])).
% 19.54/8.53  tff(c_25435, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_12918])).
% 19.54/8.53  tff(c_25436, plain, (![A_21237]: (~r2_hidden(A_21237, '#skF_6'))), inference(splitRight, [status(thm)], [c_12918])).
% 19.54/8.53  tff(c_25441, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_4, c_25436])).
% 19.54/8.53  tff(c_25455, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_25441, c_4])).
% 19.54/8.53  tff(c_25929, plain, (![B_21289, A_21290, A_21291]: (~v1_xboole_0(B_21289) | ~r2_hidden(A_21290, A_21291) | ~r1_tarski(A_21291, B_21289))), inference(resolution, [status(thm)], [c_22, c_12904])).
% 19.54/8.53  tff(c_25933, plain, (![B_21292, A_21293]: (~v1_xboole_0(B_21292) | ~r1_tarski(A_21293, B_21292) | A_21293='#skF_6')), inference(resolution, [status(thm)], [c_25455, c_25929])).
% 19.54/8.53  tff(c_25951, plain, (![B_21294]: (~v1_xboole_0(B_21294) | B_21294='#skF_6')), inference(resolution, [status(thm)], [c_10, c_25933])).
% 19.54/8.53  tff(c_25958, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_25435, c_25951])).
% 19.54/8.53  tff(c_125, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.54/8.53  tff(c_133, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_125])).
% 19.54/8.53  tff(c_170, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_133, c_156])).
% 19.54/8.53  tff(c_12833, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_170])).
% 19.54/8.53  tff(c_25962, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_25958, c_12833])).
% 19.54/8.53  tff(c_25967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_25962])).
% 19.54/8.53  tff(c_25968, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_170])).
% 19.54/8.53  tff(c_25980, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_25968, c_74])).
% 19.54/8.53  tff(c_26177, plain, (![C_21316, A_21317, B_21318]: (v4_relat_1(C_21316, A_21317) | ~m1_subset_1(C_21316, k1_zfmisc_1(k2_zfmisc_1(A_21317, B_21318))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 19.54/8.53  tff(c_26218, plain, (![C_21320]: (v4_relat_1(C_21320, '#skF_3') | ~m1_subset_1(C_21320, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_25968, c_26177])).
% 19.54/8.53  tff(c_26231, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_25980, c_26218])).
% 19.54/8.53  tff(c_26254, plain, (![C_21327, B_21328, A_21329]: (~v1_xboole_0(C_21327) | ~m1_subset_1(B_21328, k1_zfmisc_1(C_21327)) | ~r2_hidden(A_21329, B_21328))), inference(cnfTransformation, [status(thm)], [f_59])).
% 19.54/8.53  tff(c_26280, plain, (![B_21331, A_21332, A_21333]: (~v1_xboole_0(B_21331) | ~r2_hidden(A_21332, A_21333) | ~r1_tarski(A_21333, B_21331))), inference(resolution, [status(thm)], [c_22, c_26254])).
% 19.54/8.53  tff(c_26284, plain, (![B_21334, A_21335]: (~v1_xboole_0(B_21334) | ~r1_tarski(A_21335, B_21334) | k1_xboole_0=A_21335)), inference(resolution, [status(thm)], [c_4, c_26280])).
% 19.54/8.53  tff(c_33610, plain, (![A_27570, B_27571]: (~v1_xboole_0(A_27570) | k1_relat_1(B_27571)=k1_xboole_0 | ~v4_relat_1(B_27571, A_27570) | ~v1_relat_1(B_27571))), inference(resolution, [status(thm)], [c_30, c_26284])).
% 19.54/8.53  tff(c_33625, plain, (~v1_xboole_0('#skF_3') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26231, c_33610])).
% 19.54/8.53  tff(c_33640, plain, (~v1_xboole_0('#skF_3') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_242, c_33625])).
% 19.54/8.53  tff(c_33665, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_33640])).
% 19.54/8.53  tff(c_33277, plain, (![A_27534, B_27535, C_27536]: (k1_relset_1(A_27534, B_27535, C_27536)=k1_relat_1(C_27536) | ~m1_subset_1(C_27536, k1_zfmisc_1(k2_zfmisc_1(A_27534, B_27535))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.54/8.53  tff(c_33326, plain, (![C_27542]: (k1_relset_1('#skF_3', '#skF_4', C_27542)=k1_relat_1(C_27542) | ~m1_subset_1(C_27542, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_25968, c_33277])).
% 19.54/8.53  tff(c_33338, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_25980, c_33326])).
% 19.54/8.53  tff(c_34188, plain, (![B_27620, A_27621, C_27622]: (k1_xboole_0=B_27620 | k1_relset_1(A_27621, B_27620, C_27622)=A_27621 | ~v1_funct_2(C_27622, A_27621, B_27620) | ~m1_subset_1(C_27622, k1_zfmisc_1(k2_zfmisc_1(A_27621, B_27620))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 19.54/8.53  tff(c_34194, plain, (![C_27622]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_27622)='#skF_3' | ~v1_funct_2(C_27622, '#skF_3', '#skF_4') | ~m1_subset_1(C_27622, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_25968, c_34188])).
% 19.54/8.53  tff(c_34700, plain, (![C_29054]: (k1_relset_1('#skF_3', '#skF_4', C_29054)='#skF_3' | ~v1_funct_2(C_29054, '#skF_3', '#skF_4') | ~m1_subset_1(C_29054, k1_zfmisc_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_96, c_34194])).
% 19.54/8.53  tff(c_34706, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_25980, c_34700])).
% 19.54/8.53  tff(c_34716, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_33338, c_34706])).
% 19.54/8.53  tff(c_26467, plain, (![A_21353, B_21354, C_21355]: (k2_relset_1(A_21353, B_21354, C_21355)=k2_relat_1(C_21355) | ~m1_subset_1(C_21355, k1_zfmisc_1(k2_zfmisc_1(A_21353, B_21354))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 19.54/8.53  tff(c_33461, plain, (![C_27553]: (k2_relset_1('#skF_3', '#skF_4', C_27553)=k2_relat_1(C_27553) | ~m1_subset_1(C_27553, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_25968, c_26467])).
% 19.54/8.53  tff(c_33467, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_25980, c_33461])).
% 19.54/8.53  tff(c_33475, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12742, c_33467])).
% 19.54/8.53  tff(c_33981, plain, (![B_27598, C_27599, A_27600]: (k1_xboole_0=B_27598 | v1_funct_2(C_27599, A_27600, B_27598) | k1_relset_1(A_27600, B_27598, C_27599)!=A_27600 | ~m1_subset_1(C_27599, k1_zfmisc_1(k2_zfmisc_1(A_27600, B_27598))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 19.54/8.53  tff(c_37064, plain, (![B_30832, C_30833, A_30834]: (k1_xboole_0=B_30832 | v1_funct_2(C_30833, A_30834, B_30832) | k1_relset_1(A_30834, B_30832, C_30833)!=A_30834 | ~r1_tarski(k2_relat_1(C_30833), B_30832) | ~r1_tarski(k1_relat_1(C_30833), A_30834) | ~v1_relat_1(C_30833))), inference(resolution, [status(thm)], [c_42, c_33981])).
% 19.54/8.53  tff(c_37072, plain, (![B_30832, A_30834]: (k1_xboole_0=B_30832 | v1_funct_2('#skF_6', A_30834, B_30832) | k1_relset_1(A_30834, B_30832, '#skF_6')!=A_30834 | ~r1_tarski('#skF_5', B_30832) | ~r1_tarski(k1_relat_1('#skF_6'), A_30834) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_33475, c_37064])).
% 19.54/8.53  tff(c_37112, plain, (![B_30841, A_30842]: (k1_xboole_0=B_30841 | v1_funct_2('#skF_6', A_30842, B_30841) | k1_relset_1(A_30842, B_30841, '#skF_6')!=A_30842 | ~r1_tarski('#skF_5', B_30841) | ~r1_tarski('#skF_3', A_30842))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_34716, c_37072])).
% 19.54/8.53  tff(c_37125, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_5', '#skF_5') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_37112, c_122])).
% 19.54/8.53  tff(c_37135, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_37125])).
% 19.54/8.53  tff(c_37136, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3'), inference(splitLeft, [status(thm)], [c_37135])).
% 19.54/8.53  tff(c_33840, plain, (![C_27586, A_27587, B_27588]: (m1_subset_1(C_27586, k1_zfmisc_1(k2_zfmisc_1(A_27587, B_27588))) | ~r1_tarski(k2_relat_1(C_27586), B_27588) | ~r1_tarski(k1_relat_1(C_27586), A_27587) | ~v1_relat_1(C_27586))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.54/8.53  tff(c_36141, plain, (![A_30756, B_30757, C_30758]: (k1_relset_1(A_30756, B_30757, C_30758)=k1_relat_1(C_30758) | ~r1_tarski(k2_relat_1(C_30758), B_30757) | ~r1_tarski(k1_relat_1(C_30758), A_30756) | ~v1_relat_1(C_30758))), inference(resolution, [status(thm)], [c_33840, c_38])).
% 19.54/8.53  tff(c_36146, plain, (![A_30756, B_30757]: (k1_relset_1(A_30756, B_30757, '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski('#skF_5', B_30757) | ~r1_tarski(k1_relat_1('#skF_6'), A_30756) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_33475, c_36141])).
% 19.54/8.53  tff(c_36795, plain, (![A_30809, B_30810]: (k1_relset_1(A_30809, B_30810, '#skF_6')='#skF_3' | ~r1_tarski('#skF_5', B_30810) | ~r1_tarski('#skF_3', A_30809))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_34716, c_34716, c_36146])).
% 19.54/8.53  tff(c_37137, plain, (![A_30843]: (k1_relset_1(A_30843, '#skF_5', '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_30843))), inference(resolution, [status(thm)], [c_10, c_36795])).
% 19.54/8.53  tff(c_37149, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_10, c_37137])).
% 19.54/8.53  tff(c_37155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37136, c_37149])).
% 19.54/8.53  tff(c_37156, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_37135])).
% 19.54/8.53  tff(c_35690, plain, (![C_30723, A_30724]: (m1_subset_1(C_30723, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_30723), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_30723), A_30724) | ~v1_relat_1(C_30723))), inference(superposition, [status(thm), theory('equality')], [c_16, c_33840])).
% 19.54/8.53  tff(c_35692, plain, (![A_30724]: (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_6'), A_30724) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_33475, c_35690])).
% 19.54/8.53  tff(c_35694, plain, (![A_30724]: (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski('#skF_3', A_30724))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_34716, c_35692])).
% 19.54/8.53  tff(c_36125, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_35694])).
% 19.54/8.53  tff(c_37179, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_37156, c_36125])).
% 19.54/8.53  tff(c_37243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_37179])).
% 19.54/8.53  tff(c_37245, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_35694])).
% 19.54/8.53  tff(c_26283, plain, (![B_21331, A_1]: (~v1_xboole_0(B_21331) | ~r1_tarski(A_1, B_21331) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_26280])).
% 19.54/8.53  tff(c_37275, plain, (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_37245, c_26283])).
% 19.54/8.53  tff(c_37294, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_37275])).
% 19.54/8.53  tff(c_26239, plain, (![C_21323, A_21324]: (v4_relat_1(C_21323, A_21324) | ~m1_subset_1(C_21323, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_26177])).
% 19.54/8.53  tff(c_26247, plain, (![A_8, A_21324]: (v4_relat_1(A_8, A_21324) | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_26239])).
% 19.54/8.53  tff(c_34736, plain, (![A_16]: (r1_tarski('#skF_3', A_16) | ~v4_relat_1('#skF_6', A_16) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_34716, c_30])).
% 19.54/8.53  tff(c_34886, plain, (![A_29059]: (r1_tarski('#skF_3', A_29059) | ~v4_relat_1('#skF_6', A_29059))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_34736])).
% 19.54/8.53  tff(c_34909, plain, (![A_21324]: (r1_tarski('#skF_3', A_21324) | ~r1_tarski('#skF_6', k1_xboole_0))), inference(resolution, [status(thm)], [c_26247, c_34886])).
% 19.54/8.53  tff(c_34915, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_34909])).
% 19.54/8.53  tff(c_37315, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_37294, c_34915])).
% 19.54/8.53  tff(c_37626, plain, (![A_30862]: (k2_zfmisc_1(A_30862, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_37294, c_37294, c_16])).
% 19.54/8.53  tff(c_37363, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_37294, c_12])).
% 19.54/8.53  tff(c_36033, plain, (![C_30746, A_30747, B_30748]: (r1_tarski(C_30746, k2_zfmisc_1(A_30747, B_30748)) | ~r1_tarski(k2_relat_1(C_30746), B_30748) | ~r1_tarski(k1_relat_1(C_30746), A_30747) | ~v1_relat_1(C_30746))), inference(resolution, [status(thm)], [c_33840, c_20])).
% 19.54/8.53  tff(c_36038, plain, (![A_30747, B_30748]: (r1_tarski('#skF_6', k2_zfmisc_1(A_30747, B_30748)) | ~r1_tarski('#skF_5', B_30748) | ~r1_tarski(k1_relat_1('#skF_6'), A_30747) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_33475, c_36033])).
% 19.54/8.53  tff(c_36044, plain, (![A_30747, B_30748]: (r1_tarski('#skF_6', k2_zfmisc_1(A_30747, B_30748)) | ~r1_tarski('#skF_5', B_30748) | ~r1_tarski('#skF_3', A_30747))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_34716, c_36038])).
% 19.54/8.53  tff(c_37576, plain, (![A_30747, B_30748]: (r1_tarski('#skF_6', k2_zfmisc_1(A_30747, B_30748)) | ~r1_tarski('#skF_3', A_30747))), inference(demodulation, [status(thm), theory('equality')], [c_37363, c_36044])).
% 19.54/8.53  tff(c_37631, plain, (![A_30862]: (r1_tarski('#skF_6', '#skF_5') | ~r1_tarski('#skF_3', A_30862))), inference(superposition, [status(thm), theory('equality')], [c_37626, c_37576])).
% 19.54/8.53  tff(c_37731, plain, (![A_30863]: (~r1_tarski('#skF_3', A_30863))), inference(negUnitSimplification, [status(thm)], [c_37315, c_37631])).
% 19.54/8.53  tff(c_37741, plain, $false, inference(resolution, [status(thm)], [c_10, c_37731])).
% 19.54/8.53  tff(c_37755, plain, (![A_30866]: (r1_tarski('#skF_3', A_30866))), inference(splitRight, [status(thm)], [c_34909])).
% 19.54/8.53  tff(c_37829, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_37755, c_176])).
% 19.54/8.53  tff(c_37880, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37829, c_2])).
% 19.54/8.53  tff(c_37884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33665, c_37880])).
% 19.54/8.53  tff(c_37886, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_33640])).
% 19.54/8.53  tff(c_26303, plain, (![B_4]: (~v1_xboole_0(B_4) | k1_xboole_0=B_4)), inference(resolution, [status(thm)], [c_10, c_26284])).
% 19.54/8.53  tff(c_37890, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_37886, c_26303])).
% 19.54/8.53  tff(c_14, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 19.54/8.53  tff(c_25985, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_25968, c_14])).
% 19.54/8.53  tff(c_25993, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_96, c_25985])).
% 19.54/8.53  tff(c_26007, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_25993])).
% 19.54/8.53  tff(c_37949, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_37890, c_26007])).
% 19.54/8.53  tff(c_37962, plain, (![B_7]: (k2_zfmisc_1('#skF_3', B_7)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37890, c_37890, c_18])).
% 19.54/8.53  tff(c_38191, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_37962, c_25968])).
% 19.54/8.53  tff(c_38193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37949, c_38191])).
% 19.54/8.53  tff(c_38194, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_25993])).
% 19.54/8.53  tff(c_134, plain, (![A_59, B_60]: (m1_subset_1('#skF_2'(A_59, B_60), k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 19.54/8.53  tff(c_145, plain, (![B_61]: (m1_subset_1('#skF_2'(k1_xboole_0, B_61), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_134])).
% 19.54/8.53  tff(c_149, plain, (![B_61]: (r1_tarski('#skF_2'(k1_xboole_0, B_61), k1_xboole_0))), inference(resolution, [status(thm)], [c_145, c_20])).
% 19.54/8.53  tff(c_158, plain, (![B_61]: ('#skF_2'(k1_xboole_0, B_61)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_2'(k1_xboole_0, B_61)))), inference(resolution, [status(thm)], [c_149, c_156])).
% 19.54/8.53  tff(c_180, plain, (![B_66]: ('#skF_2'(k1_xboole_0, B_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_158])).
% 19.54/8.53  tff(c_56, plain, (![A_35, B_36]: (v1_funct_2('#skF_2'(A_35, B_36), A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_127])).
% 19.54/8.53  tff(c_191, plain, (![B_66]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_66))), inference(superposition, [status(thm), theory('equality')], [c_180, c_56])).
% 19.54/8.53  tff(c_38201, plain, (![B_66]: (v1_funct_2('#skF_3', '#skF_3', B_66))), inference(demodulation, [status(thm), theory('equality')], [c_38194, c_38194, c_191])).
% 19.54/8.53  tff(c_38195, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_25993])).
% 19.54/8.53  tff(c_38217, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38194, c_38195])).
% 19.54/8.53  tff(c_38222, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38217, c_122])).
% 19.54/8.53  tff(c_38396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38201, c_38222])).
% 19.54/8.53  tff(c_38397, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_80])).
% 19.54/8.53  tff(c_39121, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski(k1_relat_1('#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_39098, c_38397])).
% 19.54/8.53  tff(c_39139, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38475, c_39007, c_39121])).
% 19.54/8.53  tff(c_39142, plain, (~v4_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_39139])).
% 19.54/8.53  tff(c_39146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38475, c_38810, c_39142])).
% 19.54/8.53  tff(c_39148, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_70])).
% 19.54/8.53  tff(c_39182, plain, (![B_7]: (k2_zfmisc_1('#skF_4', B_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39148, c_39148, c_18])).
% 19.54/8.53  tff(c_39219, plain, (![A_31004, B_31005]: (m1_subset_1('#skF_2'(A_31004, B_31005), k1_zfmisc_1(k2_zfmisc_1(A_31004, B_31005))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 19.54/8.53  tff(c_39230, plain, (![B_31006]: (m1_subset_1('#skF_2'('#skF_4', B_31006), k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_39182, c_39219])).
% 19.54/8.53  tff(c_39282, plain, (![B_31010]: (r1_tarski('#skF_2'('#skF_4', B_31010), '#skF_4'))), inference(resolution, [status(thm)], [c_39230, c_20])).
% 19.54/8.53  tff(c_39147, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_70])).
% 19.54/8.53  tff(c_39156, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_39148, c_39147])).
% 19.54/8.53  tff(c_39150, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_39147, c_12])).
% 19.54/8.53  tff(c_39167, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_39156, c_39150])).
% 19.54/8.53  tff(c_39235, plain, (![B_31007, A_31008]: (B_31007=A_31008 | ~r1_tarski(B_31007, A_31008) | ~r1_tarski(A_31008, B_31007))), inference(cnfTransformation, [status(thm)], [f_40])).
% 19.54/8.53  tff(c_39248, plain, (![A_5]: (A_5='#skF_4' | ~r1_tarski(A_5, '#skF_4'))), inference(resolution, [status(thm)], [c_39167, c_39235])).
% 19.54/8.53  tff(c_39296, plain, (![B_31011]: ('#skF_2'('#skF_4', B_31011)='#skF_4')), inference(resolution, [status(thm)], [c_39282, c_39248])).
% 19.54/8.53  tff(c_39304, plain, (![B_31011]: (v1_funct_2('#skF_4', '#skF_4', B_31011))), inference(superposition, [status(thm), theory('equality')], [c_39296, c_56])).
% 19.54/8.53  tff(c_39149, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_39147, c_39147, c_16])).
% 19.54/8.53  tff(c_39170, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39156, c_39156, c_39149])).
% 19.54/8.53  tff(c_39178, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39170, c_39156, c_74])).
% 19.54/8.53  tff(c_39210, plain, (![A_31002, B_31003]: (r1_tarski(A_31002, B_31003) | ~m1_subset_1(A_31002, k1_zfmisc_1(B_31003)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.54/8.53  tff(c_39218, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_39178, c_39210])).
% 19.54/8.53  tff(c_39237, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_39218, c_39235])).
% 19.54/8.53  tff(c_39246, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_39167, c_39237])).
% 19.54/8.53  tff(c_39208, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_39156, c_39178, c_39182, c_39156, c_80])).
% 19.54/8.53  tff(c_39254, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_39246, c_39208])).
% 19.54/8.53  tff(c_39339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39304, c_39254])).
% 19.54/8.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.54/8.53  
% 19.54/8.53  Inference rules
% 19.54/8.53  ----------------------
% 19.54/8.53  #Ref     : 0
% 19.54/8.53  #Sup     : 9329
% 19.54/8.53  #Fact    : 0
% 19.54/8.53  #Define  : 0
% 19.54/8.53  #Split   : 106
% 19.54/8.53  #Chain   : 0
% 19.54/8.53  #Close   : 0
% 19.54/8.53  
% 19.54/8.53  Ordering : KBO
% 19.54/8.53  
% 19.54/8.53  Simplification rules
% 19.54/8.53  ----------------------
% 19.54/8.53  #Subsume      : 2776
% 19.54/8.53  #Demod        : 6937
% 19.54/8.53  #Tautology    : 2734
% 19.54/8.53  #SimpNegUnit  : 366
% 19.54/8.53  #BackRed      : 1298
% 19.54/8.53  
% 19.54/8.53  #Partial instantiations: 8196
% 19.54/8.53  #Strategies tried      : 1
% 19.54/8.53  
% 19.54/8.53  Timing (in seconds)
% 19.54/8.53  ----------------------
% 19.54/8.53  Preprocessing        : 0.56
% 19.54/8.53  Parsing              : 0.29
% 19.54/8.53  CNF conversion       : 0.04
% 19.54/8.53  Main loop            : 7.00
% 19.54/8.53  Inferencing          : 2.23
% 19.54/8.53  Reduction            : 2.46
% 19.54/8.53  Demodulation         : 1.72
% 19.54/8.53  BG Simplification    : 0.18
% 19.54/8.53  Subsumption          : 1.62
% 19.54/8.53  Abstraction          : 0.24
% 19.54/8.53  MUC search           : 0.00
% 19.54/8.53  Cooper               : 0.00
% 19.54/8.53  Total                : 7.66
% 19.54/8.53  Index Insertion      : 0.00
% 19.54/8.53  Index Deletion       : 0.00
% 19.54/8.53  Index Matching       : 0.00
% 19.54/8.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
