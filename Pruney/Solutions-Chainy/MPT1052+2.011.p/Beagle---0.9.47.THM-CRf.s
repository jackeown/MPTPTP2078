%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:10 EST 2020

% Result     : Theorem 13.14s
% Output     : CNFRefutation 13.14s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 353 expanded)
%              Number of leaves         :   35 ( 131 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 ( 741 expanded)
%              Number of equality atoms :   47 ( 155 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_74,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_86936,plain,(
    ! [B_28944,A_28945] :
      ( r1_tarski(k2_relat_1(B_28944),A_28945)
      | ~ v5_relat_1(B_28944,A_28945)
      | ~ v1_relat_1(B_28944) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_69,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_81,plain,(
    ! [A_34,B_35] :
      ( v1_xboole_0(k1_funct_2(A_34,B_35))
      | ~ v1_xboole_0(B_35)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_49,plain,(
    ! [B_25,A_26] :
      ( ~ r2_hidden(B_25,A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_49])).

tff(c_91,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_53])).

tff(c_93,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [B_27,A_28] :
      ( ~ v1_xboole_0(B_27)
      | B_27 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_57,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_95,plain,(
    ! [A_39,B_40] :
      ( k1_funct_2(A_39,B_40) = k1_xboole_0
      | ~ v1_xboole_0(B_40)
      | v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_81,c_57])).

tff(c_102,plain,(
    ! [A_41] :
      ( k1_funct_2(A_41,k1_xboole_0) = k1_xboole_0
      | v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_117,plain,(
    k1_funct_2('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102,c_93])).

tff(c_34,plain,(
    ! [C_22,A_20,B_21] :
      ( m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ r2_hidden(C_22,k1_funct_2(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6987,plain,(
    ! [C_2048,A_2049] :
      ( k1_xboole_0 = C_2048
      | ~ v1_funct_2(C_2048,A_2049,k1_xboole_0)
      | k1_xboole_0 = A_2049
      | ~ m1_subset_1(C_2048,k1_zfmisc_1(k2_zfmisc_1(A_2049,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_19389,plain,(
    ! [C_7864,A_7865] :
      ( k1_xboole_0 = C_7864
      | ~ v1_funct_2(C_7864,A_7865,k1_xboole_0)
      | k1_xboole_0 = A_7865
      | ~ r2_hidden(C_7864,k1_funct_2(A_7865,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_34,c_6987])).

tff(c_19522,plain,(
    ! [C_7864] :
      ( k1_xboole_0 = C_7864
      | ~ v1_funct_2(C_7864,'#skF_3',k1_xboole_0)
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_7864,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_19389])).

tff(c_19531,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_19522])).

tff(c_19591,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19531,c_6])).

tff(c_19593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_19591])).

tff(c_19595,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_19522])).

tff(c_195,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_funct_2(C_46,A_47,B_48)
      | ~ r2_hidden(C_46,k1_funct_2(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_213,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_195])).

tff(c_6235,plain,(
    ! [A_1834,B_1835,C_1836] :
      ( k1_relset_1(A_1834,B_1835,C_1836) = k1_relat_1(C_1836)
      | ~ m1_subset_1(C_1836,k1_zfmisc_1(k2_zfmisc_1(A_1834,B_1835))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7059,plain,(
    ! [A_2084,B_2085,C_2086] :
      ( k1_relset_1(A_2084,B_2085,C_2086) = k1_relat_1(C_2086)
      | ~ r2_hidden(C_2086,k1_funct_2(A_2084,B_2085)) ) ),
    inference(resolution,[status(thm)],[c_34,c_6235])).

tff(c_7162,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_7059])).

tff(c_16244,plain,(
    ! [B_5909,A_5910,C_5911] :
      ( k1_xboole_0 = B_5909
      | k1_relset_1(A_5910,B_5909,C_5911) = A_5910
      | ~ v1_funct_2(C_5911,A_5910,B_5909)
      | ~ m1_subset_1(C_5911,k1_zfmisc_1(k2_zfmisc_1(A_5910,B_5909))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32906,plain,(
    ! [B_12092,A_12093,C_12094] :
      ( k1_xboole_0 = B_12092
      | k1_relset_1(A_12093,B_12092,C_12094) = A_12093
      | ~ v1_funct_2(C_12094,A_12093,B_12092)
      | ~ r2_hidden(C_12094,k1_funct_2(A_12093,B_12092)) ) ),
    inference(resolution,[status(thm)],[c_34,c_16244])).

tff(c_33107,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_32906])).

tff(c_33126,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_7162,c_33107])).

tff(c_33128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_19595,c_33126])).

tff(c_33130,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_33143,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_33130,c_57])).

tff(c_33129,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_33136,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_33129,c_57])).

tff(c_33152,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33143,c_33136])).

tff(c_33158,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33152,c_69])).

tff(c_33160,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33152,c_44])).

tff(c_36,plain,(
    ! [C_22,A_20,B_21] :
      ( v1_funct_2(C_22,A_20,B_21)
      | ~ r2_hidden(C_22,k1_funct_2(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_33199,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_33160,c_36])).

tff(c_39063,plain,(
    ! [A_13937,B_13938,C_13939] :
      ( k1_relset_1(A_13937,B_13938,C_13939) = k1_relat_1(C_13939)
      | ~ m1_subset_1(C_13939,k1_zfmisc_1(k2_zfmisc_1(A_13937,B_13938))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_39570,plain,(
    ! [A_14080,B_14081,C_14082] :
      ( k1_relset_1(A_14080,B_14081,C_14082) = k1_relat_1(C_14082)
      | ~ r2_hidden(C_14082,k1_funct_2(A_14080,B_14081)) ) ),
    inference(resolution,[status(thm)],[c_34,c_39063])).

tff(c_39663,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_33160,c_39570])).

tff(c_28,plain,(
    ! [B_16,C_17] :
      ( k1_relset_1(k1_xboole_0,B_16,C_17) = k1_xboole_0
      | ~ v1_funct_2(C_17,k1_xboole_0,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46401,plain,(
    ! [B_16788,C_16789] :
      ( k1_relset_1('#skF_3',B_16788,C_16789) = '#skF_3'
      | ~ v1_funct_2(C_16789,'#skF_3',B_16788)
      | ~ m1_subset_1(C_16789,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_16788))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33143,c_33143,c_33143,c_33143,c_28])).

tff(c_86493,plain,(
    ! [B_28790,C_28791] :
      ( k1_relset_1('#skF_3',B_28790,C_28791) = '#skF_3'
      | ~ v1_funct_2(C_28791,'#skF_3',B_28790)
      | ~ r2_hidden(C_28791,k1_funct_2('#skF_3',B_28790)) ) ),
    inference(resolution,[status(thm)],[c_34,c_46401])).

tff(c_86764,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_33160,c_86493])).

tff(c_86783,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33199,c_39663,c_86764])).

tff(c_86785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33158,c_86783])).

tff(c_86786,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_86939,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86936,c_86786])).

tff(c_86942,plain,(
    ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_86939])).

tff(c_87089,plain,(
    ! [C_28966,A_28967,B_28968] :
      ( m1_subset_1(C_28966,k1_zfmisc_1(k2_zfmisc_1(A_28967,B_28968)))
      | ~ r2_hidden(C_28966,k1_funct_2(A_28967,B_28968)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14,plain,(
    ! [C_11,B_10,A_9] :
      ( v5_relat_1(C_11,B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_87098,plain,(
    ! [C_28969,B_28970,A_28971] :
      ( v5_relat_1(C_28969,B_28970)
      | ~ r2_hidden(C_28969,k1_funct_2(A_28971,B_28970)) ) ),
    inference(resolution,[status(thm)],[c_87089,c_14])).

tff(c_87120,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_87098])).

tff(c_87125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86942,c_87120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.14/5.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.14/5.33  
% 13.14/5.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.14/5.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 13.14/5.33  
% 13.14/5.33  %Foreground sorts:
% 13.14/5.33  
% 13.14/5.33  
% 13.14/5.33  %Background operators:
% 13.14/5.33  
% 13.14/5.33  
% 13.14/5.33  %Foreground operators:
% 13.14/5.33  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 13.14/5.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.14/5.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.14/5.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.14/5.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.14/5.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.14/5.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.14/5.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.14/5.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.14/5.33  tff('#skF_2', type, '#skF_2': $i).
% 13.14/5.33  tff('#skF_3', type, '#skF_3': $i).
% 13.14/5.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.14/5.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.14/5.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.14/5.33  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 13.14/5.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.14/5.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.14/5.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.14/5.33  tff('#skF_4', type, '#skF_4': $i).
% 13.14/5.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.14/5.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.14/5.33  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 13.14/5.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.14/5.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.14/5.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.14/5.33  
% 13.14/5.35  tff(f_102, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 13.14/5.35  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 13.14/5.35  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 13.14/5.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.14/5.35  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.14/5.35  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 13.14/5.35  tff(f_89, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 13.14/5.35  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.14/5.35  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.14/5.35  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.14/5.35  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.14/5.35  tff(c_86936, plain, (![B_28944, A_28945]: (r1_tarski(k2_relat_1(B_28944), A_28945) | ~v5_relat_1(B_28944, A_28945) | ~v1_relat_1(B_28944))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.14/5.35  tff(c_42, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.14/5.35  tff(c_69, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 13.14/5.35  tff(c_81, plain, (![A_34, B_35]: (v1_xboole_0(k1_funct_2(A_34, B_35)) | ~v1_xboole_0(B_35) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.14/5.35  tff(c_44, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.14/5.35  tff(c_49, plain, (![B_25, A_26]: (~r2_hidden(B_25, A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.14/5.35  tff(c_53, plain, (~v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_49])).
% 13.14/5.35  tff(c_91, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_81, c_53])).
% 13.14/5.35  tff(c_93, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_91])).
% 13.14/5.35  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.14/5.35  tff(c_54, plain, (![B_27, A_28]: (~v1_xboole_0(B_27) | B_27=A_28 | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.14/5.35  tff(c_57, plain, (![A_28]: (k1_xboole_0=A_28 | ~v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_6, c_54])).
% 13.14/5.35  tff(c_95, plain, (![A_39, B_40]: (k1_funct_2(A_39, B_40)=k1_xboole_0 | ~v1_xboole_0(B_40) | v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_81, c_57])).
% 13.14/5.35  tff(c_102, plain, (![A_41]: (k1_funct_2(A_41, k1_xboole_0)=k1_xboole_0 | v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_6, c_95])).
% 13.14/5.35  tff(c_117, plain, (k1_funct_2('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_102, c_93])).
% 13.14/5.35  tff(c_34, plain, (![C_22, A_20, B_21]: (m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~r2_hidden(C_22, k1_funct_2(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.14/5.35  tff(c_6987, plain, (![C_2048, A_2049]: (k1_xboole_0=C_2048 | ~v1_funct_2(C_2048, A_2049, k1_xboole_0) | k1_xboole_0=A_2049 | ~m1_subset_1(C_2048, k1_zfmisc_1(k2_zfmisc_1(A_2049, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.14/5.35  tff(c_19389, plain, (![C_7864, A_7865]: (k1_xboole_0=C_7864 | ~v1_funct_2(C_7864, A_7865, k1_xboole_0) | k1_xboole_0=A_7865 | ~r2_hidden(C_7864, k1_funct_2(A_7865, k1_xboole_0)))), inference(resolution, [status(thm)], [c_34, c_6987])).
% 13.14/5.35  tff(c_19522, plain, (![C_7864]: (k1_xboole_0=C_7864 | ~v1_funct_2(C_7864, '#skF_3', k1_xboole_0) | k1_xboole_0='#skF_3' | ~r2_hidden(C_7864, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_117, c_19389])).
% 13.14/5.35  tff(c_19531, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_19522])).
% 13.14/5.35  tff(c_19591, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19531, c_6])).
% 13.14/5.35  tff(c_19593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_19591])).
% 13.14/5.35  tff(c_19595, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_19522])).
% 13.14/5.35  tff(c_195, plain, (![C_46, A_47, B_48]: (v1_funct_2(C_46, A_47, B_48) | ~r2_hidden(C_46, k1_funct_2(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.14/5.35  tff(c_213, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_195])).
% 13.14/5.35  tff(c_6235, plain, (![A_1834, B_1835, C_1836]: (k1_relset_1(A_1834, B_1835, C_1836)=k1_relat_1(C_1836) | ~m1_subset_1(C_1836, k1_zfmisc_1(k2_zfmisc_1(A_1834, B_1835))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.14/5.35  tff(c_7059, plain, (![A_2084, B_2085, C_2086]: (k1_relset_1(A_2084, B_2085, C_2086)=k1_relat_1(C_2086) | ~r2_hidden(C_2086, k1_funct_2(A_2084, B_2085)))), inference(resolution, [status(thm)], [c_34, c_6235])).
% 13.14/5.35  tff(c_7162, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_7059])).
% 13.14/5.35  tff(c_16244, plain, (![B_5909, A_5910, C_5911]: (k1_xboole_0=B_5909 | k1_relset_1(A_5910, B_5909, C_5911)=A_5910 | ~v1_funct_2(C_5911, A_5910, B_5909) | ~m1_subset_1(C_5911, k1_zfmisc_1(k2_zfmisc_1(A_5910, B_5909))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.14/5.35  tff(c_32906, plain, (![B_12092, A_12093, C_12094]: (k1_xboole_0=B_12092 | k1_relset_1(A_12093, B_12092, C_12094)=A_12093 | ~v1_funct_2(C_12094, A_12093, B_12092) | ~r2_hidden(C_12094, k1_funct_2(A_12093, B_12092)))), inference(resolution, [status(thm)], [c_34, c_16244])).
% 13.14/5.35  tff(c_33107, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_32906])).
% 13.14/5.35  tff(c_33126, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_213, c_7162, c_33107])).
% 13.14/5.35  tff(c_33128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_19595, c_33126])).
% 13.14/5.35  tff(c_33130, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_91])).
% 13.14/5.35  tff(c_33143, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_33130, c_57])).
% 13.14/5.35  tff(c_33129, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_91])).
% 13.14/5.35  tff(c_33136, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_33129, c_57])).
% 13.14/5.35  tff(c_33152, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_33143, c_33136])).
% 13.14/5.35  tff(c_33158, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_33152, c_69])).
% 13.14/5.35  tff(c_33160, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_33152, c_44])).
% 13.14/5.35  tff(c_36, plain, (![C_22, A_20, B_21]: (v1_funct_2(C_22, A_20, B_21) | ~r2_hidden(C_22, k1_funct_2(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.14/5.35  tff(c_33199, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_33160, c_36])).
% 13.14/5.35  tff(c_39063, plain, (![A_13937, B_13938, C_13939]: (k1_relset_1(A_13937, B_13938, C_13939)=k1_relat_1(C_13939) | ~m1_subset_1(C_13939, k1_zfmisc_1(k2_zfmisc_1(A_13937, B_13938))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.14/5.35  tff(c_39570, plain, (![A_14080, B_14081, C_14082]: (k1_relset_1(A_14080, B_14081, C_14082)=k1_relat_1(C_14082) | ~r2_hidden(C_14082, k1_funct_2(A_14080, B_14081)))), inference(resolution, [status(thm)], [c_34, c_39063])).
% 13.14/5.35  tff(c_39663, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_33160, c_39570])).
% 13.14/5.35  tff(c_28, plain, (![B_16, C_17]: (k1_relset_1(k1_xboole_0, B_16, C_17)=k1_xboole_0 | ~v1_funct_2(C_17, k1_xboole_0, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_16))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.14/5.35  tff(c_46401, plain, (![B_16788, C_16789]: (k1_relset_1('#skF_3', B_16788, C_16789)='#skF_3' | ~v1_funct_2(C_16789, '#skF_3', B_16788) | ~m1_subset_1(C_16789, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_16788))))), inference(demodulation, [status(thm), theory('equality')], [c_33143, c_33143, c_33143, c_33143, c_28])).
% 13.14/5.35  tff(c_86493, plain, (![B_28790, C_28791]: (k1_relset_1('#skF_3', B_28790, C_28791)='#skF_3' | ~v1_funct_2(C_28791, '#skF_3', B_28790) | ~r2_hidden(C_28791, k1_funct_2('#skF_3', B_28790)))), inference(resolution, [status(thm)], [c_34, c_46401])).
% 13.14/5.35  tff(c_86764, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_33160, c_86493])).
% 13.14/5.35  tff(c_86783, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_33199, c_39663, c_86764])).
% 13.14/5.35  tff(c_86785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33158, c_86783])).
% 13.14/5.35  tff(c_86786, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 13.14/5.35  tff(c_86939, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86936, c_86786])).
% 13.14/5.35  tff(c_86942, plain, (~v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_86939])).
% 13.14/5.35  tff(c_87089, plain, (![C_28966, A_28967, B_28968]: (m1_subset_1(C_28966, k1_zfmisc_1(k2_zfmisc_1(A_28967, B_28968))) | ~r2_hidden(C_28966, k1_funct_2(A_28967, B_28968)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.14/5.35  tff(c_14, plain, (![C_11, B_10, A_9]: (v5_relat_1(C_11, B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.14/5.35  tff(c_87098, plain, (![C_28969, B_28970, A_28971]: (v5_relat_1(C_28969, B_28970) | ~r2_hidden(C_28969, k1_funct_2(A_28971, B_28970)))), inference(resolution, [status(thm)], [c_87089, c_14])).
% 13.14/5.35  tff(c_87120, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_87098])).
% 13.14/5.35  tff(c_87125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86942, c_87120])).
% 13.14/5.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.14/5.35  
% 13.14/5.35  Inference rules
% 13.14/5.35  ----------------------
% 13.14/5.35  #Ref     : 0
% 13.14/5.35  #Sup     : 10049
% 13.14/5.35  #Fact    : 16
% 13.14/5.35  #Define  : 0
% 13.14/5.35  #Split   : 24
% 13.14/5.35  #Chain   : 0
% 13.14/5.35  #Close   : 0
% 13.14/5.35  
% 13.14/5.35  Ordering : KBO
% 13.14/5.35  
% 13.14/5.35  Simplification rules
% 13.14/5.35  ----------------------
% 13.14/5.35  #Subsume      : 6258
% 13.14/5.35  #Demod        : 1808
% 13.14/5.35  #Tautology    : 1147
% 13.14/5.35  #SimpNegUnit  : 589
% 13.14/5.35  #BackRed      : 111
% 13.14/5.35  
% 13.14/5.35  #Partial instantiations: 21801
% 13.14/5.35  #Strategies tried      : 1
% 13.14/5.35  
% 13.14/5.35  Timing (in seconds)
% 13.14/5.35  ----------------------
% 13.14/5.35  Preprocessing        : 0.32
% 13.14/5.35  Parsing              : 0.17
% 13.14/5.35  CNF conversion       : 0.02
% 13.14/5.35  Main loop            : 4.24
% 13.14/5.35  Inferencing          : 1.30
% 13.14/5.35  Reduction            : 0.85
% 13.14/5.35  Demodulation         : 0.58
% 13.14/5.35  BG Simplification    : 0.09
% 13.14/5.35  Subsumption          : 1.85
% 13.14/5.35  Abstraction          : 0.14
% 13.14/5.35  MUC search           : 0.00
% 13.14/5.35  Cooper               : 0.00
% 13.14/5.35  Total                : 4.59
% 13.14/5.35  Index Insertion      : 0.00
% 13.14/5.35  Index Deletion       : 0.00
% 13.14/5.35  Index Matching       : 0.00
% 13.14/5.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
