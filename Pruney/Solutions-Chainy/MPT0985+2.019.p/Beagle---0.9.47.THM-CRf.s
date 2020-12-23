%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:28 EST 2020

% Result     : Theorem 10.16s
% Output     : CNFRefutation 10.16s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 537 expanded)
%              Number of leaves         :   48 ( 199 expanded)
%              Depth                    :   11
%              Number of atoms          :  300 (1565 expanded)
%              Number of equality atoms :   71 ( 303 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_177,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_160,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_137,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_150,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(c_90,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_20393,plain,(
    ! [C_695,A_696,B_697] :
      ( v1_relat_1(C_695)
      | ~ m1_subset_1(C_695,k1_zfmisc_1(k2_zfmisc_1(A_696,B_697))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_20410,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_20393])).

tff(c_94,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_88,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_20748,plain,(
    ! [A_732] :
      ( k4_relat_1(A_732) = k2_funct_1(A_732)
      | ~ v2_funct_1(A_732)
      | ~ v1_funct_1(A_732)
      | ~ v1_relat_1(A_732) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20751,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_20748])).

tff(c_20754,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20410,c_94,c_20751])).

tff(c_32,plain,(
    ! [A_19] :
      ( v1_xboole_0(k4_relat_1(A_19))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20770,plain,
    ( v1_xboole_0(k2_funct_1('#skF_6'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_20754,c_32])).

tff(c_20776,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_20770])).

tff(c_20779,plain,(
    ! [C_733,A_734,B_735] :
      ( v1_xboole_0(C_733)
      | ~ m1_subset_1(C_733,k1_zfmisc_1(k2_zfmisc_1(A_734,B_735)))
      | ~ v1_xboole_0(A_734) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_20792,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_20779])).

tff(c_20804,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_20776,c_20792])).

tff(c_86,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_21259,plain,(
    ! [A_763,B_764,C_765] :
      ( k2_relset_1(A_763,B_764,C_765) = k2_relat_1(C_765)
      | ~ m1_subset_1(C_765,k1_zfmisc_1(k2_zfmisc_1(A_763,B_764))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_21272,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_21259])).

tff(c_21283,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_21272])).

tff(c_44,plain,(
    ! [A_23] :
      ( k1_relat_1(k2_funct_1(A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_364,plain,(
    ! [A_72] :
      ( v1_funct_1(k2_funct_1(A_72))
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_84,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_249,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_367,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_364,c_249])).

tff(c_370,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_367])).

tff(c_388,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_395,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_388])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_395])).

tff(c_405,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_523,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_567,plain,(
    ! [C_102,A_103,B_104] :
      ( v1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_580,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_567])).

tff(c_1507,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_relset_1(A_171,B_172,C_173) = k2_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1520,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_1507])).

tff(c_1531,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1520])).

tff(c_40,plain,(
    ! [A_22] :
      ( v1_relat_1(k2_funct_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_406,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1116,plain,(
    ! [A_150] :
      ( k1_relat_1(k2_funct_1(A_150)) = k2_relat_1(A_150)
      | ~ v2_funct_1(A_150)
      | ~ v1_funct_1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_80,plain,(
    ! [A_43] :
      ( v1_funct_2(A_43,k1_relat_1(A_43),k2_relat_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_18136,plain,(
    ! [A_636] :
      ( v1_funct_2(k2_funct_1(A_636),k2_relat_1(A_636),k2_relat_1(k2_funct_1(A_636)))
      | ~ v1_funct_1(k2_funct_1(A_636))
      | ~ v1_relat_1(k2_funct_1(A_636))
      | ~ v2_funct_1(A_636)
      | ~ v1_funct_1(A_636)
      | ~ v1_relat_1(A_636) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1116,c_80])).

tff(c_18190,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_18136])).

tff(c_18244,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_94,c_88,c_406,c_18190])).

tff(c_18249,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_18244])).

tff(c_18252,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_18249])).

tff(c_18256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_94,c_18252])).

tff(c_18258,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_18244])).

tff(c_92,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1409,plain,(
    ! [A_164,B_165,C_166] :
      ( k1_relset_1(A_164,B_165,C_166) = k1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1432,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_1409])).

tff(c_1979,plain,(
    ! [B_199,A_200,C_201] :
      ( k1_xboole_0 = B_199
      | k1_relset_1(A_200,B_199,C_201) = A_200
      | ~ v1_funct_2(C_201,A_200,B_199)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_200,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1995,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_1979])).

tff(c_2012,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1432,c_1995])).

tff(c_2014,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2012])).

tff(c_42,plain,(
    ! [A_23] :
      ( k2_relat_1(k2_funct_1(A_23)) = k1_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1315,plain,(
    ! [A_157] :
      ( m1_subset_1(A_157,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_157),k2_relat_1(A_157))))
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_20005,plain,(
    ! [A_682] :
      ( m1_subset_1(k2_funct_1(A_682),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_682)),k1_relat_1(A_682))))
      | ~ v1_funct_1(k2_funct_1(A_682))
      | ~ v1_relat_1(k2_funct_1(A_682))
      | ~ v2_funct_1(A_682)
      | ~ v1_funct_1(A_682)
      | ~ v1_relat_1(A_682) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1315])).

tff(c_20086,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2014,c_20005])).

tff(c_20134,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_94,c_88,c_18258,c_406,c_20086])).

tff(c_20161,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),'#skF_4')))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_20134])).

tff(c_20179,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_94,c_88,c_1531,c_20161])).

tff(c_20181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_523,c_20179])).

tff(c_20182,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2012])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20226,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20182,c_12])).

tff(c_18,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20224,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20182,c_20182,c_18])).

tff(c_538,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_2'(A_94,B_95),A_94)
      | r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_543,plain,(
    ! [A_96,B_97] :
      ( ~ v1_xboole_0(A_96)
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_538,c_2])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_537,plain,(
    ~ r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_523])).

tff(c_547,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_543,c_537])).

tff(c_826,plain,(
    ! [A_133] :
      ( k4_relat_1(A_133) = k2_funct_1(A_133)
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_829,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_826])).

tff(c_832,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_94,c_829])).

tff(c_848,plain,
    ( v1_xboole_0(k2_funct_1('#skF_6'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_32])).

tff(c_852,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_848])).

tff(c_78,plain,(
    ! [A_43] :
      ( m1_subset_1(A_43,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_43),k2_relat_1(A_43))))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1538,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_78])).

tff(c_1563,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_94,c_1538])).

tff(c_22,plain,(
    ! [B_15,A_13] :
      ( v1_xboole_0(B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_13))
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1581,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_1563,c_22])).

tff(c_1595,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_852,c_1581])).

tff(c_20368,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20224,c_1595])).

tff(c_20375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20226,c_20368])).

tff(c_20376,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_20377,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_21227,plain,(
    ! [A_760,B_761,C_762] :
      ( k1_relset_1(A_760,B_761,C_762) = k1_relat_1(C_762)
      | ~ m1_subset_1(C_762,k1_zfmisc_1(k2_zfmisc_1(A_760,B_761))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_21248,plain,(
    k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_20377,c_21227])).

tff(c_21720,plain,(
    ! [B_785,C_786,A_787] :
      ( k1_xboole_0 = B_785
      | v1_funct_2(C_786,A_787,B_785)
      | k1_relset_1(A_787,B_785,C_786) != A_787
      | ~ m1_subset_1(C_786,k1_zfmisc_1(k2_zfmisc_1(A_787,B_785))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_21732,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_20377,c_21720])).

tff(c_21753,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21248,c_21732])).

tff(c_21754,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_20376,c_21753])).

tff(c_21759,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_21754])).

tff(c_21762,plain,
    ( k2_relat_1('#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_21759])).

tff(c_21765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20410,c_94,c_88,c_21283,c_21762])).

tff(c_21766,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_21754])).

tff(c_21808,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21766,c_12])).

tff(c_21810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20804,c_21808])).

tff(c_21812,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_20770])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_21832,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_21812,c_14])).

tff(c_20,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20526,plain,(
    ! [A_716,B_717] : m1_subset_1('#skF_3'(A_716,B_717),k1_zfmisc_1(k2_zfmisc_1(A_716,B_717))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_20656,plain,(
    ! [B_727] : m1_subset_1('#skF_3'(k1_xboole_0,B_727),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_20526])).

tff(c_20659,plain,(
    ! [B_727] :
      ( v1_xboole_0('#skF_3'(k1_xboole_0,B_727))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20656,c_22])).

tff(c_20676,plain,(
    ! [B_728] : v1_xboole_0('#skF_3'(k1_xboole_0,B_728)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20659])).

tff(c_20707,plain,(
    ! [B_729] : '#skF_3'(k1_xboole_0,B_729) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20676,c_14])).

tff(c_66,plain,(
    ! [A_40,B_41] : v1_funct_2('#skF_3'(A_40,B_41),A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_20718,plain,(
    ! [B_729] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_729) ),
    inference(superposition,[status(thm),theory(equality)],[c_20707,c_66])).

tff(c_21835,plain,(
    ! [B_729] : v1_funct_2('#skF_6','#skF_6',B_729) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21832,c_21832,c_20718])).

tff(c_151,plain,(
    ! [A_60] :
      ( v1_xboole_0(k2_relat_1(A_60))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_158,plain,(
    ! [A_60] :
      ( k2_relat_1(A_60) = k1_xboole_0
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_151,c_14])).

tff(c_21831,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21812,c_158])).

tff(c_21895,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21832,c_21831])).

tff(c_22538,plain,(
    ! [A_818,B_819,C_820] :
      ( k2_relset_1(A_818,B_819,C_820) = k2_relat_1(C_820)
      | ~ m1_subset_1(C_820,k1_zfmisc_1(k2_zfmisc_1(A_818,B_819))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_22560,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_22538])).

tff(c_22567,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21895,c_86,c_22560])).

tff(c_139,plain,(
    ! [A_54] :
      ( v1_xboole_0(k4_relat_1(A_54))
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_146,plain,(
    ! [A_54] :
      ( k4_relat_1(A_54) = k1_xboole_0
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_139,c_14])).

tff(c_21830,plain,(
    k4_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21812,c_146])).

tff(c_21920,plain,(
    k4_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21832,c_21830])).

tff(c_21921,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21920,c_20754])).

tff(c_21945,plain,(
    ~ v1_funct_2('#skF_6','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21921,c_20376])).

tff(c_22572,plain,(
    ~ v1_funct_2('#skF_6','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22567,c_21945])).

tff(c_22583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21835,c_22572])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:27:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.16/3.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.16/3.82  
% 10.16/3.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.16/3.83  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 10.16/3.83  
% 10.16/3.83  %Foreground sorts:
% 10.16/3.83  
% 10.16/3.83  
% 10.16/3.83  %Background operators:
% 10.16/3.83  
% 10.16/3.83  
% 10.16/3.83  %Foreground operators:
% 10.16/3.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.16/3.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.16/3.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.16/3.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.16/3.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.16/3.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.16/3.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.16/3.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.16/3.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.16/3.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.16/3.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.16/3.83  tff('#skF_5', type, '#skF_5': $i).
% 10.16/3.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.16/3.83  tff('#skF_6', type, '#skF_6': $i).
% 10.16/3.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.16/3.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.16/3.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.16/3.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.16/3.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.16/3.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.16/3.83  tff('#skF_4', type, '#skF_4': $i).
% 10.16/3.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.16/3.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.16/3.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.16/3.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.16/3.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.16/3.83  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 10.16/3.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.16/3.83  
% 10.16/3.85  tff(f_177, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 10.16/3.85  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.16/3.85  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 10.16/3.85  tff(f_70, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 10.16/3.85  tff(f_111, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 10.16/3.85  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.16/3.85  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 10.16/3.85  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.16/3.85  tff(f_160, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 10.16/3.85  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.16/3.85  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.16/3.85  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.16/3.85  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.16/3.85  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.16/3.85  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.16/3.85  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.16/3.85  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.16/3.85  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.16/3.85  tff(f_150, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 10.16/3.85  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 10.16/3.85  tff(c_90, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 10.16/3.85  tff(c_20393, plain, (![C_695, A_696, B_697]: (v1_relat_1(C_695) | ~m1_subset_1(C_695, k1_zfmisc_1(k2_zfmisc_1(A_696, B_697))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.16/3.85  tff(c_20410, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_90, c_20393])).
% 10.16/3.85  tff(c_94, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_177])).
% 10.16/3.85  tff(c_88, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_177])).
% 10.16/3.85  tff(c_20748, plain, (![A_732]: (k4_relat_1(A_732)=k2_funct_1(A_732) | ~v2_funct_1(A_732) | ~v1_funct_1(A_732) | ~v1_relat_1(A_732))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.16/3.85  tff(c_20751, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_88, c_20748])).
% 10.16/3.85  tff(c_20754, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20410, c_94, c_20751])).
% 10.16/3.85  tff(c_32, plain, (![A_19]: (v1_xboole_0(k4_relat_1(A_19)) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.16/3.85  tff(c_20770, plain, (v1_xboole_0(k2_funct_1('#skF_6')) | ~v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_20754, c_32])).
% 10.16/3.85  tff(c_20776, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_20770])).
% 10.16/3.85  tff(c_20779, plain, (![C_733, A_734, B_735]: (v1_xboole_0(C_733) | ~m1_subset_1(C_733, k1_zfmisc_1(k2_zfmisc_1(A_734, B_735))) | ~v1_xboole_0(A_734))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.16/3.85  tff(c_20792, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_90, c_20779])).
% 10.16/3.85  tff(c_20804, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_20776, c_20792])).
% 10.16/3.85  tff(c_86, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_177])).
% 10.16/3.85  tff(c_21259, plain, (![A_763, B_764, C_765]: (k2_relset_1(A_763, B_764, C_765)=k2_relat_1(C_765) | ~m1_subset_1(C_765, k1_zfmisc_1(k2_zfmisc_1(A_763, B_764))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.16/3.85  tff(c_21272, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_90, c_21259])).
% 10.16/3.85  tff(c_21283, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_21272])).
% 10.16/3.85  tff(c_44, plain, (![A_23]: (k1_relat_1(k2_funct_1(A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.16/3.85  tff(c_364, plain, (![A_72]: (v1_funct_1(k2_funct_1(A_72)) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.16/3.85  tff(c_84, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 10.16/3.85  tff(c_249, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_84])).
% 10.16/3.85  tff(c_367, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_364, c_249])).
% 10.16/3.85  tff(c_370, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_367])).
% 10.16/3.85  tff(c_388, plain, (![C_82, A_83, B_84]: (v1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.16/3.85  tff(c_395, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_90, c_388])).
% 10.16/3.85  tff(c_404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_395])).
% 10.16/3.85  tff(c_405, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_84])).
% 10.16/3.85  tff(c_523, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_405])).
% 10.16/3.85  tff(c_567, plain, (![C_102, A_103, B_104]: (v1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.16/3.85  tff(c_580, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_90, c_567])).
% 10.16/3.85  tff(c_1507, plain, (![A_171, B_172, C_173]: (k2_relset_1(A_171, B_172, C_173)=k2_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.16/3.85  tff(c_1520, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_90, c_1507])).
% 10.16/3.85  tff(c_1531, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1520])).
% 10.16/3.85  tff(c_40, plain, (![A_22]: (v1_relat_1(k2_funct_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.16/3.85  tff(c_406, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_84])).
% 10.16/3.85  tff(c_1116, plain, (![A_150]: (k1_relat_1(k2_funct_1(A_150))=k2_relat_1(A_150) | ~v2_funct_1(A_150) | ~v1_funct_1(A_150) | ~v1_relat_1(A_150))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.16/3.85  tff(c_80, plain, (![A_43]: (v1_funct_2(A_43, k1_relat_1(A_43), k2_relat_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.16/3.85  tff(c_18136, plain, (![A_636]: (v1_funct_2(k2_funct_1(A_636), k2_relat_1(A_636), k2_relat_1(k2_funct_1(A_636))) | ~v1_funct_1(k2_funct_1(A_636)) | ~v1_relat_1(k2_funct_1(A_636)) | ~v2_funct_1(A_636) | ~v1_funct_1(A_636) | ~v1_relat_1(A_636))), inference(superposition, [status(thm), theory('equality')], [c_1116, c_80])).
% 10.16/3.85  tff(c_18190, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1531, c_18136])).
% 10.16/3.85  tff(c_18244, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_94, c_88, c_406, c_18190])).
% 10.16/3.85  tff(c_18249, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_18244])).
% 10.16/3.85  tff(c_18252, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_18249])).
% 10.16/3.85  tff(c_18256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_580, c_94, c_18252])).
% 10.16/3.85  tff(c_18258, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_18244])).
% 10.16/3.85  tff(c_92, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 10.16/3.85  tff(c_1409, plain, (![A_164, B_165, C_166]: (k1_relset_1(A_164, B_165, C_166)=k1_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.16/3.85  tff(c_1432, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_90, c_1409])).
% 10.16/3.85  tff(c_1979, plain, (![B_199, A_200, C_201]: (k1_xboole_0=B_199 | k1_relset_1(A_200, B_199, C_201)=A_200 | ~v1_funct_2(C_201, A_200, B_199) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_200, B_199))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.16/3.85  tff(c_1995, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_90, c_1979])).
% 10.16/3.85  tff(c_2012, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1432, c_1995])).
% 10.16/3.85  tff(c_2014, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2012])).
% 10.16/3.85  tff(c_42, plain, (![A_23]: (k2_relat_1(k2_funct_1(A_23))=k1_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.16/3.85  tff(c_1315, plain, (![A_157]: (m1_subset_1(A_157, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_157), k2_relat_1(A_157)))) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.16/3.85  tff(c_20005, plain, (![A_682]: (m1_subset_1(k2_funct_1(A_682), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_682)), k1_relat_1(A_682)))) | ~v1_funct_1(k2_funct_1(A_682)) | ~v1_relat_1(k2_funct_1(A_682)) | ~v2_funct_1(A_682) | ~v1_funct_1(A_682) | ~v1_relat_1(A_682))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1315])).
% 10.16/3.85  tff(c_20086, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2014, c_20005])).
% 10.16/3.85  tff(c_20134, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_94, c_88, c_18258, c_406, c_20086])).
% 10.16/3.85  tff(c_20161, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), '#skF_4'))) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_44, c_20134])).
% 10.16/3.85  tff(c_20179, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_94, c_88, c_1531, c_20161])).
% 10.16/3.85  tff(c_20181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_523, c_20179])).
% 10.16/3.85  tff(c_20182, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2012])).
% 10.16/3.85  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.16/3.85  tff(c_20226, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20182, c_12])).
% 10.16/3.85  tff(c_18, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.16/3.85  tff(c_20224, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20182, c_20182, c_18])).
% 10.16/3.85  tff(c_538, plain, (![A_94, B_95]: (r2_hidden('#skF_2'(A_94, B_95), A_94) | r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.16/3.85  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.16/3.85  tff(c_543, plain, (![A_96, B_97]: (~v1_xboole_0(A_96) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_538, c_2])).
% 10.16/3.85  tff(c_26, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.16/3.85  tff(c_537, plain, (~r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_523])).
% 10.16/3.85  tff(c_547, plain, (~v1_xboole_0(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_543, c_537])).
% 10.16/3.85  tff(c_826, plain, (![A_133]: (k4_relat_1(A_133)=k2_funct_1(A_133) | ~v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.16/3.85  tff(c_829, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_88, c_826])).
% 10.16/3.85  tff(c_832, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_580, c_94, c_829])).
% 10.16/3.85  tff(c_848, plain, (v1_xboole_0(k2_funct_1('#skF_6')) | ~v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_832, c_32])).
% 10.16/3.85  tff(c_852, plain, (~v1_xboole_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_547, c_848])).
% 10.16/3.85  tff(c_78, plain, (![A_43]: (m1_subset_1(A_43, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_43), k2_relat_1(A_43)))) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.16/3.85  tff(c_1538, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1531, c_78])).
% 10.16/3.85  tff(c_1563, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_94, c_1538])).
% 10.16/3.85  tff(c_22, plain, (![B_15, A_13]: (v1_xboole_0(B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_13)) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.16/3.85  tff(c_1581, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_1563, c_22])).
% 10.16/3.85  tff(c_1595, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_852, c_1581])).
% 10.16/3.85  tff(c_20368, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20224, c_1595])).
% 10.16/3.85  tff(c_20375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20226, c_20368])).
% 10.16/3.85  tff(c_20376, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_405])).
% 10.16/3.85  tff(c_20377, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_405])).
% 10.16/3.85  tff(c_21227, plain, (![A_760, B_761, C_762]: (k1_relset_1(A_760, B_761, C_762)=k1_relat_1(C_762) | ~m1_subset_1(C_762, k1_zfmisc_1(k2_zfmisc_1(A_760, B_761))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.16/3.85  tff(c_21248, plain, (k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_20377, c_21227])).
% 10.16/3.85  tff(c_21720, plain, (![B_785, C_786, A_787]: (k1_xboole_0=B_785 | v1_funct_2(C_786, A_787, B_785) | k1_relset_1(A_787, B_785, C_786)!=A_787 | ~m1_subset_1(C_786, k1_zfmisc_1(k2_zfmisc_1(A_787, B_785))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.16/3.85  tff(c_21732, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))!='#skF_5'), inference(resolution, [status(thm)], [c_20377, c_21720])).
% 10.16/3.85  tff(c_21753, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_21248, c_21732])).
% 10.16/3.85  tff(c_21754, plain, (k1_xboole_0='#skF_4' | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_20376, c_21753])).
% 10.16/3.85  tff(c_21759, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_21754])).
% 10.16/3.85  tff(c_21762, plain, (k2_relat_1('#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_44, c_21759])).
% 10.16/3.85  tff(c_21765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20410, c_94, c_88, c_21283, c_21762])).
% 10.16/3.85  tff(c_21766, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_21754])).
% 10.16/3.85  tff(c_21808, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21766, c_12])).
% 10.16/3.85  tff(c_21810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20804, c_21808])).
% 10.16/3.85  tff(c_21812, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_20770])).
% 10.16/3.85  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.16/3.85  tff(c_21832, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_21812, c_14])).
% 10.16/3.85  tff(c_20, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.16/3.85  tff(c_20526, plain, (![A_716, B_717]: (m1_subset_1('#skF_3'(A_716, B_717), k1_zfmisc_1(k2_zfmisc_1(A_716, B_717))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 10.16/3.85  tff(c_20656, plain, (![B_727]: (m1_subset_1('#skF_3'(k1_xboole_0, B_727), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_20526])).
% 10.16/3.85  tff(c_20659, plain, (![B_727]: (v1_xboole_0('#skF_3'(k1_xboole_0, B_727)) | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_20656, c_22])).
% 10.16/3.85  tff(c_20676, plain, (![B_728]: (v1_xboole_0('#skF_3'(k1_xboole_0, B_728)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20659])).
% 10.16/3.85  tff(c_20707, plain, (![B_729]: ('#skF_3'(k1_xboole_0, B_729)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20676, c_14])).
% 10.16/3.85  tff(c_66, plain, (![A_40, B_41]: (v1_funct_2('#skF_3'(A_40, B_41), A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_150])).
% 10.16/3.85  tff(c_20718, plain, (![B_729]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_729))), inference(superposition, [status(thm), theory('equality')], [c_20707, c_66])).
% 10.16/3.85  tff(c_21835, plain, (![B_729]: (v1_funct_2('#skF_6', '#skF_6', B_729))), inference(demodulation, [status(thm), theory('equality')], [c_21832, c_21832, c_20718])).
% 10.16/3.85  tff(c_151, plain, (![A_60]: (v1_xboole_0(k2_relat_1(A_60)) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.16/3.85  tff(c_158, plain, (![A_60]: (k2_relat_1(A_60)=k1_xboole_0 | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_151, c_14])).
% 10.16/3.85  tff(c_21831, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_21812, c_158])).
% 10.16/3.85  tff(c_21895, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_21832, c_21831])).
% 10.16/3.85  tff(c_22538, plain, (![A_818, B_819, C_820]: (k2_relset_1(A_818, B_819, C_820)=k2_relat_1(C_820) | ~m1_subset_1(C_820, k1_zfmisc_1(k2_zfmisc_1(A_818, B_819))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.16/3.85  tff(c_22560, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_90, c_22538])).
% 10.16/3.85  tff(c_22567, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_21895, c_86, c_22560])).
% 10.16/3.85  tff(c_139, plain, (![A_54]: (v1_xboole_0(k4_relat_1(A_54)) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.16/3.85  tff(c_146, plain, (![A_54]: (k4_relat_1(A_54)=k1_xboole_0 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_139, c_14])).
% 10.16/3.85  tff(c_21830, plain, (k4_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_21812, c_146])).
% 10.16/3.85  tff(c_21920, plain, (k4_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_21832, c_21830])).
% 10.16/3.85  tff(c_21921, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_21920, c_20754])).
% 10.16/3.85  tff(c_21945, plain, (~v1_funct_2('#skF_6', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21921, c_20376])).
% 10.16/3.85  tff(c_22572, plain, (~v1_funct_2('#skF_6', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22567, c_21945])).
% 10.16/3.85  tff(c_22583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21835, c_22572])).
% 10.16/3.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.16/3.85  
% 10.16/3.85  Inference rules
% 10.16/3.85  ----------------------
% 10.16/3.85  #Ref     : 0
% 10.16/3.85  #Sup     : 5387
% 10.16/3.85  #Fact    : 0
% 10.16/3.85  #Define  : 0
% 10.16/3.85  #Split   : 11
% 10.16/3.85  #Chain   : 0
% 10.16/3.85  #Close   : 0
% 10.16/3.85  
% 10.16/3.85  Ordering : KBO
% 10.16/3.85  
% 10.16/3.85  Simplification rules
% 10.16/3.85  ----------------------
% 10.16/3.85  #Subsume      : 595
% 10.16/3.85  #Demod        : 7083
% 10.16/3.85  #Tautology    : 3683
% 10.16/3.85  #SimpNegUnit  : 21
% 10.16/3.85  #BackRed      : 151
% 10.16/3.85  
% 10.16/3.85  #Partial instantiations: 0
% 10.16/3.85  #Strategies tried      : 1
% 10.16/3.85  
% 10.16/3.85  Timing (in seconds)
% 10.16/3.85  ----------------------
% 10.16/3.85  Preprocessing        : 0.36
% 10.16/3.85  Parsing              : 0.19
% 10.16/3.85  CNF conversion       : 0.02
% 10.16/3.85  Main loop            : 2.68
% 10.16/3.85  Inferencing          : 0.73
% 10.16/3.85  Reduction            : 1.00
% 10.16/3.85  Demodulation         : 0.76
% 10.16/3.85  BG Simplification    : 0.09
% 10.16/3.85  Subsumption          : 0.69
% 10.16/3.85  Abstraction          : 0.12
% 10.16/3.85  MUC search           : 0.00
% 10.16/3.85  Cooper               : 0.00
% 10.16/3.85  Total                : 3.08
% 10.16/3.85  Index Insertion      : 0.00
% 10.16/3.85  Index Deletion       : 0.00
% 10.16/3.85  Index Matching       : 0.00
% 10.16/3.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
