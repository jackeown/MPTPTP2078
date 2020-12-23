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
% DateTime   : Thu Dec  3 10:11:36 EST 2020

% Result     : Theorem 6.65s
% Output     : CNFRefutation 6.65s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 610 expanded)
%              Number of leaves         :   42 ( 222 expanded)
%              Depth                    :   11
%              Number of atoms          :  184 (1603 expanded)
%              Number of equality atoms :   56 ( 299 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_163,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_142,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_3718,plain,(
    ! [A_491,B_492,C_493,D_494] :
      ( r2_hidden('#skF_5'(A_491,B_492,C_493,D_494),C_493)
      | ~ r2_hidden(A_491,D_494)
      | ~ m1_subset_1(D_494,k1_zfmisc_1(k2_zfmisc_1(B_492,C_493))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3785,plain,(
    ! [A_503] :
      ( r2_hidden('#skF_5'(A_503,'#skF_6','#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_503,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_80,c_3718])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3796,plain,(
    ! [A_503] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_503,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3785,c_2])).

tff(c_3815,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3796])).

tff(c_3575,plain,(
    ! [A_473,B_474,D_475] :
      ( r2_relset_1(A_473,B_474,D_475,D_475)
      | ~ m1_subset_1(D_475,k1_zfmisc_1(k2_zfmisc_1(A_473,B_474))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3591,plain,(
    r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_3575])).

tff(c_74,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_134,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_150,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_134])).

tff(c_78,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_76,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_3682,plain,(
    ! [A_486,B_487,C_488] :
      ( k1_relset_1(A_486,B_487,C_488) = k1_relat_1(C_488)
      | ~ m1_subset_1(C_488,k1_zfmisc_1(k2_zfmisc_1(A_486,B_487))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3700,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_3682])).

tff(c_4341,plain,(
    ! [B_570,A_571,C_572] :
      ( k1_xboole_0 = B_570
      | k1_relset_1(A_571,B_570,C_572) = A_571
      | ~ v1_funct_2(C_572,A_571,B_570)
      | ~ m1_subset_1(C_572,k1_zfmisc_1(k2_zfmisc_1(A_571,B_570))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4347,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_4341])).

tff(c_4363,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3700,c_4347])).

tff(c_4428,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4363])).

tff(c_149,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_134])).

tff(c_84,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_82,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_3699,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_3682])).

tff(c_4344,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_4341])).

tff(c_4360,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3699,c_4344])).

tff(c_4367,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4360])).

tff(c_4619,plain,(
    ! [A_583,B_584] :
      ( r2_hidden('#skF_3'(A_583,B_584),k1_relat_1(A_583))
      | B_584 = A_583
      | k1_relat_1(B_584) != k1_relat_1(A_583)
      | ~ v1_funct_1(B_584)
      | ~ v1_relat_1(B_584)
      | ~ v1_funct_1(A_583)
      | ~ v1_relat_1(A_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4635,plain,(
    ! [B_584] :
      ( r2_hidden('#skF_3'('#skF_8',B_584),'#skF_6')
      | B_584 = '#skF_8'
      | k1_relat_1(B_584) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_584)
      | ~ v1_relat_1(B_584)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4367,c_4619])).

tff(c_5829,plain,(
    ! [B_654] :
      ( r2_hidden('#skF_3'('#skF_8',B_654),'#skF_6')
      | B_654 = '#skF_8'
      | k1_relat_1(B_654) != '#skF_6'
      | ~ v1_funct_1(B_654)
      | ~ v1_relat_1(B_654) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_84,c_4367,c_4635])).

tff(c_72,plain,(
    ! [E_55] :
      ( k1_funct_1('#skF_9',E_55) = k1_funct_1('#skF_8',E_55)
      | ~ r2_hidden(E_55,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_6047,plain,(
    ! [B_672] :
      ( k1_funct_1('#skF_9','#skF_3'('#skF_8',B_672)) = k1_funct_1('#skF_8','#skF_3'('#skF_8',B_672))
      | B_672 = '#skF_8'
      | k1_relat_1(B_672) != '#skF_6'
      | ~ v1_funct_1(B_672)
      | ~ v1_relat_1(B_672) ) ),
    inference(resolution,[status(thm)],[c_5829,c_72])).

tff(c_34,plain,(
    ! [B_25,A_21] :
      ( k1_funct_1(B_25,'#skF_3'(A_21,B_25)) != k1_funct_1(A_21,'#skF_3'(A_21,B_25))
      | B_25 = A_21
      | k1_relat_1(B_25) != k1_relat_1(A_21)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6054,plain,
    ( k1_relat_1('#skF_9') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_9' = '#skF_8'
    | k1_relat_1('#skF_9') != '#skF_6'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_6047,c_34])).

tff(c_6061,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_78,c_4428,c_149,c_84,c_4367,c_4428,c_6054])).

tff(c_70,plain,(
    ~ r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_6098,plain,(
    ~ r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6061,c_70])).

tff(c_6110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3591,c_6098])).

tff(c_6111,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4363])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_122,plain,(
    ! [B_64,A_65] :
      ( ~ r1_tarski(B_64,A_65)
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_128,plain,(
    ! [A_67] :
      ( ~ r1_tarski(A_67,'#skF_1'(A_67))
      | v1_xboole_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_4,c_122])).

tff(c_133,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_128])).

tff(c_6153,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6111,c_133])).

tff(c_6160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3815,c_6153])).

tff(c_6161,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4360])).

tff(c_6202,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6161,c_133])).

tff(c_6209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3815,c_6202])).

tff(c_6252,plain,(
    ! [A_675] : ~ r2_hidden(A_675,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_3796])).

tff(c_6267,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_6252])).

tff(c_6211,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_3796])).

tff(c_188,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_2'(A_76,B_77),A_76)
      | r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_202,plain,(
    ! [A_78,B_79] :
      ( ~ v1_xboole_0(A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_188,c_2])).

tff(c_165,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_174,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_165])).

tff(c_213,plain,(
    ! [A_78] :
      ( k1_xboole_0 = A_78
      | ~ v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_202,c_174])).

tff(c_6218,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6211,c_213])).

tff(c_6475,plain,(
    ! [A_689] :
      ( A_689 = '#skF_7'
      | ~ v1_xboole_0(A_689) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6218,c_213])).

tff(c_6486,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6267,c_6475])).

tff(c_26,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3593,plain,(
    ! [A_473,B_474] : r2_relset_1(A_473,B_474,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_3575])).

tff(c_6227,plain,(
    ! [A_473,B_474] : r2_relset_1(A_473,B_474,'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6218,c_6218,c_3593])).

tff(c_6758,plain,(
    ! [A_473,B_474] : r2_relset_1(A_473,B_474,'#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6486,c_6486,c_6227])).

tff(c_6271,plain,(
    ! [A_676] :
      ( r2_hidden('#skF_5'(A_676,'#skF_6','#skF_7','#skF_9'),'#skF_7')
      | ~ r2_hidden(A_676,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_74,c_3718])).

tff(c_6279,plain,(
    ! [A_676] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_676,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6271,c_2])).

tff(c_6285,plain,(
    ! [A_677] : ~ r2_hidden(A_677,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6211,c_6279])).

tff(c_6300,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_6285])).

tff(c_6485,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6300,c_6475])).

tff(c_6518,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6486,c_6485])).

tff(c_6507,plain,(
    ~ r2_relset_1('#skF_6','#skF_9','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_70])).

tff(c_6792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6758,c_6518,c_6518,c_6507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:11:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.65/2.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.38  
% 6.65/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.38  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2
% 6.65/2.38  
% 6.65/2.38  %Foreground sorts:
% 6.65/2.38  
% 6.65/2.38  
% 6.65/2.38  %Background operators:
% 6.65/2.38  
% 6.65/2.38  
% 6.65/2.38  %Foreground operators:
% 6.65/2.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.65/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.65/2.38  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.65/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.65/2.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.65/2.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.65/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.65/2.38  tff('#skF_7', type, '#skF_7': $i).
% 6.65/2.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.65/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.65/2.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.65/2.38  tff('#skF_6', type, '#skF_6': $i).
% 6.65/2.38  tff('#skF_9', type, '#skF_9': $i).
% 6.65/2.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.65/2.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.65/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.65/2.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.65/2.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.65/2.38  tff('#skF_8', type, '#skF_8': $i).
% 6.65/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.65/2.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.65/2.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.65/2.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.65/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.65/2.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.65/2.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.65/2.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.65/2.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.65/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.65/2.38  
% 6.65/2.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.65/2.40  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 6.65/2.40  tff(f_124, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 6.65/2.40  tff(f_111, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.65/2.40  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.65/2.40  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.65/2.40  tff(f_142, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.65/2.40  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 6.65/2.40  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.65/2.40  tff(f_89, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.65/2.40  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.65/2.40  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.65/2.40  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.65/2.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.65/2.40  tff(c_80, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.65/2.40  tff(c_3718, plain, (![A_491, B_492, C_493, D_494]: (r2_hidden('#skF_5'(A_491, B_492, C_493, D_494), C_493) | ~r2_hidden(A_491, D_494) | ~m1_subset_1(D_494, k1_zfmisc_1(k2_zfmisc_1(B_492, C_493))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.65/2.40  tff(c_3785, plain, (![A_503]: (r2_hidden('#skF_5'(A_503, '#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_503, '#skF_8'))), inference(resolution, [status(thm)], [c_80, c_3718])).
% 6.65/2.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.65/2.40  tff(c_3796, plain, (![A_503]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_503, '#skF_8'))), inference(resolution, [status(thm)], [c_3785, c_2])).
% 6.65/2.40  tff(c_3815, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_3796])).
% 6.65/2.40  tff(c_3575, plain, (![A_473, B_474, D_475]: (r2_relset_1(A_473, B_474, D_475, D_475) | ~m1_subset_1(D_475, k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.65/2.40  tff(c_3591, plain, (r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_80, c_3575])).
% 6.65/2.40  tff(c_74, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.65/2.40  tff(c_134, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.65/2.40  tff(c_150, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_134])).
% 6.65/2.40  tff(c_78, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.65/2.40  tff(c_76, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.65/2.40  tff(c_3682, plain, (![A_486, B_487, C_488]: (k1_relset_1(A_486, B_487, C_488)=k1_relat_1(C_488) | ~m1_subset_1(C_488, k1_zfmisc_1(k2_zfmisc_1(A_486, B_487))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.65/2.40  tff(c_3700, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_3682])).
% 6.65/2.40  tff(c_4341, plain, (![B_570, A_571, C_572]: (k1_xboole_0=B_570 | k1_relset_1(A_571, B_570, C_572)=A_571 | ~v1_funct_2(C_572, A_571, B_570) | ~m1_subset_1(C_572, k1_zfmisc_1(k2_zfmisc_1(A_571, B_570))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.65/2.40  tff(c_4347, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_4341])).
% 6.65/2.40  tff(c_4363, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3700, c_4347])).
% 6.65/2.40  tff(c_4428, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_4363])).
% 6.65/2.40  tff(c_149, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_80, c_134])).
% 6.65/2.40  tff(c_84, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.65/2.40  tff(c_82, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.65/2.40  tff(c_3699, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_80, c_3682])).
% 6.65/2.40  tff(c_4344, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_80, c_4341])).
% 6.65/2.40  tff(c_4360, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3699, c_4344])).
% 6.65/2.40  tff(c_4367, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_4360])).
% 6.65/2.40  tff(c_4619, plain, (![A_583, B_584]: (r2_hidden('#skF_3'(A_583, B_584), k1_relat_1(A_583)) | B_584=A_583 | k1_relat_1(B_584)!=k1_relat_1(A_583) | ~v1_funct_1(B_584) | ~v1_relat_1(B_584) | ~v1_funct_1(A_583) | ~v1_relat_1(A_583))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.65/2.40  tff(c_4635, plain, (![B_584]: (r2_hidden('#skF_3'('#skF_8', B_584), '#skF_6') | B_584='#skF_8' | k1_relat_1(B_584)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_584) | ~v1_relat_1(B_584) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4367, c_4619])).
% 6.65/2.40  tff(c_5829, plain, (![B_654]: (r2_hidden('#skF_3'('#skF_8', B_654), '#skF_6') | B_654='#skF_8' | k1_relat_1(B_654)!='#skF_6' | ~v1_funct_1(B_654) | ~v1_relat_1(B_654))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_84, c_4367, c_4635])).
% 6.65/2.40  tff(c_72, plain, (![E_55]: (k1_funct_1('#skF_9', E_55)=k1_funct_1('#skF_8', E_55) | ~r2_hidden(E_55, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.65/2.40  tff(c_6047, plain, (![B_672]: (k1_funct_1('#skF_9', '#skF_3'('#skF_8', B_672))=k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_672)) | B_672='#skF_8' | k1_relat_1(B_672)!='#skF_6' | ~v1_funct_1(B_672) | ~v1_relat_1(B_672))), inference(resolution, [status(thm)], [c_5829, c_72])).
% 6.65/2.40  tff(c_34, plain, (![B_25, A_21]: (k1_funct_1(B_25, '#skF_3'(A_21, B_25))!=k1_funct_1(A_21, '#skF_3'(A_21, B_25)) | B_25=A_21 | k1_relat_1(B_25)!=k1_relat_1(A_21) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.65/2.40  tff(c_6054, plain, (k1_relat_1('#skF_9')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_9'='#skF_8' | k1_relat_1('#skF_9')!='#skF_6' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_6047, c_34])).
% 6.65/2.40  tff(c_6061, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_78, c_4428, c_149, c_84, c_4367, c_4428, c_6054])).
% 6.65/2.40  tff(c_70, plain, (~r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.65/2.40  tff(c_6098, plain, (~r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6061, c_70])).
% 6.65/2.40  tff(c_6110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3591, c_6098])).
% 6.65/2.40  tff(c_6111, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_4363])).
% 6.65/2.40  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.65/2.40  tff(c_122, plain, (![B_64, A_65]: (~r1_tarski(B_64, A_65) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.65/2.40  tff(c_128, plain, (![A_67]: (~r1_tarski(A_67, '#skF_1'(A_67)) | v1_xboole_0(A_67))), inference(resolution, [status(thm)], [c_4, c_122])).
% 6.65/2.40  tff(c_133, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_128])).
% 6.65/2.40  tff(c_6153, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6111, c_133])).
% 6.65/2.40  tff(c_6160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3815, c_6153])).
% 6.65/2.40  tff(c_6161, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_4360])).
% 6.65/2.40  tff(c_6202, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6161, c_133])).
% 6.65/2.40  tff(c_6209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3815, c_6202])).
% 6.65/2.40  tff(c_6252, plain, (![A_675]: (~r2_hidden(A_675, '#skF_8'))), inference(splitRight, [status(thm)], [c_3796])).
% 6.65/2.40  tff(c_6267, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_6252])).
% 6.65/2.40  tff(c_6211, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_3796])).
% 6.65/2.40  tff(c_188, plain, (![A_76, B_77]: (r2_hidden('#skF_2'(A_76, B_77), A_76) | r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.65/2.40  tff(c_202, plain, (![A_78, B_79]: (~v1_xboole_0(A_78) | r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_188, c_2])).
% 6.65/2.40  tff(c_165, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.65/2.40  tff(c_174, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_165])).
% 6.65/2.40  tff(c_213, plain, (![A_78]: (k1_xboole_0=A_78 | ~v1_xboole_0(A_78))), inference(resolution, [status(thm)], [c_202, c_174])).
% 6.65/2.40  tff(c_6218, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_6211, c_213])).
% 6.65/2.40  tff(c_6475, plain, (![A_689]: (A_689='#skF_7' | ~v1_xboole_0(A_689))), inference(demodulation, [status(thm), theory('equality')], [c_6218, c_213])).
% 6.65/2.40  tff(c_6486, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_6267, c_6475])).
% 6.65/2.40  tff(c_26, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.65/2.40  tff(c_3593, plain, (![A_473, B_474]: (r2_relset_1(A_473, B_474, k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_3575])).
% 6.65/2.40  tff(c_6227, plain, (![A_473, B_474]: (r2_relset_1(A_473, B_474, '#skF_7', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6218, c_6218, c_3593])).
% 6.65/2.40  tff(c_6758, plain, (![A_473, B_474]: (r2_relset_1(A_473, B_474, '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_6486, c_6486, c_6227])).
% 6.65/2.40  tff(c_6271, plain, (![A_676]: (r2_hidden('#skF_5'(A_676, '#skF_6', '#skF_7', '#skF_9'), '#skF_7') | ~r2_hidden(A_676, '#skF_9'))), inference(resolution, [status(thm)], [c_74, c_3718])).
% 6.65/2.40  tff(c_6279, plain, (![A_676]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_676, '#skF_9'))), inference(resolution, [status(thm)], [c_6271, c_2])).
% 6.65/2.40  tff(c_6285, plain, (![A_677]: (~r2_hidden(A_677, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_6211, c_6279])).
% 6.65/2.40  tff(c_6300, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_6285])).
% 6.65/2.40  tff(c_6485, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_6300, c_6475])).
% 6.65/2.40  tff(c_6518, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6486, c_6485])).
% 6.65/2.40  tff(c_6507, plain, (~r2_relset_1('#skF_6', '#skF_9', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_70])).
% 6.65/2.40  tff(c_6792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6758, c_6518, c_6518, c_6507])).
% 6.65/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.65/2.40  
% 6.65/2.40  Inference rules
% 6.65/2.40  ----------------------
% 6.65/2.40  #Ref     : 4
% 6.65/2.40  #Sup     : 1277
% 6.65/2.40  #Fact    : 0
% 6.65/2.40  #Define  : 0
% 6.65/2.40  #Split   : 21
% 6.65/2.40  #Chain   : 0
% 6.65/2.40  #Close   : 0
% 6.65/2.40  
% 6.65/2.40  Ordering : KBO
% 6.65/2.40  
% 6.65/2.40  Simplification rules
% 6.65/2.40  ----------------------
% 6.65/2.40  #Subsume      : 411
% 6.65/2.40  #Demod        : 1707
% 6.65/2.40  #Tautology    : 623
% 6.65/2.40  #SimpNegUnit  : 63
% 6.65/2.40  #BackRed      : 544
% 6.65/2.40  
% 6.65/2.40  #Partial instantiations: 0
% 6.65/2.40  #Strategies tried      : 1
% 6.65/2.40  
% 6.65/2.40  Timing (in seconds)
% 6.65/2.40  ----------------------
% 6.65/2.40  Preprocessing        : 0.37
% 6.65/2.40  Parsing              : 0.19
% 6.65/2.40  CNF conversion       : 0.03
% 6.65/2.40  Main loop            : 1.21
% 6.65/2.40  Inferencing          : 0.40
% 6.65/2.40  Reduction            : 0.41
% 6.65/2.40  Demodulation         : 0.28
% 6.65/2.40  BG Simplification    : 0.05
% 6.65/2.40  Subsumption          : 0.24
% 6.65/2.40  Abstraction          : 0.04
% 6.65/2.40  MUC search           : 0.00
% 6.65/2.40  Cooper               : 0.00
% 6.65/2.40  Total                : 1.61
% 6.65/2.40  Index Insertion      : 0.00
% 6.65/2.40  Index Deletion       : 0.00
% 6.65/2.40  Index Matching       : 0.00
% 6.65/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
