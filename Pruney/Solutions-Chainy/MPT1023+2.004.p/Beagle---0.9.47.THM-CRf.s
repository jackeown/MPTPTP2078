%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:17 EST 2020

% Result     : Theorem 11.34s
% Output     : CNFRefutation 11.44s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 255 expanded)
%              Number of leaves         :   41 ( 107 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 778 expanded)
%              Number of equality atoms :   55 ( 187 expanded)
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

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_77,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_74,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2132,plain,(
    ! [A_253,B_254,D_255] :
      ( r2_relset_1(A_253,B_254,D_255,D_255)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2150,plain,(
    r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_2132])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2989,plain,(
    ! [A_320,B_321,C_322,D_323] :
      ( r2_hidden('#skF_5'(A_320,B_321,C_322,D_323),C_322)
      | ~ r2_hidden(A_320,D_323)
      | ~ m1_subset_1(D_323,k1_zfmisc_1(k2_zfmisc_1(B_321,C_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3050,plain,(
    ! [A_326] :
      ( r2_hidden('#skF_5'(A_326,'#skF_6','#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_326,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_74,c_2989])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3061,plain,(
    ! [A_326] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_326,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3050,c_2])).

tff(c_3062,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3061])).

tff(c_68,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_128,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_145,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_128])).

tff(c_72,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_70,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2242,plain,(
    ! [A_264,B_265,C_266] :
      ( k1_relset_1(A_264,B_265,C_266) = k1_relat_1(C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2269,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_2242])).

tff(c_3531,plain,(
    ! [B_356,A_357,C_358] :
      ( k1_xboole_0 = B_356
      | k1_relset_1(A_357,B_356,C_358) = A_357
      | ~ v1_funct_2(C_358,A_357,B_356)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_357,B_356))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3550,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_3531])).

tff(c_3560,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2269,c_3550])).

tff(c_3564,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3560])).

tff(c_146,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_128])).

tff(c_78,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_76,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2270,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_2242])).

tff(c_3553,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_3531])).

tff(c_3563,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2270,c_3553])).

tff(c_3619,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3563])).

tff(c_3755,plain,(
    ! [A_365,B_366] :
      ( r2_hidden('#skF_3'(A_365,B_366),k1_relat_1(A_365))
      | B_366 = A_365
      | k1_relat_1(B_366) != k1_relat_1(A_365)
      | ~ v1_funct_1(B_366)
      | ~ v1_relat_1(B_366)
      | ~ v1_funct_1(A_365)
      | ~ v1_relat_1(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8169,plain,(
    ! [A_571,B_572] :
      ( m1_subset_1('#skF_3'(A_571,B_572),k1_relat_1(A_571))
      | B_572 = A_571
      | k1_relat_1(B_572) != k1_relat_1(A_571)
      | ~ v1_funct_1(B_572)
      | ~ v1_relat_1(B_572)
      | ~ v1_funct_1(A_571)
      | ~ v1_relat_1(A_571) ) ),
    inference(resolution,[status(thm)],[c_3755,c_20])).

tff(c_8175,plain,(
    ! [B_572] :
      ( m1_subset_1('#skF_3'('#skF_8',B_572),'#skF_6')
      | B_572 = '#skF_8'
      | k1_relat_1(B_572) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_572)
      | ~ v1_relat_1(B_572)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3619,c_8169])).

tff(c_23490,plain,(
    ! [B_896] :
      ( m1_subset_1('#skF_3'('#skF_8',B_896),'#skF_6')
      | B_896 = '#skF_8'
      | k1_relat_1(B_896) != '#skF_6'
      | ~ v1_funct_1(B_896)
      | ~ v1_relat_1(B_896) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_78,c_3619,c_8175])).

tff(c_66,plain,(
    ! [E_50] :
      ( k1_funct_1('#skF_9',E_50) = k1_funct_1('#skF_8',E_50)
      | ~ m1_subset_1(E_50,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_23724,plain,(
    ! [B_900] :
      ( k1_funct_1('#skF_9','#skF_3'('#skF_8',B_900)) = k1_funct_1('#skF_8','#skF_3'('#skF_8',B_900))
      | B_900 = '#skF_8'
      | k1_relat_1(B_900) != '#skF_6'
      | ~ v1_funct_1(B_900)
      | ~ v1_relat_1(B_900) ) ),
    inference(resolution,[status(thm)],[c_23490,c_66])).

tff(c_30,plain,(
    ! [B_22,A_18] :
      ( k1_funct_1(B_22,'#skF_3'(A_18,B_22)) != k1_funct_1(A_18,'#skF_3'(A_18,B_22))
      | B_22 = A_18
      | k1_relat_1(B_22) != k1_relat_1(A_18)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_23731,plain,
    ( k1_relat_1('#skF_9') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_9' = '#skF_8'
    | k1_relat_1('#skF_9') != '#skF_6'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_23724,c_30])).

tff(c_23738,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_72,c_3564,c_146,c_78,c_3564,c_3619,c_23731])).

tff(c_64,plain,(
    ~ r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_23786,plain,(
    ~ r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23738,c_64])).

tff(c_23799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_23786])).

tff(c_23800,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3563])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_23845,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23800,c_12])).

tff(c_23847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3062,c_23845])).

tff(c_23848,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3560])).

tff(c_23892,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23848,c_12])).

tff(c_23894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3062,c_23892])).

tff(c_23974,plain,(
    ! [A_905] : ~ r2_hidden(A_905,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_3061])).

tff(c_23989,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_23974])).

tff(c_23896,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_3061])).

tff(c_24001,plain,(
    ! [A_906] :
      ( r2_hidden('#skF_5'(A_906,'#skF_6','#skF_7','#skF_9'),'#skF_7')
      | ~ r2_hidden(A_906,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_68,c_2989])).

tff(c_24009,plain,(
    ! [A_906] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_906,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24001,c_2])).

tff(c_24015,plain,(
    ! [A_907] : ~ r2_hidden(A_907,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23896,c_24009])).

tff(c_24030,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_24015])).

tff(c_112,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_2'(A_62,B_63),A_62)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_120,plain,(
    ! [A_62,B_63] :
      ( ~ v1_xboole_0(A_62)
      | r1_tarski(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_173,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_190,plain,(
    ! [B_78,A_79] :
      ( B_78 = A_79
      | ~ r1_tarski(B_78,A_79)
      | ~ v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_120,c_173])).

tff(c_203,plain,(
    ! [B_63,A_62] :
      ( B_63 = A_62
      | ~ v1_xboole_0(B_63)
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_120,c_190])).

tff(c_24332,plain,(
    ! [A_923] :
      ( A_923 = '#skF_9'
      | ~ v1_xboole_0(A_923) ) ),
    inference(resolution,[status(thm)],[c_24030,c_203])).

tff(c_24350,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_23989,c_24332])).

tff(c_24391,plain,(
    ~ r2_relset_1('#skF_6','#skF_7','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24350,c_64])).

tff(c_24405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_24391])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.34/4.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.34/4.23  
% 11.34/4.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.44/4.24  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2
% 11.44/4.24  
% 11.44/4.24  %Foreground sorts:
% 11.44/4.24  
% 11.44/4.24  
% 11.44/4.24  %Background operators:
% 11.44/4.24  
% 11.44/4.24  
% 11.44/4.24  %Foreground operators:
% 11.44/4.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.44/4.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.44/4.24  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.44/4.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.44/4.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.44/4.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.44/4.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.44/4.24  tff('#skF_7', type, '#skF_7': $i).
% 11.44/4.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.44/4.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.44/4.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.44/4.24  tff('#skF_6', type, '#skF_6': $i).
% 11.44/4.24  tff('#skF_9', type, '#skF_9': $i).
% 11.44/4.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.44/4.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.44/4.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.44/4.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.44/4.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 11.44/4.24  tff('#skF_8', type, '#skF_8': $i).
% 11.44/4.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.44/4.24  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 11.44/4.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.44/4.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.44/4.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.44/4.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.44/4.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.44/4.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.44/4.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.44/4.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.44/4.24  
% 11.44/4.25  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 11.44/4.25  tff(f_99, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.44/4.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.44/4.25  tff(f_112, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 11.44/4.25  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.44/4.25  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.44/4.25  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.44/4.25  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 11.44/4.25  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 11.44/4.25  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.44/4.25  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.44/4.25  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.44/4.25  tff(c_74, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.44/4.25  tff(c_2132, plain, (![A_253, B_254, D_255]: (r2_relset_1(A_253, B_254, D_255, D_255) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.44/4.25  tff(c_2150, plain, (r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_74, c_2132])).
% 11.44/4.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.44/4.25  tff(c_2989, plain, (![A_320, B_321, C_322, D_323]: (r2_hidden('#skF_5'(A_320, B_321, C_322, D_323), C_322) | ~r2_hidden(A_320, D_323) | ~m1_subset_1(D_323, k1_zfmisc_1(k2_zfmisc_1(B_321, C_322))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.44/4.25  tff(c_3050, plain, (![A_326]: (r2_hidden('#skF_5'(A_326, '#skF_6', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_326, '#skF_8'))), inference(resolution, [status(thm)], [c_74, c_2989])).
% 11.44/4.25  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.44/4.25  tff(c_3061, plain, (![A_326]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_326, '#skF_8'))), inference(resolution, [status(thm)], [c_3050, c_2])).
% 11.44/4.25  tff(c_3062, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_3061])).
% 11.44/4.25  tff(c_68, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.44/4.25  tff(c_128, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.44/4.25  tff(c_145, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_68, c_128])).
% 11.44/4.25  tff(c_72, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.44/4.25  tff(c_70, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.44/4.25  tff(c_2242, plain, (![A_264, B_265, C_266]: (k1_relset_1(A_264, B_265, C_266)=k1_relat_1(C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.44/4.25  tff(c_2269, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_68, c_2242])).
% 11.44/4.25  tff(c_3531, plain, (![B_356, A_357, C_358]: (k1_xboole_0=B_356 | k1_relset_1(A_357, B_356, C_358)=A_357 | ~v1_funct_2(C_358, A_357, B_356) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_357, B_356))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.44/4.25  tff(c_3550, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_3531])).
% 11.44/4.25  tff(c_3560, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2269, c_3550])).
% 11.44/4.25  tff(c_3564, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_3560])).
% 11.44/4.25  tff(c_146, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_128])).
% 11.44/4.25  tff(c_78, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.44/4.25  tff(c_76, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.44/4.25  tff(c_2270, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_2242])).
% 11.44/4.25  tff(c_3553, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_3531])).
% 11.44/4.25  tff(c_3563, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2270, c_3553])).
% 11.44/4.25  tff(c_3619, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_3563])).
% 11.44/4.25  tff(c_3755, plain, (![A_365, B_366]: (r2_hidden('#skF_3'(A_365, B_366), k1_relat_1(A_365)) | B_366=A_365 | k1_relat_1(B_366)!=k1_relat_1(A_365) | ~v1_funct_1(B_366) | ~v1_relat_1(B_366) | ~v1_funct_1(A_365) | ~v1_relat_1(A_365))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.44/4.25  tff(c_20, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.44/4.25  tff(c_8169, plain, (![A_571, B_572]: (m1_subset_1('#skF_3'(A_571, B_572), k1_relat_1(A_571)) | B_572=A_571 | k1_relat_1(B_572)!=k1_relat_1(A_571) | ~v1_funct_1(B_572) | ~v1_relat_1(B_572) | ~v1_funct_1(A_571) | ~v1_relat_1(A_571))), inference(resolution, [status(thm)], [c_3755, c_20])).
% 11.44/4.25  tff(c_8175, plain, (![B_572]: (m1_subset_1('#skF_3'('#skF_8', B_572), '#skF_6') | B_572='#skF_8' | k1_relat_1(B_572)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_572) | ~v1_relat_1(B_572) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3619, c_8169])).
% 11.44/4.25  tff(c_23490, plain, (![B_896]: (m1_subset_1('#skF_3'('#skF_8', B_896), '#skF_6') | B_896='#skF_8' | k1_relat_1(B_896)!='#skF_6' | ~v1_funct_1(B_896) | ~v1_relat_1(B_896))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_78, c_3619, c_8175])).
% 11.44/4.25  tff(c_66, plain, (![E_50]: (k1_funct_1('#skF_9', E_50)=k1_funct_1('#skF_8', E_50) | ~m1_subset_1(E_50, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.44/4.25  tff(c_23724, plain, (![B_900]: (k1_funct_1('#skF_9', '#skF_3'('#skF_8', B_900))=k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_900)) | B_900='#skF_8' | k1_relat_1(B_900)!='#skF_6' | ~v1_funct_1(B_900) | ~v1_relat_1(B_900))), inference(resolution, [status(thm)], [c_23490, c_66])).
% 11.44/4.25  tff(c_30, plain, (![B_22, A_18]: (k1_funct_1(B_22, '#skF_3'(A_18, B_22))!=k1_funct_1(A_18, '#skF_3'(A_18, B_22)) | B_22=A_18 | k1_relat_1(B_22)!=k1_relat_1(A_18) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.44/4.25  tff(c_23731, plain, (k1_relat_1('#skF_9')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_9'='#skF_8' | k1_relat_1('#skF_9')!='#skF_6' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_23724, c_30])).
% 11.44/4.25  tff(c_23738, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_72, c_3564, c_146, c_78, c_3564, c_3619, c_23731])).
% 11.44/4.25  tff(c_64, plain, (~r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.44/4.25  tff(c_23786, plain, (~r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_23738, c_64])).
% 11.44/4.25  tff(c_23799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2150, c_23786])).
% 11.44/4.25  tff(c_23800, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_3563])).
% 11.44/4.25  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.44/4.25  tff(c_23845, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_23800, c_12])).
% 11.44/4.25  tff(c_23847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3062, c_23845])).
% 11.44/4.25  tff(c_23848, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_3560])).
% 11.44/4.25  tff(c_23892, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_23848, c_12])).
% 11.44/4.25  tff(c_23894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3062, c_23892])).
% 11.44/4.25  tff(c_23974, plain, (![A_905]: (~r2_hidden(A_905, '#skF_8'))), inference(splitRight, [status(thm)], [c_3061])).
% 11.44/4.25  tff(c_23989, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_23974])).
% 11.44/4.25  tff(c_23896, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_3061])).
% 11.44/4.25  tff(c_24001, plain, (![A_906]: (r2_hidden('#skF_5'(A_906, '#skF_6', '#skF_7', '#skF_9'), '#skF_7') | ~r2_hidden(A_906, '#skF_9'))), inference(resolution, [status(thm)], [c_68, c_2989])).
% 11.44/4.25  tff(c_24009, plain, (![A_906]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_906, '#skF_9'))), inference(resolution, [status(thm)], [c_24001, c_2])).
% 11.44/4.25  tff(c_24015, plain, (![A_907]: (~r2_hidden(A_907, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_23896, c_24009])).
% 11.44/4.25  tff(c_24030, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_24015])).
% 11.44/4.25  tff(c_112, plain, (![A_62, B_63]: (r2_hidden('#skF_2'(A_62, B_63), A_62) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.44/4.25  tff(c_120, plain, (![A_62, B_63]: (~v1_xboole_0(A_62) | r1_tarski(A_62, B_63))), inference(resolution, [status(thm)], [c_112, c_2])).
% 11.44/4.25  tff(c_173, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.44/4.25  tff(c_190, plain, (![B_78, A_79]: (B_78=A_79 | ~r1_tarski(B_78, A_79) | ~v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_120, c_173])).
% 11.44/4.25  tff(c_203, plain, (![B_63, A_62]: (B_63=A_62 | ~v1_xboole_0(B_63) | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_120, c_190])).
% 11.44/4.25  tff(c_24332, plain, (![A_923]: (A_923='#skF_9' | ~v1_xboole_0(A_923))), inference(resolution, [status(thm)], [c_24030, c_203])).
% 11.44/4.25  tff(c_24350, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_23989, c_24332])).
% 11.44/4.25  tff(c_24391, plain, (~r2_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24350, c_64])).
% 11.44/4.25  tff(c_24405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2150, c_24391])).
% 11.44/4.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.44/4.25  
% 11.44/4.25  Inference rules
% 11.44/4.25  ----------------------
% 11.44/4.25  #Ref     : 1
% 11.44/4.25  #Sup     : 5572
% 11.44/4.25  #Fact    : 0
% 11.44/4.25  #Define  : 0
% 11.44/4.25  #Split   : 31
% 11.44/4.25  #Chain   : 0
% 11.44/4.25  #Close   : 0
% 11.44/4.25  
% 11.44/4.25  Ordering : KBO
% 11.44/4.25  
% 11.44/4.25  Simplification rules
% 11.44/4.25  ----------------------
% 11.44/4.25  #Subsume      : 1597
% 11.44/4.25  #Demod        : 5690
% 11.44/4.25  #Tautology    : 2629
% 11.44/4.25  #SimpNegUnit  : 141
% 11.44/4.25  #BackRed      : 298
% 11.44/4.25  
% 11.44/4.25  #Partial instantiations: 0
% 11.44/4.25  #Strategies tried      : 1
% 11.44/4.25  
% 11.44/4.25  Timing (in seconds)
% 11.44/4.25  ----------------------
% 11.44/4.26  Preprocessing        : 0.37
% 11.44/4.26  Parsing              : 0.19
% 11.44/4.26  CNF conversion       : 0.03
% 11.44/4.26  Main loop            : 3.17
% 11.44/4.26  Inferencing          : 0.83
% 11.44/4.26  Reduction            : 1.04
% 11.44/4.26  Demodulation         : 0.75
% 11.44/4.26  BG Simplification    : 0.08
% 11.44/4.26  Subsumption          : 0.98
% 11.44/4.26  Abstraction          : 0.11
% 11.44/4.26  MUC search           : 0.00
% 11.44/4.26  Cooper               : 0.00
% 11.44/4.26  Total                : 3.58
% 11.44/4.26  Index Insertion      : 0.00
% 11.44/4.26  Index Deletion       : 0.00
% 11.44/4.26  Index Matching       : 0.00
% 11.44/4.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
