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
% DateTime   : Thu Dec  3 10:16:18 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :  284 (2055 expanded)
%              Number of leaves         :   35 ( 675 expanded)
%              Depth                    :   17
%              Number of atoms          :  595 (6302 expanded)
%              Number of equality atoms :  258 (1747 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_80,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8942,plain,(
    ! [A_824,B_825,D_826] :
      ( r2_relset_1(A_824,B_825,D_826,D_826)
      | ~ m1_subset_1(D_826,k1_zfmisc_1(k2_zfmisc_1(A_824,B_825))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8964,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_8942])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_62,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8997,plain,(
    ! [A_832,B_833,C_834] :
      ( k1_relset_1(A_832,B_833,C_834) = k1_relat_1(C_834)
      | ~ m1_subset_1(C_834,k1_zfmisc_1(k2_zfmisc_1(A_832,B_833))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_9026,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_8997])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_9025,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_8997])).

tff(c_9095,plain,(
    ! [B_847,A_848,C_849] :
      ( k1_xboole_0 = B_847
      | k1_relset_1(A_848,B_847,C_849) = A_848
      | ~ v1_funct_2(C_849,A_848,B_847)
      | ~ m1_subset_1(C_849,k1_zfmisc_1(k2_zfmisc_1(A_848,B_847))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_9110,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_9095])).

tff(c_9127,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_9025,c_9110])).

tff(c_9132,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9127])).

tff(c_155,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_176,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_155])).

tff(c_5134,plain,(
    ! [A_493,B_494,D_495] :
      ( r2_relset_1(A_493,B_494,D_495,D_495)
      | ~ m1_subset_1(D_495,k1_zfmisc_1(k2_zfmisc_1(A_493,B_494))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5156,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_5134])).

tff(c_5184,plain,(
    ! [A_501,B_502,C_503] :
      ( k1_relset_1(A_501,B_502,C_503) = k1_relat_1(C_503)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_501,B_502))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5214,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_5184])).

tff(c_5331,plain,(
    ! [B_521,A_522,C_523] :
      ( k1_xboole_0 = B_521
      | k1_relset_1(A_522,B_521,C_523) = A_522
      | ~ v1_funct_2(C_523,A_522,B_521)
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(A_522,B_521))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5346,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_5331])).

tff(c_5363,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5214,c_5346])).

tff(c_5368,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5363])).

tff(c_177,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_155])).

tff(c_5215,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_5184])).

tff(c_5349,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_5331])).

tff(c_5366,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5215,c_5349])).

tff(c_5374,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5366])).

tff(c_24,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ v1_xboole_0(B_11)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_143,plain,(
    ! [E_53] :
      ( k1_funct_1('#skF_5',E_53) = k1_funct_1('#skF_6',E_53)
      | ~ m1_subset_1(E_53,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_148,plain,(
    ! [B_11] :
      ( k1_funct_1('#skF_5',B_11) = k1_funct_1('#skF_6',B_11)
      | ~ v1_xboole_0(B_11)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_143])).

tff(c_207,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_5545,plain,(
    ! [A_544,B_545] :
      ( r2_hidden('#skF_2'(A_544,B_545),k1_relat_1(A_544))
      | B_545 = A_544
      | k1_relat_1(B_545) != k1_relat_1(A_544)
      | ~ v1_funct_1(B_545)
      | ~ v1_relat_1(B_545)
      | ~ v1_funct_1(A_544)
      | ~ v1_relat_1(A_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5554,plain,(
    ! [B_545] :
      ( r2_hidden('#skF_2'('#skF_6',B_545),'#skF_3')
      | B_545 = '#skF_6'
      | k1_relat_1(B_545) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_545)
      | ~ v1_relat_1(B_545)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5374,c_5545])).

tff(c_5662,plain,(
    ! [B_560] :
      ( r2_hidden('#skF_2'('#skF_6',B_560),'#skF_3')
      | B_560 = '#skF_6'
      | k1_relat_1(B_560) != '#skF_3'
      | ~ v1_funct_1(B_560)
      | ~ v1_relat_1(B_560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_64,c_5374,c_5554])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ r2_hidden(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5665,plain,(
    ! [B_560] :
      ( m1_subset_1('#skF_2'('#skF_6',B_560),'#skF_3')
      | v1_xboole_0('#skF_3')
      | B_560 = '#skF_6'
      | k1_relat_1(B_560) != '#skF_3'
      | ~ v1_funct_1(B_560)
      | ~ v1_relat_1(B_560) ) ),
    inference(resolution,[status(thm)],[c_5662,c_20])).

tff(c_5723,plain,(
    ! [B_566] :
      ( m1_subset_1('#skF_2'('#skF_6',B_566),'#skF_3')
      | B_566 = '#skF_6'
      | k1_relat_1(B_566) != '#skF_3'
      | ~ v1_funct_1(B_566)
      | ~ v1_relat_1(B_566) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_5665])).

tff(c_58,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_5',E_37) = k1_funct_1('#skF_6',E_37)
      | ~ m1_subset_1(E_37,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5780,plain,(
    ! [B_571] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_571)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_571))
      | B_571 = '#skF_6'
      | k1_relat_1(B_571) != '#skF_3'
      | ~ v1_funct_1(B_571)
      | ~ v1_relat_1(B_571) ) ),
    inference(resolution,[status(thm)],[c_5723,c_58])).

tff(c_32,plain,(
    ! [B_18,A_14] :
      ( k1_funct_1(B_18,'#skF_2'(A_14,B_18)) != k1_funct_1(A_14,'#skF_2'(A_14,B_18))
      | B_18 = A_14
      | k1_relat_1(B_18) != k1_relat_1(A_14)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5787,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5780,c_32])).

tff(c_5794,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_70,c_5368,c_177,c_64,c_5374,c_5368,c_5787])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5808,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5794,c_56])).

tff(c_5819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5156,c_5808])).

tff(c_5820,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5366])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5846,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5820,c_12])).

tff(c_16,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5844,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5820,c_5820,c_16])).

tff(c_120,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_132,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_120])).

tff(c_236,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_246,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_132,c_236])).

tff(c_5158,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_5872,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5844,c_5158])).

tff(c_5880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5846,c_5872])).

tff(c_5881,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5363])).

tff(c_5908,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5881,c_12])).

tff(c_5906,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5881,c_5881,c_16])).

tff(c_5954,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5906,c_5158])).

tff(c_5962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5908,c_5954])).

tff(c_5963,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_5969,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5963,c_66])).

tff(c_6009,plain,(
    ! [A_578,B_579,C_580] :
      ( k1_relset_1(A_578,B_579,C_580) = k1_relat_1(C_580)
      | ~ m1_subset_1(C_580,k1_zfmisc_1(k2_zfmisc_1(A_578,B_579))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6195,plain,(
    ! [C_602] :
      ( k1_relset_1('#skF_3','#skF_4',C_602) = k1_relat_1(C_602)
      | ~ m1_subset_1(C_602,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5963,c_6009])).

tff(c_6215,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5969,c_6195])).

tff(c_6517,plain,(
    ! [B_635,A_636,C_637] :
      ( k1_xboole_0 = B_635
      | k1_relset_1(A_636,B_635,C_637) = A_636
      | ~ v1_funct_2(C_637,A_636,B_635)
      | ~ m1_subset_1(C_637,k1_zfmisc_1(k2_zfmisc_1(A_636,B_635))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6520,plain,(
    ! [C_637] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_637) = '#skF_3'
      | ~ v1_funct_2(C_637,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_637,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5963,c_6517])).

tff(c_6555,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6520])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5977,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5963,c_14])).

tff(c_6095,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5977])).

tff(c_6573,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6555,c_6095])).

tff(c_6584,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6555,c_6555,c_16])).

tff(c_6688,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6584,c_5963])).

tff(c_6690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6573,c_6688])).

tff(c_6817,plain,(
    ! [C_653] :
      ( k1_relset_1('#skF_3','#skF_4',C_653) = '#skF_3'
      | ~ v1_funct_2(C_653,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_653,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_6520])).

tff(c_6823,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_5969,c_6817])).

tff(c_6841,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6215,c_6823])).

tff(c_5970,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5963,c_60])).

tff(c_6214,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5970,c_6195])).

tff(c_6820,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_5970,c_6817])).

tff(c_6838,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6214,c_6820])).

tff(c_6866,plain,(
    ! [A_654,B_655] :
      ( r2_hidden('#skF_2'(A_654,B_655),k1_relat_1(A_654))
      | B_655 = A_654
      | k1_relat_1(B_655) != k1_relat_1(A_654)
      | ~ v1_funct_1(B_655)
      | ~ v1_relat_1(B_655)
      | ~ v1_funct_1(A_654)
      | ~ v1_relat_1(A_654) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6878,plain,(
    ! [B_655] :
      ( r2_hidden('#skF_2'('#skF_6',B_655),'#skF_3')
      | B_655 = '#skF_6'
      | k1_relat_1(B_655) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_655)
      | ~ v1_relat_1(B_655)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6838,c_6866])).

tff(c_6970,plain,(
    ! [B_662] :
      ( r2_hidden('#skF_2'('#skF_6',B_662),'#skF_3')
      | B_662 = '#skF_6'
      | k1_relat_1(B_662) != '#skF_3'
      | ~ v1_funct_1(B_662)
      | ~ v1_relat_1(B_662) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_64,c_6838,c_6878])).

tff(c_6973,plain,(
    ! [B_662] :
      ( m1_subset_1('#skF_2'('#skF_6',B_662),'#skF_3')
      | v1_xboole_0('#skF_3')
      | B_662 = '#skF_6'
      | k1_relat_1(B_662) != '#skF_3'
      | ~ v1_funct_1(B_662)
      | ~ v1_relat_1(B_662) ) ),
    inference(resolution,[status(thm)],[c_6970,c_20])).

tff(c_6996,plain,(
    ! [B_666] :
      ( m1_subset_1('#skF_2'('#skF_6',B_666),'#skF_3')
      | B_666 = '#skF_6'
      | k1_relat_1(B_666) != '#skF_3'
      | ~ v1_funct_1(B_666)
      | ~ v1_relat_1(B_666) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_6973])).

tff(c_7058,plain,(
    ! [B_672] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_672)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_672))
      | B_672 = '#skF_6'
      | k1_relat_1(B_672) != '#skF_3'
      | ~ v1_funct_1(B_672)
      | ~ v1_relat_1(B_672) ) ),
    inference(resolution,[status(thm)],[c_6996,c_58])).

tff(c_7065,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7058,c_32])).

tff(c_7072,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_70,c_6841,c_177,c_64,c_6841,c_6838,c_7065])).

tff(c_133,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_120])).

tff(c_245,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_133,c_236])).

tff(c_5079,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_5965,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5963,c_5079])).

tff(c_7098,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7072,c_5965])).

tff(c_7112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_7098])).

tff(c_7114,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5977])).

tff(c_7127,plain,(
    ! [A_7] : r1_tarski('#skF_5',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7114,c_12])).

tff(c_7136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7127,c_5965])).

tff(c_7137,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_7142,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7137,c_66])).

tff(c_7248,plain,(
    ! [A_678,B_679,C_680] :
      ( k1_relset_1(A_678,B_679,C_680) = k1_relat_1(C_680)
      | ~ m1_subset_1(C_680,k1_zfmisc_1(k2_zfmisc_1(A_678,B_679))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7431,plain,(
    ! [C_700] :
      ( k1_relset_1('#skF_3','#skF_4',C_700) = k1_relat_1(C_700)
      | ~ m1_subset_1(C_700,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7137,c_7248])).

tff(c_7450,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_7142,c_7431])).

tff(c_7720,plain,(
    ! [B_730,A_731,C_732] :
      ( k1_xboole_0 = B_730
      | k1_relset_1(A_731,B_730,C_732) = A_731
      | ~ v1_funct_2(C_732,A_731,B_730)
      | ~ m1_subset_1(C_732,k1_zfmisc_1(k2_zfmisc_1(A_731,B_730))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_7723,plain,(
    ! [C_732] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_732) = '#skF_3'
      | ~ v1_funct_2(C_732,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_732,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7137,c_7720])).

tff(c_7790,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7723])).

tff(c_7148,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_7137,c_14])).

tff(c_7273,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_7148])).

tff(c_7809,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7790,c_7273])).

tff(c_7818,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7790,c_7790,c_16])).

tff(c_7882,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7818,c_7137])).

tff(c_7884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7809,c_7882])).

tff(c_7983,plain,(
    ! [C_753] :
      ( k1_relset_1('#skF_3','#skF_4',C_753) = '#skF_3'
      | ~ v1_funct_2(C_753,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_753,k1_zfmisc_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_7723])).

tff(c_7986,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_7142,c_7983])).

tff(c_8004,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_7450,c_7986])).

tff(c_7143,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7137,c_60])).

tff(c_7451,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7143,c_7431])).

tff(c_7989,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_7143,c_7983])).

tff(c_8007,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_7451,c_7989])).

tff(c_8036,plain,(
    ! [A_754,B_755] :
      ( r2_hidden('#skF_2'(A_754,B_755),k1_relat_1(A_754))
      | B_755 = A_754
      | k1_relat_1(B_755) != k1_relat_1(A_754)
      | ~ v1_funct_1(B_755)
      | ~ v1_relat_1(B_755)
      | ~ v1_funct_1(A_754)
      | ~ v1_relat_1(A_754) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8045,plain,(
    ! [B_755] :
      ( r2_hidden('#skF_2'('#skF_6',B_755),'#skF_3')
      | B_755 = '#skF_6'
      | k1_relat_1(B_755) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_755)
      | ~ v1_relat_1(B_755)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8007,c_8036])).

tff(c_8122,plain,(
    ! [B_761] :
      ( r2_hidden('#skF_2'('#skF_6',B_761),'#skF_3')
      | B_761 = '#skF_6'
      | k1_relat_1(B_761) != '#skF_3'
      | ~ v1_funct_1(B_761)
      | ~ v1_relat_1(B_761) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_64,c_8007,c_8045])).

tff(c_8125,plain,(
    ! [B_761] :
      ( m1_subset_1('#skF_2'('#skF_6',B_761),'#skF_3')
      | v1_xboole_0('#skF_3')
      | B_761 = '#skF_6'
      | k1_relat_1(B_761) != '#skF_3'
      | ~ v1_funct_1(B_761)
      | ~ v1_relat_1(B_761) ) ),
    inference(resolution,[status(thm)],[c_8122,c_20])).

tff(c_8144,plain,(
    ! [B_763] :
      ( m1_subset_1('#skF_2'('#skF_6',B_763),'#skF_3')
      | B_763 = '#skF_6'
      | k1_relat_1(B_763) != '#skF_3'
      | ~ v1_funct_1(B_763)
      | ~ v1_relat_1(B_763) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_8125])).

tff(c_8523,plain,(
    ! [B_793] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_793)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_793))
      | B_793 = '#skF_6'
      | k1_relat_1(B_793) != '#skF_3'
      | ~ v1_funct_1(B_793)
      | ~ v1_relat_1(B_793) ) ),
    inference(resolution,[status(thm)],[c_8144,c_58])).

tff(c_8530,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8523,c_32])).

tff(c_8537,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_70,c_8004,c_177,c_64,c_8007,c_8004,c_8530])).

tff(c_7199,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7137,c_7137,c_246])).

tff(c_7200,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7199])).

tff(c_8546,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8537,c_7200])).

tff(c_8560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8546])).

tff(c_8562,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7148])).

tff(c_8574,plain,(
    ! [A_7] : r1_tarski('#skF_6',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8562,c_12])).

tff(c_8584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8574,c_7200])).

tff(c_8585,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7199])).

tff(c_8592,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8585,c_56])).

tff(c_7162,plain,(
    ! [A_673,B_674,D_675] :
      ( r2_relset_1(A_673,B_674,D_675,D_675)
      | ~ m1_subset_1(D_675,k1_zfmisc_1(k2_zfmisc_1(A_673,B_674))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8738,plain,(
    ! [D_804] :
      ( r2_relset_1('#skF_3','#skF_4',D_804,D_804)
      | ~ m1_subset_1(D_804,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7137,c_7162])).

tff(c_8740,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_7143,c_8738])).

tff(c_8753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8592,c_8740])).

tff(c_8755,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_9113,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_9095])).

tff(c_9130,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9026,c_9113])).

tff(c_9138,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9130])).

tff(c_9424,plain,(
    ! [A_882,B_883] :
      ( r2_hidden('#skF_2'(A_882,B_883),k1_relat_1(A_882))
      | B_883 = A_882
      | k1_relat_1(B_883) != k1_relat_1(A_882)
      | ~ v1_funct_1(B_883)
      | ~ v1_relat_1(B_883)
      | ~ v1_funct_1(A_882)
      | ~ v1_relat_1(A_882) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_9433,plain,(
    ! [B_883] :
      ( r2_hidden('#skF_2'('#skF_6',B_883),'#skF_3')
      | B_883 = '#skF_6'
      | k1_relat_1(B_883) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_883)
      | ~ v1_relat_1(B_883)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9138,c_9424])).

tff(c_9453,plain,(
    ! [B_886] :
      ( r2_hidden('#skF_2'('#skF_6',B_886),'#skF_3')
      | B_886 = '#skF_6'
      | k1_relat_1(B_886) != '#skF_3'
      | ~ v1_funct_1(B_886)
      | ~ v1_relat_1(B_886) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_64,c_9138,c_9433])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9459,plain,(
    ! [B_886] :
      ( ~ v1_xboole_0('#skF_3')
      | B_886 = '#skF_6'
      | k1_relat_1(B_886) != '#skF_3'
      | ~ v1_funct_1(B_886)
      | ~ v1_relat_1(B_886) ) ),
    inference(resolution,[status(thm)],[c_9453,c_2])).

tff(c_9465,plain,(
    ! [B_887] :
      ( B_887 = '#skF_6'
      | k1_relat_1(B_887) != '#skF_3'
      | ~ v1_funct_1(B_887)
      | ~ v1_relat_1(B_887) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8755,c_9459])).

tff(c_9480,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_176,c_9465])).

tff(c_9490,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9132,c_9480])).

tff(c_9501,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9490,c_56])).

tff(c_9512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8964,c_9501])).

tff(c_9513,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9130])).

tff(c_9537,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9513,c_12])).

tff(c_9535,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9513,c_9513,c_16])).

tff(c_8784,plain,(
    ! [B_807,A_808] :
      ( B_807 = A_808
      | ~ r1_tarski(B_807,A_808)
      | ~ r1_tarski(A_808,B_807) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8793,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_133,c_8784])).

tff(c_9053,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_8793])).

tff(c_9554,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9535,c_9053])).

tff(c_9562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9537,c_9554])).

tff(c_9563,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9127])).

tff(c_9588,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9563,c_12])).

tff(c_9586,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9563,c_9563,c_16])).

tff(c_9634,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9586,c_9053])).

tff(c_9642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9588,c_9634])).

tff(c_9643,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8793])).

tff(c_9650,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9643,c_60])).

tff(c_10089,plain,(
    ! [B_935,C_936,A_937] :
      ( k1_xboole_0 = B_935
      | v1_funct_2(C_936,A_937,B_935)
      | k1_relset_1(A_937,B_935,C_936) != A_937
      | ~ m1_subset_1(C_936,k1_zfmisc_1(k2_zfmisc_1(A_937,B_935))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10092,plain,(
    ! [C_936] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(C_936,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_936) != '#skF_3'
      | ~ m1_subset_1(C_936,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9643,c_10089])).

tff(c_10159,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10092])).

tff(c_9660,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_9643,c_14])).

tff(c_9755,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_9660])).

tff(c_10172,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10159,c_9755])).

tff(c_10187,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10159,c_10159,c_16])).

tff(c_10251,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10187,c_9643])).

tff(c_10253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10172,c_10251])).

tff(c_10255,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10092])).

tff(c_9962,plain,(
    ! [B_920,A_921,C_922] :
      ( k1_xboole_0 = B_920
      | k1_relset_1(A_921,B_920,C_922) = A_921
      | ~ v1_funct_2(C_922,A_921,B_920)
      | ~ m1_subset_1(C_922,k1_zfmisc_1(k2_zfmisc_1(A_921,B_920))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_9965,plain,(
    ! [C_922] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_922) = '#skF_3'
      | ~ v1_funct_2(C_922,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_922,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9643,c_9962])).

tff(c_10257,plain,(
    ! [C_949] :
      ( k1_relset_1('#skF_3','#skF_4',C_949) = '#skF_3'
      | ~ v1_funct_2(C_949,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_949,k1_zfmisc_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10255,c_9965])).

tff(c_10260,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_9650,c_10257])).

tff(c_10278,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9026,c_10260])).

tff(c_9649,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9643,c_66])).

tff(c_10263,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_9649,c_10257])).

tff(c_10281,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_9025,c_10263])).

tff(c_10424,plain,(
    ! [A_960,B_961] :
      ( r2_hidden('#skF_2'(A_960,B_961),k1_relat_1(A_960))
      | B_961 = A_960
      | k1_relat_1(B_961) != k1_relat_1(A_960)
      | ~ v1_funct_1(B_961)
      | ~ v1_relat_1(B_961)
      | ~ v1_funct_1(A_960)
      | ~ v1_relat_1(A_960) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10433,plain,(
    ! [B_961] :
      ( r2_hidden('#skF_2'('#skF_5',B_961),'#skF_3')
      | B_961 = '#skF_5'
      | k1_relat_1(B_961) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_961)
      | ~ v1_relat_1(B_961)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10281,c_10424])).

tff(c_10493,plain,(
    ! [B_966] :
      ( r2_hidden('#skF_2'('#skF_5',B_966),'#skF_3')
      | B_966 = '#skF_5'
      | k1_relat_1(B_966) != '#skF_3'
      | ~ v1_funct_1(B_966)
      | ~ v1_relat_1(B_966) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_70,c_10281,c_10433])).

tff(c_10499,plain,(
    ! [B_966] :
      ( ~ v1_xboole_0('#skF_3')
      | B_966 = '#skF_5'
      | k1_relat_1(B_966) != '#skF_3'
      | ~ v1_funct_1(B_966)
      | ~ v1_relat_1(B_966) ) ),
    inference(resolution,[status(thm)],[c_10493,c_2])).

tff(c_10505,plain,(
    ! [B_967] :
      ( B_967 = '#skF_5'
      | k1_relat_1(B_967) != '#skF_3'
      | ~ v1_funct_1(B_967)
      | ~ v1_relat_1(B_967) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8755,c_10499])).

tff(c_10520,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_6') != '#skF_3'
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_177,c_10505])).

tff(c_10530,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_10278,c_10520])).

tff(c_8794,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_132,c_8784])).

tff(c_8975,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8794])).

tff(c_9645,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9643,c_8975])).

tff(c_10539,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10530,c_9645])).

tff(c_10554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10539])).

tff(c_10556,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9660])).

tff(c_10575,plain,(
    ! [A_7] : r1_tarski('#skF_6',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10556,c_12])).

tff(c_10584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10575,c_9645])).

tff(c_10585,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8794])).

tff(c_10591,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10585,c_60])).

tff(c_10609,plain,(
    ! [A_968,B_969,C_970] :
      ( k1_relset_1(A_968,B_969,C_970) = k1_relat_1(C_970)
      | ~ m1_subset_1(C_970,k1_zfmisc_1(k2_zfmisc_1(A_968,B_969))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10881,plain,(
    ! [C_1001] :
      ( k1_relset_1('#skF_3','#skF_4',C_1001) = k1_relat_1(C_1001)
      | ~ m1_subset_1(C_1001,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10585,c_10609])).

tff(c_10901,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10591,c_10881])).

tff(c_11053,plain,(
    ! [B_1014,A_1015,C_1016] :
      ( k1_xboole_0 = B_1014
      | k1_relset_1(A_1015,B_1014,C_1016) = A_1015
      | ~ v1_funct_2(C_1016,A_1015,B_1014)
      | ~ m1_subset_1(C_1016,k1_zfmisc_1(k2_zfmisc_1(A_1015,B_1014))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_11056,plain,(
    ! [C_1016] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_1016) = '#skF_3'
      | ~ v1_funct_2(C_1016,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_1016,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10585,c_11053])).

tff(c_11100,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11056])).

tff(c_10598,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_10585,c_14])).

tff(c_10717,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_10598])).

tff(c_11118,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11100,c_10717])).

tff(c_11130,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11100,c_11100,c_16])).

tff(c_11220,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11130,c_10585])).

tff(c_11222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11118,c_11220])).

tff(c_11339,plain,(
    ! [C_1038] :
      ( k1_relset_1('#skF_3','#skF_4',C_1038) = '#skF_3'
      | ~ v1_funct_2(C_1038,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_1038,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_11056])).

tff(c_11345,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_10591,c_11339])).

tff(c_11363,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10901,c_11345])).

tff(c_10590,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10585,c_66])).

tff(c_10900,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10590,c_10881])).

tff(c_11342,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_10590,c_11339])).

tff(c_11360,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_10900,c_11342])).

tff(c_11389,plain,(
    ! [A_1039,B_1040] :
      ( r2_hidden('#skF_2'(A_1039,B_1040),k1_relat_1(A_1039))
      | B_1040 = A_1039
      | k1_relat_1(B_1040) != k1_relat_1(A_1039)
      | ~ v1_funct_1(B_1040)
      | ~ v1_relat_1(B_1040)
      | ~ v1_funct_1(A_1039)
      | ~ v1_relat_1(A_1039) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_11401,plain,(
    ! [B_1040] :
      ( r2_hidden('#skF_2'('#skF_5',B_1040),'#skF_3')
      | B_1040 = '#skF_5'
      | k1_relat_1(B_1040) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_1040)
      | ~ v1_relat_1(B_1040)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11360,c_11389])).

tff(c_11540,plain,(
    ! [B_1053] :
      ( r2_hidden('#skF_2'('#skF_5',B_1053),'#skF_3')
      | B_1053 = '#skF_5'
      | k1_relat_1(B_1053) != '#skF_3'
      | ~ v1_funct_1(B_1053)
      | ~ v1_relat_1(B_1053) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_70,c_11360,c_11401])).

tff(c_11546,plain,(
    ! [B_1053] :
      ( ~ v1_xboole_0('#skF_3')
      | B_1053 = '#skF_5'
      | k1_relat_1(B_1053) != '#skF_3'
      | ~ v1_funct_1(B_1053)
      | ~ v1_relat_1(B_1053) ) ),
    inference(resolution,[status(thm)],[c_11540,c_2])).

tff(c_11552,plain,(
    ! [B_1054] :
      ( B_1054 = '#skF_5'
      | k1_relat_1(B_1054) != '#skF_3'
      | ~ v1_funct_1(B_1054)
      | ~ v1_relat_1(B_1054) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8755,c_11546])).

tff(c_11567,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_6') != '#skF_3'
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_177,c_11552])).

tff(c_11579,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_11363,c_11567])).

tff(c_10588,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10585,c_133])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10636,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_10588,c_6])).

tff(c_10656,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_10636])).

tff(c_11603,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11579,c_10656])).

tff(c_11621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11603])).

tff(c_11623,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10598])).

tff(c_11637,plain,(
    ! [A_7] : r1_tarski('#skF_5',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11623,c_12])).

tff(c_11646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11637,c_10656])).

tff(c_11647,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10636])).

tff(c_11659,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11647,c_56])).

tff(c_11667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8964,c_11659])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.32  % Computer   : n008.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 13:12:00 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.51/2.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.51/2.89  
% 7.51/2.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.51/2.89  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 7.51/2.89  
% 7.51/2.89  %Foreground sorts:
% 7.51/2.89  
% 7.51/2.89  
% 7.51/2.89  %Background operators:
% 7.51/2.89  
% 7.51/2.89  
% 7.51/2.89  %Foreground operators:
% 7.51/2.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.51/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.51/2.89  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.51/2.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.51/2.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.51/2.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.51/2.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.51/2.89  tff('#skF_5', type, '#skF_5': $i).
% 7.51/2.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.51/2.89  tff('#skF_6', type, '#skF_6': $i).
% 7.51/2.89  tff('#skF_3', type, '#skF_3': $i).
% 7.51/2.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.51/2.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.51/2.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.51/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.51/2.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.51/2.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.51/2.89  tff('#skF_4', type, '#skF_4': $i).
% 7.51/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.51/2.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.51/2.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.51/2.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.51/2.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.51/2.89  
% 7.86/2.92  tff(f_135, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 7.86/2.92  tff(f_96, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.86/2.92  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.86/2.92  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.86/2.92  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.86/2.92  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.86/2.92  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 7.86/2.92  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 7.86/2.92  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.86/2.92  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.86/2.92  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.86/2.92  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.86/2.92  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.86/2.92  tff(c_8942, plain, (![A_824, B_825, D_826]: (r2_relset_1(A_824, B_825, D_826, D_826) | ~m1_subset_1(D_826, k1_zfmisc_1(k2_zfmisc_1(A_824, B_825))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.86/2.92  tff(c_8964, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_8942])).
% 7.86/2.92  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.86/2.92  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.86/2.92  tff(c_62, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.86/2.92  tff(c_8997, plain, (![A_832, B_833, C_834]: (k1_relset_1(A_832, B_833, C_834)=k1_relat_1(C_834) | ~m1_subset_1(C_834, k1_zfmisc_1(k2_zfmisc_1(A_832, B_833))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.86/2.92  tff(c_9026, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_8997])).
% 7.86/2.92  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.86/2.92  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.86/2.92  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.86/2.92  tff(c_9025, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_8997])).
% 7.86/2.92  tff(c_9095, plain, (![B_847, A_848, C_849]: (k1_xboole_0=B_847 | k1_relset_1(A_848, B_847, C_849)=A_848 | ~v1_funct_2(C_849, A_848, B_847) | ~m1_subset_1(C_849, k1_zfmisc_1(k2_zfmisc_1(A_848, B_847))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.86/2.92  tff(c_9110, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_9095])).
% 7.86/2.92  tff(c_9127, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_9025, c_9110])).
% 7.86/2.92  tff(c_9132, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_9127])).
% 7.86/2.92  tff(c_155, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.86/2.92  tff(c_176, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_155])).
% 7.86/2.92  tff(c_5134, plain, (![A_493, B_494, D_495]: (r2_relset_1(A_493, B_494, D_495, D_495) | ~m1_subset_1(D_495, k1_zfmisc_1(k2_zfmisc_1(A_493, B_494))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.86/2.92  tff(c_5156, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_5134])).
% 7.86/2.92  tff(c_5184, plain, (![A_501, B_502, C_503]: (k1_relset_1(A_501, B_502, C_503)=k1_relat_1(C_503) | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_501, B_502))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.86/2.92  tff(c_5214, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_5184])).
% 7.86/2.92  tff(c_5331, plain, (![B_521, A_522, C_523]: (k1_xboole_0=B_521 | k1_relset_1(A_522, B_521, C_523)=A_522 | ~v1_funct_2(C_523, A_522, B_521) | ~m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1(A_522, B_521))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.86/2.92  tff(c_5346, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_5331])).
% 7.86/2.92  tff(c_5363, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5214, c_5346])).
% 7.86/2.92  tff(c_5368, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_5363])).
% 7.86/2.92  tff(c_177, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_155])).
% 7.86/2.92  tff(c_5215, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_5184])).
% 7.86/2.92  tff(c_5349, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_5331])).
% 7.86/2.92  tff(c_5366, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5215, c_5349])).
% 7.86/2.92  tff(c_5374, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_5366])).
% 7.86/2.92  tff(c_24, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~v1_xboole_0(B_11) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.86/2.92  tff(c_143, plain, (![E_53]: (k1_funct_1('#skF_5', E_53)=k1_funct_1('#skF_6', E_53) | ~m1_subset_1(E_53, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.86/2.92  tff(c_148, plain, (![B_11]: (k1_funct_1('#skF_5', B_11)=k1_funct_1('#skF_6', B_11) | ~v1_xboole_0(B_11) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_143])).
% 7.86/2.92  tff(c_207, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_148])).
% 7.86/2.92  tff(c_5545, plain, (![A_544, B_545]: (r2_hidden('#skF_2'(A_544, B_545), k1_relat_1(A_544)) | B_545=A_544 | k1_relat_1(B_545)!=k1_relat_1(A_544) | ~v1_funct_1(B_545) | ~v1_relat_1(B_545) | ~v1_funct_1(A_544) | ~v1_relat_1(A_544))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.86/2.92  tff(c_5554, plain, (![B_545]: (r2_hidden('#skF_2'('#skF_6', B_545), '#skF_3') | B_545='#skF_6' | k1_relat_1(B_545)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_545) | ~v1_relat_1(B_545) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5374, c_5545])).
% 7.86/2.92  tff(c_5662, plain, (![B_560]: (r2_hidden('#skF_2'('#skF_6', B_560), '#skF_3') | B_560='#skF_6' | k1_relat_1(B_560)!='#skF_3' | ~v1_funct_1(B_560) | ~v1_relat_1(B_560))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_64, c_5374, c_5554])).
% 7.86/2.92  tff(c_20, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~r2_hidden(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.86/2.92  tff(c_5665, plain, (![B_560]: (m1_subset_1('#skF_2'('#skF_6', B_560), '#skF_3') | v1_xboole_0('#skF_3') | B_560='#skF_6' | k1_relat_1(B_560)!='#skF_3' | ~v1_funct_1(B_560) | ~v1_relat_1(B_560))), inference(resolution, [status(thm)], [c_5662, c_20])).
% 7.86/2.92  tff(c_5723, plain, (![B_566]: (m1_subset_1('#skF_2'('#skF_6', B_566), '#skF_3') | B_566='#skF_6' | k1_relat_1(B_566)!='#skF_3' | ~v1_funct_1(B_566) | ~v1_relat_1(B_566))), inference(negUnitSimplification, [status(thm)], [c_207, c_5665])).
% 7.86/2.92  tff(c_58, plain, (![E_37]: (k1_funct_1('#skF_5', E_37)=k1_funct_1('#skF_6', E_37) | ~m1_subset_1(E_37, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.86/2.92  tff(c_5780, plain, (![B_571]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_571))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_571)) | B_571='#skF_6' | k1_relat_1(B_571)!='#skF_3' | ~v1_funct_1(B_571) | ~v1_relat_1(B_571))), inference(resolution, [status(thm)], [c_5723, c_58])).
% 7.86/2.92  tff(c_32, plain, (![B_18, A_14]: (k1_funct_1(B_18, '#skF_2'(A_14, B_18))!=k1_funct_1(A_14, '#skF_2'(A_14, B_18)) | B_18=A_14 | k1_relat_1(B_18)!=k1_relat_1(A_14) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.86/2.92  tff(c_5787, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5780, c_32])).
% 7.86/2.92  tff(c_5794, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_70, c_5368, c_177, c_64, c_5374, c_5368, c_5787])).
% 7.86/2.92  tff(c_56, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.86/2.92  tff(c_5808, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5794, c_56])).
% 7.86/2.92  tff(c_5819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5156, c_5808])).
% 7.86/2.92  tff(c_5820, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5366])).
% 7.86/2.92  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.86/2.92  tff(c_5846, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_5820, c_12])).
% 7.86/2.92  tff(c_16, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.86/2.92  tff(c_5844, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5820, c_5820, c_16])).
% 7.86/2.92  tff(c_120, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.86/2.92  tff(c_132, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_120])).
% 7.86/2.92  tff(c_236, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.86/2.92  tff(c_246, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_132, c_236])).
% 7.86/2.92  tff(c_5158, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_246])).
% 7.86/2.92  tff(c_5872, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5844, c_5158])).
% 7.86/2.92  tff(c_5880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5846, c_5872])).
% 7.86/2.92  tff(c_5881, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5363])).
% 7.86/2.92  tff(c_5908, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_5881, c_12])).
% 7.86/2.92  tff(c_5906, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5881, c_5881, c_16])).
% 7.86/2.92  tff(c_5954, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5906, c_5158])).
% 7.86/2.92  tff(c_5962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5908, c_5954])).
% 7.86/2.92  tff(c_5963, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_246])).
% 7.86/2.92  tff(c_5969, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5963, c_66])).
% 7.86/2.92  tff(c_6009, plain, (![A_578, B_579, C_580]: (k1_relset_1(A_578, B_579, C_580)=k1_relat_1(C_580) | ~m1_subset_1(C_580, k1_zfmisc_1(k2_zfmisc_1(A_578, B_579))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.86/2.92  tff(c_6195, plain, (![C_602]: (k1_relset_1('#skF_3', '#skF_4', C_602)=k1_relat_1(C_602) | ~m1_subset_1(C_602, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_5963, c_6009])).
% 7.86/2.92  tff(c_6215, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5969, c_6195])).
% 7.86/2.92  tff(c_6517, plain, (![B_635, A_636, C_637]: (k1_xboole_0=B_635 | k1_relset_1(A_636, B_635, C_637)=A_636 | ~v1_funct_2(C_637, A_636, B_635) | ~m1_subset_1(C_637, k1_zfmisc_1(k2_zfmisc_1(A_636, B_635))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.86/2.92  tff(c_6520, plain, (![C_637]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_637)='#skF_3' | ~v1_funct_2(C_637, '#skF_3', '#skF_4') | ~m1_subset_1(C_637, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_5963, c_6517])).
% 7.86/2.92  tff(c_6555, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_6520])).
% 7.86/2.92  tff(c_14, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.86/2.92  tff(c_5977, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5963, c_14])).
% 7.86/2.92  tff(c_6095, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_5977])).
% 7.86/2.92  tff(c_6573, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6555, c_6095])).
% 7.86/2.92  tff(c_6584, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6555, c_6555, c_16])).
% 7.86/2.92  tff(c_6688, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6584, c_5963])).
% 7.86/2.92  tff(c_6690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6573, c_6688])).
% 7.86/2.92  tff(c_6817, plain, (![C_653]: (k1_relset_1('#skF_3', '#skF_4', C_653)='#skF_3' | ~v1_funct_2(C_653, '#skF_3', '#skF_4') | ~m1_subset_1(C_653, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_6520])).
% 7.86/2.92  tff(c_6823, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_5969, c_6817])).
% 7.86/2.92  tff(c_6841, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_6215, c_6823])).
% 7.86/2.92  tff(c_5970, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5963, c_60])).
% 7.86/2.92  tff(c_6214, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5970, c_6195])).
% 7.86/2.92  tff(c_6820, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_5970, c_6817])).
% 7.86/2.92  tff(c_6838, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_6214, c_6820])).
% 7.86/2.92  tff(c_6866, plain, (![A_654, B_655]: (r2_hidden('#skF_2'(A_654, B_655), k1_relat_1(A_654)) | B_655=A_654 | k1_relat_1(B_655)!=k1_relat_1(A_654) | ~v1_funct_1(B_655) | ~v1_relat_1(B_655) | ~v1_funct_1(A_654) | ~v1_relat_1(A_654))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.86/2.92  tff(c_6878, plain, (![B_655]: (r2_hidden('#skF_2'('#skF_6', B_655), '#skF_3') | B_655='#skF_6' | k1_relat_1(B_655)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_655) | ~v1_relat_1(B_655) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6838, c_6866])).
% 7.86/2.92  tff(c_6970, plain, (![B_662]: (r2_hidden('#skF_2'('#skF_6', B_662), '#skF_3') | B_662='#skF_6' | k1_relat_1(B_662)!='#skF_3' | ~v1_funct_1(B_662) | ~v1_relat_1(B_662))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_64, c_6838, c_6878])).
% 7.86/2.92  tff(c_6973, plain, (![B_662]: (m1_subset_1('#skF_2'('#skF_6', B_662), '#skF_3') | v1_xboole_0('#skF_3') | B_662='#skF_6' | k1_relat_1(B_662)!='#skF_3' | ~v1_funct_1(B_662) | ~v1_relat_1(B_662))), inference(resolution, [status(thm)], [c_6970, c_20])).
% 7.86/2.92  tff(c_6996, plain, (![B_666]: (m1_subset_1('#skF_2'('#skF_6', B_666), '#skF_3') | B_666='#skF_6' | k1_relat_1(B_666)!='#skF_3' | ~v1_funct_1(B_666) | ~v1_relat_1(B_666))), inference(negUnitSimplification, [status(thm)], [c_207, c_6973])).
% 7.86/2.92  tff(c_7058, plain, (![B_672]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_672))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_672)) | B_672='#skF_6' | k1_relat_1(B_672)!='#skF_3' | ~v1_funct_1(B_672) | ~v1_relat_1(B_672))), inference(resolution, [status(thm)], [c_6996, c_58])).
% 7.86/2.92  tff(c_7065, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7058, c_32])).
% 7.86/2.92  tff(c_7072, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_70, c_6841, c_177, c_64, c_6841, c_6838, c_7065])).
% 7.86/2.92  tff(c_133, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_120])).
% 7.86/2.92  tff(c_245, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_133, c_236])).
% 7.86/2.92  tff(c_5079, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_245])).
% 7.86/2.92  tff(c_5965, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5963, c_5079])).
% 7.86/2.92  tff(c_7098, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7072, c_5965])).
% 7.86/2.92  tff(c_7112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_7098])).
% 7.86/2.92  tff(c_7114, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_5977])).
% 7.86/2.92  tff(c_7127, plain, (![A_7]: (r1_tarski('#skF_5', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_7114, c_12])).
% 7.86/2.92  tff(c_7136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7127, c_5965])).
% 7.86/2.92  tff(c_7137, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_245])).
% 7.86/2.92  tff(c_7142, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7137, c_66])).
% 7.86/2.92  tff(c_7248, plain, (![A_678, B_679, C_680]: (k1_relset_1(A_678, B_679, C_680)=k1_relat_1(C_680) | ~m1_subset_1(C_680, k1_zfmisc_1(k2_zfmisc_1(A_678, B_679))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.86/2.92  tff(c_7431, plain, (![C_700]: (k1_relset_1('#skF_3', '#skF_4', C_700)=k1_relat_1(C_700) | ~m1_subset_1(C_700, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_7137, c_7248])).
% 7.86/2.92  tff(c_7450, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_7142, c_7431])).
% 7.86/2.92  tff(c_7720, plain, (![B_730, A_731, C_732]: (k1_xboole_0=B_730 | k1_relset_1(A_731, B_730, C_732)=A_731 | ~v1_funct_2(C_732, A_731, B_730) | ~m1_subset_1(C_732, k1_zfmisc_1(k2_zfmisc_1(A_731, B_730))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.86/2.92  tff(c_7723, plain, (![C_732]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_732)='#skF_3' | ~v1_funct_2(C_732, '#skF_3', '#skF_4') | ~m1_subset_1(C_732, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_7137, c_7720])).
% 7.86/2.92  tff(c_7790, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_7723])).
% 7.86/2.92  tff(c_7148, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_7137, c_14])).
% 7.86/2.92  tff(c_7273, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_7148])).
% 7.86/2.92  tff(c_7809, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7790, c_7273])).
% 7.86/2.92  tff(c_7818, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7790, c_7790, c_16])).
% 7.86/2.92  tff(c_7882, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7818, c_7137])).
% 7.86/2.92  tff(c_7884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7809, c_7882])).
% 7.86/2.92  tff(c_7983, plain, (![C_753]: (k1_relset_1('#skF_3', '#skF_4', C_753)='#skF_3' | ~v1_funct_2(C_753, '#skF_3', '#skF_4') | ~m1_subset_1(C_753, k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_7723])).
% 7.86/2.92  tff(c_7986, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_7142, c_7983])).
% 7.86/2.92  tff(c_8004, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_7450, c_7986])).
% 7.86/2.92  tff(c_7143, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7137, c_60])).
% 7.86/2.92  tff(c_7451, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_7143, c_7431])).
% 7.86/2.92  tff(c_7989, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_7143, c_7983])).
% 7.86/2.92  tff(c_8007, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_7451, c_7989])).
% 7.86/2.92  tff(c_8036, plain, (![A_754, B_755]: (r2_hidden('#skF_2'(A_754, B_755), k1_relat_1(A_754)) | B_755=A_754 | k1_relat_1(B_755)!=k1_relat_1(A_754) | ~v1_funct_1(B_755) | ~v1_relat_1(B_755) | ~v1_funct_1(A_754) | ~v1_relat_1(A_754))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.86/2.92  tff(c_8045, plain, (![B_755]: (r2_hidden('#skF_2'('#skF_6', B_755), '#skF_3') | B_755='#skF_6' | k1_relat_1(B_755)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_755) | ~v1_relat_1(B_755) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8007, c_8036])).
% 7.86/2.92  tff(c_8122, plain, (![B_761]: (r2_hidden('#skF_2'('#skF_6', B_761), '#skF_3') | B_761='#skF_6' | k1_relat_1(B_761)!='#skF_3' | ~v1_funct_1(B_761) | ~v1_relat_1(B_761))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_64, c_8007, c_8045])).
% 7.86/2.92  tff(c_8125, plain, (![B_761]: (m1_subset_1('#skF_2'('#skF_6', B_761), '#skF_3') | v1_xboole_0('#skF_3') | B_761='#skF_6' | k1_relat_1(B_761)!='#skF_3' | ~v1_funct_1(B_761) | ~v1_relat_1(B_761))), inference(resolution, [status(thm)], [c_8122, c_20])).
% 7.86/2.92  tff(c_8144, plain, (![B_763]: (m1_subset_1('#skF_2'('#skF_6', B_763), '#skF_3') | B_763='#skF_6' | k1_relat_1(B_763)!='#skF_3' | ~v1_funct_1(B_763) | ~v1_relat_1(B_763))), inference(negUnitSimplification, [status(thm)], [c_207, c_8125])).
% 7.86/2.92  tff(c_8523, plain, (![B_793]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_793))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_793)) | B_793='#skF_6' | k1_relat_1(B_793)!='#skF_3' | ~v1_funct_1(B_793) | ~v1_relat_1(B_793))), inference(resolution, [status(thm)], [c_8144, c_58])).
% 7.86/2.92  tff(c_8530, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8523, c_32])).
% 7.86/2.92  tff(c_8537, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_70, c_8004, c_177, c_64, c_8007, c_8004, c_8530])).
% 7.86/2.92  tff(c_7199, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7137, c_7137, c_246])).
% 7.86/2.92  tff(c_7200, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_7199])).
% 7.86/2.92  tff(c_8546, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8537, c_7200])).
% 7.86/2.92  tff(c_8560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_8546])).
% 7.86/2.92  tff(c_8562, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_7148])).
% 7.86/2.92  tff(c_8574, plain, (![A_7]: (r1_tarski('#skF_6', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_8562, c_12])).
% 7.86/2.92  tff(c_8584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8574, c_7200])).
% 7.86/2.92  tff(c_8585, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_7199])).
% 7.86/2.92  tff(c_8592, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8585, c_56])).
% 7.86/2.92  tff(c_7162, plain, (![A_673, B_674, D_675]: (r2_relset_1(A_673, B_674, D_675, D_675) | ~m1_subset_1(D_675, k1_zfmisc_1(k2_zfmisc_1(A_673, B_674))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.86/2.92  tff(c_8738, plain, (![D_804]: (r2_relset_1('#skF_3', '#skF_4', D_804, D_804) | ~m1_subset_1(D_804, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_7137, c_7162])).
% 7.86/2.92  tff(c_8740, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_7143, c_8738])).
% 7.86/2.92  tff(c_8753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8592, c_8740])).
% 7.86/2.92  tff(c_8755, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_148])).
% 7.86/2.92  tff(c_9113, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_9095])).
% 7.86/2.92  tff(c_9130, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_9026, c_9113])).
% 7.86/2.92  tff(c_9138, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_9130])).
% 7.86/2.92  tff(c_9424, plain, (![A_882, B_883]: (r2_hidden('#skF_2'(A_882, B_883), k1_relat_1(A_882)) | B_883=A_882 | k1_relat_1(B_883)!=k1_relat_1(A_882) | ~v1_funct_1(B_883) | ~v1_relat_1(B_883) | ~v1_funct_1(A_882) | ~v1_relat_1(A_882))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.86/2.92  tff(c_9433, plain, (![B_883]: (r2_hidden('#skF_2'('#skF_6', B_883), '#skF_3') | B_883='#skF_6' | k1_relat_1(B_883)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_883) | ~v1_relat_1(B_883) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9138, c_9424])).
% 7.86/2.92  tff(c_9453, plain, (![B_886]: (r2_hidden('#skF_2'('#skF_6', B_886), '#skF_3') | B_886='#skF_6' | k1_relat_1(B_886)!='#skF_3' | ~v1_funct_1(B_886) | ~v1_relat_1(B_886))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_64, c_9138, c_9433])).
% 7.86/2.92  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.86/2.92  tff(c_9459, plain, (![B_886]: (~v1_xboole_0('#skF_3') | B_886='#skF_6' | k1_relat_1(B_886)!='#skF_3' | ~v1_funct_1(B_886) | ~v1_relat_1(B_886))), inference(resolution, [status(thm)], [c_9453, c_2])).
% 7.86/2.92  tff(c_9465, plain, (![B_887]: (B_887='#skF_6' | k1_relat_1(B_887)!='#skF_3' | ~v1_funct_1(B_887) | ~v1_relat_1(B_887))), inference(demodulation, [status(thm), theory('equality')], [c_8755, c_9459])).
% 7.86/2.92  tff(c_9480, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_176, c_9465])).
% 7.86/2.92  tff(c_9490, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_9132, c_9480])).
% 7.86/2.92  tff(c_9501, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9490, c_56])).
% 7.86/2.92  tff(c_9512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8964, c_9501])).
% 7.86/2.92  tff(c_9513, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_9130])).
% 7.86/2.92  tff(c_9537, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_9513, c_12])).
% 7.86/2.92  tff(c_9535, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9513, c_9513, c_16])).
% 7.86/2.92  tff(c_8784, plain, (![B_807, A_808]: (B_807=A_808 | ~r1_tarski(B_807, A_808) | ~r1_tarski(A_808, B_807))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.86/2.92  tff(c_8793, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_133, c_8784])).
% 7.86/2.92  tff(c_9053, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_8793])).
% 7.86/2.92  tff(c_9554, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9535, c_9053])).
% 7.86/2.92  tff(c_9562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9537, c_9554])).
% 7.86/2.92  tff(c_9563, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_9127])).
% 7.86/2.92  tff(c_9588, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_9563, c_12])).
% 7.86/2.92  tff(c_9586, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9563, c_9563, c_16])).
% 7.86/2.92  tff(c_9634, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9586, c_9053])).
% 7.86/2.92  tff(c_9642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9588, c_9634])).
% 7.86/2.92  tff(c_9643, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_8793])).
% 7.86/2.92  tff(c_9650, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9643, c_60])).
% 7.86/2.92  tff(c_10089, plain, (![B_935, C_936, A_937]: (k1_xboole_0=B_935 | v1_funct_2(C_936, A_937, B_935) | k1_relset_1(A_937, B_935, C_936)!=A_937 | ~m1_subset_1(C_936, k1_zfmisc_1(k2_zfmisc_1(A_937, B_935))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.86/2.92  tff(c_10092, plain, (![C_936]: (k1_xboole_0='#skF_4' | v1_funct_2(C_936, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_936)!='#skF_3' | ~m1_subset_1(C_936, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_9643, c_10089])).
% 7.86/2.92  tff(c_10159, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_10092])).
% 7.86/2.92  tff(c_9660, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_9643, c_14])).
% 7.86/2.92  tff(c_9755, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_9660])).
% 7.86/2.92  tff(c_10172, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10159, c_9755])).
% 7.86/2.92  tff(c_10187, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10159, c_10159, c_16])).
% 7.86/2.92  tff(c_10251, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10187, c_9643])).
% 7.86/2.92  tff(c_10253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10172, c_10251])).
% 7.86/2.92  tff(c_10255, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_10092])).
% 7.86/2.92  tff(c_9962, plain, (![B_920, A_921, C_922]: (k1_xboole_0=B_920 | k1_relset_1(A_921, B_920, C_922)=A_921 | ~v1_funct_2(C_922, A_921, B_920) | ~m1_subset_1(C_922, k1_zfmisc_1(k2_zfmisc_1(A_921, B_920))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.86/2.92  tff(c_9965, plain, (![C_922]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_922)='#skF_3' | ~v1_funct_2(C_922, '#skF_3', '#skF_4') | ~m1_subset_1(C_922, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_9643, c_9962])).
% 7.86/2.92  tff(c_10257, plain, (![C_949]: (k1_relset_1('#skF_3', '#skF_4', C_949)='#skF_3' | ~v1_funct_2(C_949, '#skF_3', '#skF_4') | ~m1_subset_1(C_949, k1_zfmisc_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_10255, c_9965])).
% 7.86/2.92  tff(c_10260, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_9650, c_10257])).
% 7.86/2.92  tff(c_10278, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_9026, c_10260])).
% 7.86/2.92  tff(c_9649, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9643, c_66])).
% 7.86/2.92  tff(c_10263, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_9649, c_10257])).
% 7.86/2.92  tff(c_10281, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_9025, c_10263])).
% 7.86/2.92  tff(c_10424, plain, (![A_960, B_961]: (r2_hidden('#skF_2'(A_960, B_961), k1_relat_1(A_960)) | B_961=A_960 | k1_relat_1(B_961)!=k1_relat_1(A_960) | ~v1_funct_1(B_961) | ~v1_relat_1(B_961) | ~v1_funct_1(A_960) | ~v1_relat_1(A_960))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.86/2.92  tff(c_10433, plain, (![B_961]: (r2_hidden('#skF_2'('#skF_5', B_961), '#skF_3') | B_961='#skF_5' | k1_relat_1(B_961)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_961) | ~v1_relat_1(B_961) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10281, c_10424])).
% 7.86/2.92  tff(c_10493, plain, (![B_966]: (r2_hidden('#skF_2'('#skF_5', B_966), '#skF_3') | B_966='#skF_5' | k1_relat_1(B_966)!='#skF_3' | ~v1_funct_1(B_966) | ~v1_relat_1(B_966))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_70, c_10281, c_10433])).
% 7.86/2.92  tff(c_10499, plain, (![B_966]: (~v1_xboole_0('#skF_3') | B_966='#skF_5' | k1_relat_1(B_966)!='#skF_3' | ~v1_funct_1(B_966) | ~v1_relat_1(B_966))), inference(resolution, [status(thm)], [c_10493, c_2])).
% 7.86/2.92  tff(c_10505, plain, (![B_967]: (B_967='#skF_5' | k1_relat_1(B_967)!='#skF_3' | ~v1_funct_1(B_967) | ~v1_relat_1(B_967))), inference(demodulation, [status(thm), theory('equality')], [c_8755, c_10499])).
% 7.86/2.92  tff(c_10520, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_6')!='#skF_3' | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_177, c_10505])).
% 7.86/2.92  tff(c_10530, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_10278, c_10520])).
% 7.86/2.92  tff(c_8794, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_132, c_8784])).
% 7.86/2.92  tff(c_8975, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_8794])).
% 7.86/2.92  tff(c_9645, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9643, c_8975])).
% 7.86/2.92  tff(c_10539, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10530, c_9645])).
% 7.86/2.92  tff(c_10554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_10539])).
% 7.86/2.92  tff(c_10556, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_9660])).
% 7.86/2.92  tff(c_10575, plain, (![A_7]: (r1_tarski('#skF_6', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_10556, c_12])).
% 7.86/2.92  tff(c_10584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10575, c_9645])).
% 7.86/2.92  tff(c_10585, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_8794])).
% 7.86/2.92  tff(c_10591, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_10585, c_60])).
% 7.86/2.92  tff(c_10609, plain, (![A_968, B_969, C_970]: (k1_relset_1(A_968, B_969, C_970)=k1_relat_1(C_970) | ~m1_subset_1(C_970, k1_zfmisc_1(k2_zfmisc_1(A_968, B_969))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.86/2.92  tff(c_10881, plain, (![C_1001]: (k1_relset_1('#skF_3', '#skF_4', C_1001)=k1_relat_1(C_1001) | ~m1_subset_1(C_1001, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_10585, c_10609])).
% 7.86/2.92  tff(c_10901, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10591, c_10881])).
% 7.86/2.92  tff(c_11053, plain, (![B_1014, A_1015, C_1016]: (k1_xboole_0=B_1014 | k1_relset_1(A_1015, B_1014, C_1016)=A_1015 | ~v1_funct_2(C_1016, A_1015, B_1014) | ~m1_subset_1(C_1016, k1_zfmisc_1(k2_zfmisc_1(A_1015, B_1014))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.86/2.92  tff(c_11056, plain, (![C_1016]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_1016)='#skF_3' | ~v1_funct_2(C_1016, '#skF_3', '#skF_4') | ~m1_subset_1(C_1016, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_10585, c_11053])).
% 7.86/2.92  tff(c_11100, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_11056])).
% 7.86/2.92  tff(c_10598, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_10585, c_14])).
% 7.86/2.92  tff(c_10717, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_10598])).
% 7.86/2.92  tff(c_11118, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11100, c_10717])).
% 7.86/2.92  tff(c_11130, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11100, c_11100, c_16])).
% 7.86/2.92  tff(c_11220, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11130, c_10585])).
% 7.86/2.92  tff(c_11222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11118, c_11220])).
% 7.86/2.92  tff(c_11339, plain, (![C_1038]: (k1_relset_1('#skF_3', '#skF_4', C_1038)='#skF_3' | ~v1_funct_2(C_1038, '#skF_3', '#skF_4') | ~m1_subset_1(C_1038, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_11056])).
% 7.86/2.92  tff(c_11345, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_10591, c_11339])).
% 7.86/2.92  tff(c_11363, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10901, c_11345])).
% 7.86/2.92  tff(c_10590, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_10585, c_66])).
% 7.86/2.92  tff(c_10900, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10590, c_10881])).
% 7.86/2.92  tff(c_11342, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_10590, c_11339])).
% 7.86/2.92  tff(c_11360, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_10900, c_11342])).
% 7.86/2.92  tff(c_11389, plain, (![A_1039, B_1040]: (r2_hidden('#skF_2'(A_1039, B_1040), k1_relat_1(A_1039)) | B_1040=A_1039 | k1_relat_1(B_1040)!=k1_relat_1(A_1039) | ~v1_funct_1(B_1040) | ~v1_relat_1(B_1040) | ~v1_funct_1(A_1039) | ~v1_relat_1(A_1039))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.86/2.92  tff(c_11401, plain, (![B_1040]: (r2_hidden('#skF_2'('#skF_5', B_1040), '#skF_3') | B_1040='#skF_5' | k1_relat_1(B_1040)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_1040) | ~v1_relat_1(B_1040) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11360, c_11389])).
% 7.86/2.92  tff(c_11540, plain, (![B_1053]: (r2_hidden('#skF_2'('#skF_5', B_1053), '#skF_3') | B_1053='#skF_5' | k1_relat_1(B_1053)!='#skF_3' | ~v1_funct_1(B_1053) | ~v1_relat_1(B_1053))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_70, c_11360, c_11401])).
% 7.86/2.92  tff(c_11546, plain, (![B_1053]: (~v1_xboole_0('#skF_3') | B_1053='#skF_5' | k1_relat_1(B_1053)!='#skF_3' | ~v1_funct_1(B_1053) | ~v1_relat_1(B_1053))), inference(resolution, [status(thm)], [c_11540, c_2])).
% 7.86/2.92  tff(c_11552, plain, (![B_1054]: (B_1054='#skF_5' | k1_relat_1(B_1054)!='#skF_3' | ~v1_funct_1(B_1054) | ~v1_relat_1(B_1054))), inference(demodulation, [status(thm), theory('equality')], [c_8755, c_11546])).
% 7.86/2.92  tff(c_11567, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_6')!='#skF_3' | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_177, c_11552])).
% 7.86/2.92  tff(c_11579, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_11363, c_11567])).
% 7.86/2.92  tff(c_10588, plain, (r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10585, c_133])).
% 7.86/2.92  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.86/2.92  tff(c_10636, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_10588, c_6])).
% 7.86/2.92  tff(c_10656, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_10636])).
% 7.86/2.92  tff(c_11603, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11579, c_10656])).
% 7.86/2.92  tff(c_11621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_11603])).
% 7.86/2.92  tff(c_11623, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_10598])).
% 7.86/2.92  tff(c_11637, plain, (![A_7]: (r1_tarski('#skF_5', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_11623, c_12])).
% 7.86/2.92  tff(c_11646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11637, c_10656])).
% 7.86/2.92  tff(c_11647, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_10636])).
% 7.86/2.92  tff(c_11659, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11647, c_56])).
% 7.86/2.92  tff(c_11667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8964, c_11659])).
% 7.86/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/2.92  
% 7.86/2.92  Inference rules
% 7.86/2.92  ----------------------
% 7.86/2.92  #Ref     : 7
% 7.86/2.92  #Sup     : 2262
% 7.86/2.92  #Fact    : 0
% 7.86/2.92  #Define  : 0
% 7.86/2.92  #Split   : 59
% 7.86/2.92  #Chain   : 0
% 7.86/2.92  #Close   : 0
% 7.86/2.92  
% 7.86/2.92  Ordering : KBO
% 7.86/2.92  
% 7.86/2.92  Simplification rules
% 7.86/2.92  ----------------------
% 7.86/2.92  #Subsume      : 408
% 7.86/2.92  #Demod        : 3303
% 7.86/2.92  #Tautology    : 1363
% 7.86/2.92  #SimpNegUnit  : 247
% 7.86/2.92  #BackRed      : 804
% 7.86/2.92  
% 7.86/2.92  #Partial instantiations: 0
% 7.86/2.92  #Strategies tried      : 1
% 7.86/2.92  
% 7.86/2.92  Timing (in seconds)
% 7.86/2.92  ----------------------
% 7.86/2.93  Preprocessing        : 0.32
% 7.86/2.93  Parsing              : 0.17
% 7.86/2.93  CNF conversion       : 0.02
% 7.86/2.93  Main loop            : 1.79
% 7.86/2.93  Inferencing          : 0.58
% 7.86/2.93  Reduction            : 0.65
% 7.86/2.93  Demodulation         : 0.45
% 7.86/2.93  BG Simplification    : 0.06
% 7.86/2.93  Subsumption          : 0.33
% 7.86/2.93  Abstraction          : 0.07
% 7.86/2.93  MUC search           : 0.00
% 7.86/2.93  Cooper               : 0.00
% 7.86/2.93  Total                : 2.20
% 7.86/2.93  Index Insertion      : 0.00
% 7.86/2.93  Index Deletion       : 0.00
% 7.86/2.93  Index Matching       : 0.00
% 7.86/2.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
