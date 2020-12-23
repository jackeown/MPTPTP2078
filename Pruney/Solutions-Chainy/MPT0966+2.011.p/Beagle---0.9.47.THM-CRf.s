%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:09 EST 2020

% Result     : Theorem 11.06s
% Output     : CNFRefutation 11.51s
% Verified   : 
% Statistics : Number of formulae       :  399 (6026 expanded)
%              Number of leaves         :   35 (1903 expanded)
%              Depth                    :   20
%              Number of atoms          :  802 (16546 expanded)
%              Number of equality atoms :  246 (4987 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_124,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_30,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_113,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_119,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_113])).

tff(c_123,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_119])).

tff(c_25927,plain,(
    ! [C_1641,A_1642,B_1643] :
      ( v4_relat_1(C_1641,A_1642)
      | ~ m1_subset_1(C_1641,k1_zfmisc_1(k2_zfmisc_1(A_1642,B_1643))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_25942,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_25927])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26083,plain,(
    ! [A_1656,B_1657,C_1658] :
      ( k2_relset_1(A_1656,B_1657,C_1658) = k2_relat_1(C_1658)
      | ~ m1_subset_1(C_1658,k1_zfmisc_1(k2_zfmisc_1(A_1656,B_1657))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26098,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_26083])).

tff(c_58,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_26117,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26098,c_58])).

tff(c_26229,plain,(
    ! [C_1670,A_1671,B_1672] :
      ( m1_subset_1(C_1670,k1_zfmisc_1(k2_zfmisc_1(A_1671,B_1672)))
      | ~ r1_tarski(k2_relat_1(C_1670),B_1672)
      | ~ r1_tarski(k1_relat_1(C_1670),A_1671)
      | ~ v1_relat_1(C_1670) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_75,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_7277,plain,(
    ! [A_602,B_603,C_604] :
      ( k1_relset_1(A_602,B_603,C_604) = k1_relat_1(C_604)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(A_602,B_603))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7292,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_7277])).

tff(c_7541,plain,(
    ! [B_635,A_636,C_637] :
      ( k1_xboole_0 = B_635
      | k1_relset_1(A_636,B_635,C_637) = A_636
      | ~ v1_funct_2(C_637,A_636,B_635)
      | ~ m1_subset_1(C_637,k1_zfmisc_1(k2_zfmisc_1(A_636,B_635))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7551,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_7541])).

tff(c_7562,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_7292,c_7551])).

tff(c_7563,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_7562])).

tff(c_4658,plain,(
    ! [A_409,B_410,C_411] :
      ( k1_relset_1(A_409,B_410,C_411) = k1_relat_1(C_411)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_409,B_410))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4673,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_4658])).

tff(c_5122,plain,(
    ! [B_460,A_461,C_462] :
      ( k1_xboole_0 = B_460
      | k1_relset_1(A_461,B_460,C_462) = A_461
      | ~ v1_funct_2(C_462,A_461,B_460)
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(A_461,B_460))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5132,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_5122])).

tff(c_5143,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4673,c_5132])).

tff(c_5144,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5143])).

tff(c_4773,plain,(
    ! [A_418,B_419,C_420] :
      ( k2_relset_1(A_418,B_419,C_420) = k2_relat_1(C_420)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(k2_zfmisc_1(A_418,B_419))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4788,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_4773])).

tff(c_4798,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4788,c_58])).

tff(c_4844,plain,(
    ! [C_426,A_427,B_428] :
      ( m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(A_427,B_428)))
      | ~ r1_tarski(k2_relat_1(C_426),B_428)
      | ~ r1_tarski(k1_relat_1(C_426),A_427)
      | ~ v1_relat_1(C_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6551,plain,(
    ! [C_558,A_559,B_560] :
      ( r1_tarski(C_558,k2_zfmisc_1(A_559,B_560))
      | ~ r1_tarski(k2_relat_1(C_558),B_560)
      | ~ r1_tarski(k1_relat_1(C_558),A_559)
      | ~ v1_relat_1(C_558) ) ),
    inference(resolution,[status(thm)],[c_4844,c_16])).

tff(c_6553,plain,(
    ! [A_559] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_559,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_559)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4798,c_6551])).

tff(c_6568,plain,(
    ! [A_561] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_561,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_5144,c_6553])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4672,plain,(
    ! [A_409,B_410,A_6] :
      ( k1_relset_1(A_409,B_410,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_409,B_410)) ) ),
    inference(resolution,[status(thm)],[c_18,c_4658])).

tff(c_6574,plain,(
    ! [A_561] :
      ( k1_relset_1(A_561,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_561) ) ),
    inference(resolution,[status(thm)],[c_6568,c_4672])).

tff(c_6601,plain,(
    ! [A_562] :
      ( k1_relset_1(A_562,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5144,c_6574])).

tff(c_6606,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_6601])).

tff(c_6563,plain,(
    ! [A_559] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_559,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_559) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_5144,c_6553])).

tff(c_4982,plain,(
    ! [B_444,C_445,A_446] :
      ( k1_xboole_0 = B_444
      | v1_funct_2(C_445,A_446,B_444)
      | k1_relset_1(A_446,B_444,C_445) != A_446
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_446,B_444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6726,plain,(
    ! [B_569,A_570,A_571] :
      ( k1_xboole_0 = B_569
      | v1_funct_2(A_570,A_571,B_569)
      | k1_relset_1(A_571,B_569,A_570) != A_571
      | ~ r1_tarski(A_570,k2_zfmisc_1(A_571,B_569)) ) ),
    inference(resolution,[status(thm)],[c_18,c_4982])).

tff(c_6759,plain,(
    ! [A_559] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_559,'#skF_3')
      | k1_relset_1(A_559,'#skF_3','#skF_4') != A_559
      | ~ r1_tarski('#skF_1',A_559) ) ),
    inference(resolution,[status(thm)],[c_6563,c_6726])).

tff(c_6817,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6759])).

tff(c_6889,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6817,c_8])).

tff(c_4359,plain,(
    ! [B_365,A_366] :
      ( B_365 = A_366
      | ~ r1_tarski(B_365,A_366)
      | ~ r1_tarski(A_366,B_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4369,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_4359])).

tff(c_4467,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4369])).

tff(c_4796,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4788,c_4467])).

tff(c_7012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6889,c_4796])).

tff(c_7015,plain,(
    ! [A_581] :
      ( v1_funct_2('#skF_4',A_581,'#skF_3')
      | k1_relset_1(A_581,'#skF_3','#skF_4') != A_581
      | ~ r1_tarski('#skF_1',A_581) ) ),
    inference(splitRight,[status(thm)],[c_6759])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_66,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54])).

tff(c_4423,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_7021,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_7015,c_4423])).

tff(c_7026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6606,c_7021])).

tff(c_7027,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4369])).

tff(c_7199,plain,(
    ! [A_597,B_598,C_599] :
      ( k2_relset_1(A_597,B_598,C_599) = k2_relat_1(C_599)
      | ~ m1_subset_1(C_599,k1_zfmisc_1(k2_zfmisc_1(A_597,B_598))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7206,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_7199])).

tff(c_7215,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7027,c_7206])).

tff(c_7396,plain,(
    ! [C_617,A_618,B_619] :
      ( m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(A_618,B_619)))
      | ~ r1_tarski(k2_relat_1(C_617),B_619)
      | ~ r1_tarski(k1_relat_1(C_617),A_618)
      | ~ v1_relat_1(C_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9173,plain,(
    ! [C_751,A_752,B_753] :
      ( r1_tarski(C_751,k2_zfmisc_1(A_752,B_753))
      | ~ r1_tarski(k2_relat_1(C_751),B_753)
      | ~ r1_tarski(k1_relat_1(C_751),A_752)
      | ~ v1_relat_1(C_751) ) ),
    inference(resolution,[status(thm)],[c_7396,c_16])).

tff(c_9175,plain,(
    ! [A_752,B_753] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_752,B_753))
      | ~ r1_tarski('#skF_3',B_753)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_752)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7215,c_9173])).

tff(c_9189,plain,(
    ! [A_754,B_755] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_754,B_755))
      | ~ r1_tarski('#skF_3',B_755)
      | ~ r1_tarski('#skF_1',A_754) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_7563,c_9175])).

tff(c_7291,plain,(
    ! [A_602,B_603,A_6] :
      ( k1_relset_1(A_602,B_603,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_602,B_603)) ) ),
    inference(resolution,[status(thm)],[c_18,c_7277])).

tff(c_9195,plain,(
    ! [A_754,B_755] :
      ( k1_relset_1(A_754,B_755,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_755)
      | ~ r1_tarski('#skF_1',A_754) ) ),
    inference(resolution,[status(thm)],[c_9189,c_7291])).

tff(c_9261,plain,(
    ! [A_762,B_763] :
      ( k1_relset_1(A_762,B_763,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_763)
      | ~ r1_tarski('#skF_1',A_762) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7563,c_9195])).

tff(c_9276,plain,(
    ! [A_765] :
      ( k1_relset_1(A_765,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_765) ) ),
    inference(resolution,[status(thm)],[c_6,c_9261])).

tff(c_9281,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_9276])).

tff(c_9469,plain,(
    ! [C_777,A_778] :
      ( r1_tarski(C_777,k2_zfmisc_1(A_778,k2_relat_1(C_777)))
      | ~ r1_tarski(k1_relat_1(C_777),A_778)
      | ~ v1_relat_1(C_777) ) ),
    inference(resolution,[status(thm)],[c_6,c_9173])).

tff(c_9525,plain,(
    ! [A_778] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_778,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_778)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7215,c_9469])).

tff(c_9556,plain,(
    ! [A_778] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_778,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_778) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_7563,c_9525])).

tff(c_7685,plain,(
    ! [B_648,C_649,A_650] :
      ( k1_xboole_0 = B_648
      | v1_funct_2(C_649,A_650,B_648)
      | k1_relset_1(A_650,B_648,C_649) != A_650
      | ~ m1_subset_1(C_649,k1_zfmisc_1(k2_zfmisc_1(A_650,B_648))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_10159,plain,(
    ! [B_799,A_800,A_801] :
      ( k1_xboole_0 = B_799
      | v1_funct_2(A_800,A_801,B_799)
      | k1_relset_1(A_801,B_799,A_800) != A_801
      | ~ r1_tarski(A_800,k2_zfmisc_1(A_801,B_799)) ) ),
    inference(resolution,[status(thm)],[c_18,c_7685])).

tff(c_10194,plain,(
    ! [A_778] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_778,'#skF_3')
      | k1_relset_1(A_778,'#skF_3','#skF_4') != A_778
      | ~ r1_tarski('#skF_1',A_778) ) ),
    inference(resolution,[status(thm)],[c_9556,c_10159])).

tff(c_10554,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10194])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( v5_relat_1(B_14,A_13)
      | ~ r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_7222,plain,(
    ! [A_13] :
      ( v5_relat_1('#skF_4',A_13)
      | ~ r1_tarski('#skF_3',A_13)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7215,c_26])).

tff(c_7231,plain,(
    ! [A_13] :
      ( v5_relat_1('#skF_4',A_13)
      | ~ r1_tarski('#skF_3',A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_7222])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_7157,plain,(
    ! [C_593,A_594,B_595] :
      ( v4_relat_1(C_593,A_594)
      | ~ m1_subset_1(C_593,k1_zfmisc_1(k2_zfmisc_1(A_594,B_595))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7347,plain,(
    ! [A_612,A_613,B_614] :
      ( v4_relat_1(A_612,A_613)
      | ~ r1_tarski(A_612,k2_zfmisc_1(A_613,B_614)) ) ),
    inference(resolution,[status(thm)],[c_18,c_7157])).

tff(c_8038,plain,(
    ! [B_680,A_681,B_682] :
      ( v4_relat_1(k2_relat_1(B_680),A_681)
      | ~ v5_relat_1(B_680,k2_zfmisc_1(A_681,B_682))
      | ~ v1_relat_1(B_680) ) ),
    inference(resolution,[status(thm)],[c_28,c_7347])).

tff(c_8124,plain,(
    ! [B_689,A_690] :
      ( v4_relat_1(k2_relat_1(B_689),A_690)
      | ~ v5_relat_1(B_689,k1_xboole_0)
      | ~ v1_relat_1(B_689) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8038])).

tff(c_8133,plain,(
    ! [A_690] :
      ( v4_relat_1('#skF_3',A_690)
      | ~ v5_relat_1('#skF_4',k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7215,c_8124])).

tff(c_8140,plain,(
    ! [A_690] :
      ( v4_relat_1('#skF_3',A_690)
      | ~ v5_relat_1('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_8133])).

tff(c_8143,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8140])).

tff(c_8182,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7231,c_8143])).

tff(c_10598,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10554,c_8182])).

tff(c_10644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10598])).

tff(c_10647,plain,(
    ! [A_812] :
      ( v1_funct_2('#skF_4',A_812,'#skF_3')
      | k1_relset_1(A_812,'#skF_3','#skF_4') != A_812
      | ~ r1_tarski('#skF_1',A_812) ) ),
    inference(splitRight,[status(thm)],[c_10194])).

tff(c_10658,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_10647,c_4423])).

tff(c_10671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9281,c_10658])).

tff(c_10673,plain,(
    v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8140])).

tff(c_4447,plain,(
    ! [B_380,A_381] :
      ( r1_tarski(k2_relat_1(B_380),A_381)
      | ~ v5_relat_1(B_380,A_381)
      | ~ v1_relat_1(B_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7964,plain,(
    ! [B_677,A_678] :
      ( k2_relat_1(B_677) = A_678
      | ~ r1_tarski(A_678,k2_relat_1(B_677))
      | ~ v5_relat_1(B_677,A_678)
      | ~ v1_relat_1(B_677) ) ),
    inference(resolution,[status(thm)],[c_4447,c_2])).

tff(c_7967,plain,(
    ! [A_678] :
      ( k2_relat_1('#skF_4') = A_678
      | ~ r1_tarski(A_678,'#skF_3')
      | ~ v5_relat_1('#skF_4',A_678)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7215,c_7964])).

tff(c_7988,plain,(
    ! [A_678] :
      ( A_678 = '#skF_3'
      | ~ r1_tarski(A_678,'#skF_3')
      | ~ v5_relat_1('#skF_4',A_678) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_7215,c_7967])).

tff(c_10689,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_10673,c_7988])).

tff(c_10700,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10689])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4425,plain,(
    ! [C_376,B_377,A_378] :
      ( v5_relat_1(C_376,B_377)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(k2_zfmisc_1(A_378,B_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4461,plain,(
    ! [C_383,B_384] :
      ( v5_relat_1(C_383,B_384)
      | ~ m1_subset_1(C_383,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4425])).

tff(c_4465,plain,(
    ! [A_6,B_384] :
      ( v5_relat_1(A_6,B_384)
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_4461])).

tff(c_7225,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_3',A_13)
      | ~ v5_relat_1('#skF_4',A_13)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7215,c_28])).

tff(c_7243,plain,(
    ! [A_601] :
      ( r1_tarski('#skF_3',A_601)
      | ~ v5_relat_1('#skF_4',A_601) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_7225])).

tff(c_7267,plain,(
    ! [B_384] :
      ( r1_tarski('#skF_3',B_384)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4465,c_7243])).

tff(c_7298,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7267])).

tff(c_10766,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10700,c_7298])).

tff(c_7417,plain,(
    ! [C_617,A_4] :
      ( m1_subset_1(C_617,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_617),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_617),A_4)
      | ~ v1_relat_1(C_617) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_7396])).

tff(c_11124,plain,(
    ! [C_826,A_827] :
      ( m1_subset_1(C_826,k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(k2_relat_1(C_826),'#skF_3')
      | ~ r1_tarski(k1_relat_1(C_826),A_827)
      | ~ v1_relat_1(C_826) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10700,c_10700,c_7417])).

tff(c_11128,plain,(
    ! [A_827] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski('#skF_3','#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_827)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7215,c_11124])).

tff(c_11135,plain,(
    ! [A_827] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski('#skF_1',A_827) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_7563,c_6,c_11128])).

tff(c_11148,plain,(
    ! [A_830] : ~ r1_tarski('#skF_1',A_830) ),
    inference(splitLeft,[status(thm)],[c_11135])).

tff(c_11153,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_11148])).

tff(c_11154,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11135])).

tff(c_11160,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_11154,c_16])).

tff(c_11167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10766,c_11160])).

tff(c_11168,plain,(
    ! [B_384] : r1_tarski('#skF_3',B_384) ),
    inference(splitRight,[status(thm)],[c_7267])).

tff(c_11174,plain,(
    ! [B_831] : r1_tarski('#skF_3',B_831) ),
    inference(splitRight,[status(thm)],[c_7267])).

tff(c_4374,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_4359])).

tff(c_11196,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11174,c_4374])).

tff(c_11169,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7267])).

tff(c_11224,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11196,c_11169])).

tff(c_11226,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_11224,c_2])).

tff(c_11232,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11168,c_11226])).

tff(c_11213,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11196,c_11196,c_14])).

tff(c_11314,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11232,c_11232,c_11213])).

tff(c_42,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_29,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_70,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_7173,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_7176,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_7173])).

tff(c_7180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7176])).

tff(c_7181,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29 ) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_11200,plain,(
    ! [A_29] :
      ( v1_funct_2('#skF_3',A_29,'#skF_3')
      | A_29 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11196,c_11196,c_11196,c_7181])).

tff(c_11423,plain,(
    ! [A_843] :
      ( v1_funct_2('#skF_4',A_843,'#skF_4')
      | A_843 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11232,c_11232,c_11232,c_11200])).

tff(c_11245,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11232,c_4423])).

tff(c_11430,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11423,c_11245])).

tff(c_103,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_107,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_103])).

tff(c_4368,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_4359])).

tff(c_7130,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4368])).

tff(c_11439,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11430,c_7130])).

tff(c_11444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11314,c_11439])).

tff(c_11445,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4368])).

tff(c_11449,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11445,c_60])).

tff(c_11601,plain,(
    ! [A_859,B_860,C_861] :
      ( k1_relset_1(A_859,B_860,C_861) = k1_relat_1(C_861)
      | ~ m1_subset_1(C_861,k1_zfmisc_1(k2_zfmisc_1(A_859,B_860))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_11692,plain,(
    ! [C_868] :
      ( k1_relset_1('#skF_1','#skF_2',C_868) = k1_relat_1(C_868)
      | ~ m1_subset_1(C_868,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11445,c_11601])).

tff(c_11700,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11449,c_11692])).

tff(c_21794,plain,(
    ! [B_1365,A_1366,C_1367] :
      ( k1_xboole_0 = B_1365
      | k1_relset_1(A_1366,B_1365,C_1367) = A_1366
      | ~ v1_funct_2(C_1367,A_1366,B_1365)
      | ~ m1_subset_1(C_1367,k1_zfmisc_1(k2_zfmisc_1(A_1366,B_1365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_21800,plain,(
    ! [C_1367] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_1367) = '#skF_1'
      | ~ v1_funct_2(C_1367,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1367,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11445,c_21794])).

tff(c_21824,plain,(
    ! [C_1370] :
      ( k1_relset_1('#skF_1','#skF_2',C_1370) = '#skF_1'
      | ~ v1_funct_2(C_1370,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1370,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_21800])).

tff(c_21827,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_11449,c_21824])).

tff(c_21834,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_11700,c_21827])).

tff(c_12451,plain,(
    ! [B_934,A_935,C_936] :
      ( k1_xboole_0 = B_934
      | k1_relset_1(A_935,B_934,C_936) = A_935
      | ~ v1_funct_2(C_936,A_935,B_934)
      | ~ m1_subset_1(C_936,k1_zfmisc_1(k2_zfmisc_1(A_935,B_934))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12457,plain,(
    ! [C_936] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_936) = '#skF_1'
      | ~ v1_funct_2(C_936,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_936,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11445,c_12451])).

tff(c_12526,plain,(
    ! [C_944] :
      ( k1_relset_1('#skF_1','#skF_2',C_944) = '#skF_1'
      | ~ v1_funct_2(C_944,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_944,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_12457])).

tff(c_12532,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_11449,c_12526])).

tff(c_12542,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_11700,c_12532])).

tff(c_11883,plain,(
    ! [A_886,B_887,C_888] :
      ( k2_relset_1(A_886,B_887,C_888) = k2_relat_1(C_888)
      | ~ m1_subset_1(C_888,k1_zfmisc_1(k2_zfmisc_1(A_886,B_887))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_11920,plain,(
    ! [C_893] :
      ( k2_relset_1('#skF_1','#skF_2',C_893) = k2_relat_1(C_893)
      | ~ m1_subset_1(C_893,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11445,c_11883])).

tff(c_11923,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11449,c_11920])).

tff(c_11929,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7027,c_11923])).

tff(c_12192,plain,(
    ! [C_914,A_915,B_916] :
      ( m1_subset_1(C_914,k1_zfmisc_1(k2_zfmisc_1(A_915,B_916)))
      | ~ r1_tarski(k2_relat_1(C_914),B_916)
      | ~ r1_tarski(k1_relat_1(C_914),A_915)
      | ~ v1_relat_1(C_914) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_13851,plain,(
    ! [C_1026,A_1027,B_1028] :
      ( r1_tarski(C_1026,k2_zfmisc_1(A_1027,B_1028))
      | ~ r1_tarski(k2_relat_1(C_1026),B_1028)
      | ~ r1_tarski(k1_relat_1(C_1026),A_1027)
      | ~ v1_relat_1(C_1026) ) ),
    inference(resolution,[status(thm)],[c_12192,c_16])).

tff(c_13853,plain,(
    ! [A_1027,B_1028] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1027,B_1028))
      | ~ r1_tarski('#skF_3',B_1028)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1027)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11929,c_13851])).

tff(c_14032,plain,(
    ! [A_1035,B_1036] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1035,B_1036))
      | ~ r1_tarski('#skF_3',B_1036)
      | ~ r1_tarski('#skF_1',A_1035) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_12542,c_13853])).

tff(c_11615,plain,(
    ! [A_859,B_860,A_6] :
      ( k1_relset_1(A_859,B_860,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_859,B_860)) ) ),
    inference(resolution,[status(thm)],[c_18,c_11601])).

tff(c_14038,plain,(
    ! [A_1035,B_1036] :
      ( k1_relset_1(A_1035,B_1036,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_1036)
      | ~ r1_tarski('#skF_1',A_1035) ) ),
    inference(resolution,[status(thm)],[c_14032,c_11615])).

tff(c_14098,plain,(
    ! [A_1041,B_1042] :
      ( k1_relset_1(A_1041,B_1042,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_1042)
      | ~ r1_tarski('#skF_1',A_1041) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12542,c_14038])).

tff(c_14178,plain,(
    ! [A_1049] :
      ( k1_relset_1(A_1049,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_1049) ) ),
    inference(resolution,[status(thm)],[c_6,c_14098])).

tff(c_14183,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_14178])).

tff(c_40,plain,(
    ! [C_28,A_26,B_27] :
      ( m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ r1_tarski(k2_relat_1(C_28),B_27)
      | ~ r1_tarski(k1_relat_1(C_28),A_26)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12320,plain,(
    ! [B_920,C_921,A_922] :
      ( k1_xboole_0 = B_920
      | v1_funct_2(C_921,A_922,B_920)
      | k1_relset_1(A_922,B_920,C_921) != A_922
      | ~ m1_subset_1(C_921,k1_zfmisc_1(k2_zfmisc_1(A_922,B_920))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_15984,plain,(
    ! [B_1097,C_1098,A_1099] :
      ( k1_xboole_0 = B_1097
      | v1_funct_2(C_1098,A_1099,B_1097)
      | k1_relset_1(A_1099,B_1097,C_1098) != A_1099
      | ~ r1_tarski(k2_relat_1(C_1098),B_1097)
      | ~ r1_tarski(k1_relat_1(C_1098),A_1099)
      | ~ v1_relat_1(C_1098) ) ),
    inference(resolution,[status(thm)],[c_40,c_12320])).

tff(c_15997,plain,(
    ! [B_1097,A_1099] :
      ( k1_xboole_0 = B_1097
      | v1_funct_2('#skF_4',A_1099,B_1097)
      | k1_relset_1(A_1099,B_1097,'#skF_4') != A_1099
      | ~ r1_tarski('#skF_3',B_1097)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1099)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11929,c_15984])).

tff(c_16619,plain,(
    ! [B_1113,A_1114] :
      ( k1_xboole_0 = B_1113
      | v1_funct_2('#skF_4',A_1114,B_1113)
      | k1_relset_1(A_1114,B_1113,'#skF_4') != A_1114
      | ~ r1_tarski('#skF_3',B_1113)
      | ~ r1_tarski('#skF_1',A_1114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_12542,c_15997])).

tff(c_16638,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_16619,c_4423])).

tff(c_16655,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_14183,c_16638])).

tff(c_11940,plain,(
    ! [A_13] :
      ( v5_relat_1('#skF_4',A_13)
      | ~ r1_tarski('#skF_3',A_13)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11929,c_26])).

tff(c_11951,plain,(
    ! [A_13] :
      ( v5_relat_1('#skF_4',A_13)
      | ~ r1_tarski('#skF_3',A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_11940])).

tff(c_11472,plain,(
    ! [C_844,A_845,B_846] :
      ( v4_relat_1(C_844,A_845)
      | ~ m1_subset_1(C_844,k1_zfmisc_1(k2_zfmisc_1(A_845,B_846))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_11616,plain,(
    ! [A_862,A_863,B_864] :
      ( v4_relat_1(A_862,A_863)
      | ~ r1_tarski(A_862,k2_zfmisc_1(A_863,B_864)) ) ),
    inference(resolution,[status(thm)],[c_18,c_11472])).

tff(c_12895,plain,(
    ! [B_965,A_966,B_967] :
      ( v4_relat_1(k2_relat_1(B_965),A_966)
      | ~ v5_relat_1(B_965,k2_zfmisc_1(A_966,B_967))
      | ~ v1_relat_1(B_965) ) ),
    inference(resolution,[status(thm)],[c_28,c_11616])).

tff(c_12977,plain,(
    ! [B_974,A_975] :
      ( v4_relat_1(k2_relat_1(B_974),A_975)
      | ~ v5_relat_1(B_974,k1_xboole_0)
      | ~ v1_relat_1(B_974) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_12895])).

tff(c_12989,plain,(
    ! [A_975] :
      ( v4_relat_1('#skF_3',A_975)
      | ~ v5_relat_1('#skF_4',k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11929,c_12977])).

tff(c_12997,plain,(
    ! [A_975] :
      ( v4_relat_1('#skF_3',A_975)
      | ~ v5_relat_1('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_12989])).

tff(c_13014,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_12997])).

tff(c_13021,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11951,c_13014])).

tff(c_16701,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16655,c_13021])).

tff(c_16755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16701])).

tff(c_16757,plain,(
    v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_12997])).

tff(c_12771,plain,(
    ! [B_958,A_959] :
      ( k2_relat_1(B_958) = A_959
      | ~ r1_tarski(A_959,k2_relat_1(B_958))
      | ~ v5_relat_1(B_958,A_959)
      | ~ v1_relat_1(B_958) ) ),
    inference(resolution,[status(thm)],[c_4447,c_2])).

tff(c_12774,plain,(
    ! [A_959] :
      ( k2_relat_1('#skF_4') = A_959
      | ~ r1_tarski(A_959,'#skF_3')
      | ~ v5_relat_1('#skF_4',A_959)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11929,c_12771])).

tff(c_12795,plain,(
    ! [A_959] :
      ( A_959 = '#skF_3'
      | ~ r1_tarski(A_959,'#skF_3')
      | ~ v5_relat_1('#skF_4',A_959) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_11929,c_12774])).

tff(c_16779,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16757,c_12795])).

tff(c_16790,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16779])).

tff(c_16848,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16790,c_8])).

tff(c_11731,plain,(
    ! [A_870] :
      ( k1_relset_1('#skF_1','#skF_2',A_870) = k1_relat_1(A_870)
      | ~ r1_tarski(A_870,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_11692])).

tff(c_11748,plain,(
    ! [B_14] :
      ( k1_relset_1('#skF_1','#skF_2',k2_relat_1(B_14)) = k1_relat_1(k2_relat_1(B_14))
      | ~ v5_relat_1(B_14,'#skF_4')
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_28,c_11731])).

tff(c_11934,plain,
    ( k1_relat_1(k2_relat_1('#skF_4')) = k1_relset_1('#skF_1','#skF_2','#skF_3')
    | ~ v5_relat_1('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11929,c_11748])).

tff(c_11947,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3')
    | ~ v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_11929,c_11934])).

tff(c_12091,plain,(
    ~ v5_relat_1('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_11947])).

tff(c_12098,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_11951,c_12091])).

tff(c_16981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16848,c_12098])).

tff(c_16983,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_11947])).

tff(c_11943,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_3',A_13)
      | ~ v5_relat_1('#skF_4',A_13)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11929,c_28])).

tff(c_11953,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_3',A_13)
      | ~ v5_relat_1('#skF_4',A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_11943])).

tff(c_16987,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_16983,c_11953])).

tff(c_17001,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_16987,c_2])).

tff(c_17009,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_17001])).

tff(c_17214,plain,(
    ! [B_1135,A_1136,C_1137] :
      ( k1_xboole_0 = B_1135
      | k1_relset_1(A_1136,B_1135,C_1137) = A_1136
      | ~ v1_funct_2(C_1137,A_1136,B_1135)
      | ~ m1_subset_1(C_1137,k1_zfmisc_1(k2_zfmisc_1(A_1136,B_1135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_17220,plain,(
    ! [C_1137] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_1137) = '#skF_1'
      | ~ v1_funct_2(C_1137,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1137,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11445,c_17214])).

tff(c_17260,plain,(
    ! [C_1139] :
      ( k1_relset_1('#skF_1','#skF_2',C_1139) = '#skF_1'
      | ~ v1_funct_2(C_1139,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1139,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_17220])).

tff(c_17266,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_11449,c_17260])).

tff(c_17275,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_11700,c_17266])).

tff(c_17024,plain,(
    ! [C_1123,A_1124,B_1125] :
      ( m1_subset_1(C_1123,k1_zfmisc_1(k2_zfmisc_1(A_1124,B_1125)))
      | ~ r1_tarski(k2_relat_1(C_1123),B_1125)
      | ~ r1_tarski(k1_relat_1(C_1123),A_1124)
      | ~ v1_relat_1(C_1123) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_relset_1(A_20,B_21,C_22) = k1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_19143,plain,(
    ! [A_1264,B_1265,C_1266] :
      ( k1_relset_1(A_1264,B_1265,C_1266) = k1_relat_1(C_1266)
      | ~ r1_tarski(k2_relat_1(C_1266),B_1265)
      | ~ r1_tarski(k1_relat_1(C_1266),A_1264)
      | ~ v1_relat_1(C_1266) ) ),
    inference(resolution,[status(thm)],[c_17024,c_36])).

tff(c_19145,plain,(
    ! [A_1264,B_1265] :
      ( k1_relset_1(A_1264,B_1265,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_1265)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1264)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11929,c_19143])).

tff(c_19159,plain,(
    ! [A_1267,B_1268] :
      ( k1_relset_1(A_1267,B_1268,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_1268)
      | ~ r1_tarski('#skF_1',A_1267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_17275,c_17275,c_19145])).

tff(c_19170,plain,(
    ! [A_1269] :
      ( k1_relset_1(A_1269,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_1269) ) ),
    inference(resolution,[status(thm)],[c_6,c_19159])).

tff(c_19175,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_19170])).

tff(c_17322,plain,(
    ! [B_1141,C_1142,A_1143] :
      ( k1_xboole_0 = B_1141
      | v1_funct_2(C_1142,A_1143,B_1141)
      | k1_relset_1(A_1143,B_1141,C_1142) != A_1143
      | ~ m1_subset_1(C_1142,k1_zfmisc_1(k2_zfmisc_1(A_1143,B_1141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_20279,plain,(
    ! [B_1299,C_1300,A_1301] :
      ( k1_xboole_0 = B_1299
      | v1_funct_2(C_1300,A_1301,B_1299)
      | k1_relset_1(A_1301,B_1299,C_1300) != A_1301
      | ~ r1_tarski(k2_relat_1(C_1300),B_1299)
      | ~ r1_tarski(k1_relat_1(C_1300),A_1301)
      | ~ v1_relat_1(C_1300) ) ),
    inference(resolution,[status(thm)],[c_40,c_17322])).

tff(c_20288,plain,(
    ! [B_1299,A_1301] :
      ( k1_xboole_0 = B_1299
      | v1_funct_2('#skF_4',A_1301,B_1299)
      | k1_relset_1(A_1301,B_1299,'#skF_4') != A_1301
      | ~ r1_tarski('#skF_3',B_1299)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1301)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11929,c_20279])).

tff(c_20800,plain,(
    ! [B_1317,A_1318] :
      ( k1_xboole_0 = B_1317
      | v1_funct_2('#skF_4',A_1318,B_1317)
      | k1_relset_1(A_1318,B_1317,'#skF_4') != A_1318
      | ~ r1_tarski('#skF_3',B_1317)
      | ~ r1_tarski('#skF_1',A_1318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_17275,c_20288])).

tff(c_20819,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_20800,c_4423])).

tff(c_20836,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_19175,c_20819])).

tff(c_7038,plain,(
    ! [A_582,B_583,A_584] :
      ( v5_relat_1(A_582,B_583)
      | ~ r1_tarski(A_582,k2_zfmisc_1(A_584,B_583)) ) ),
    inference(resolution,[status(thm)],[c_18,c_4425])).

tff(c_17528,plain,(
    ! [B_1162,B_1163,A_1164] :
      ( v5_relat_1(k2_relat_1(B_1162),B_1163)
      | ~ v5_relat_1(B_1162,k2_zfmisc_1(A_1164,B_1163))
      | ~ v1_relat_1(B_1162) ) ),
    inference(resolution,[status(thm)],[c_28,c_7038])).

tff(c_17618,plain,(
    ! [B_1171] :
      ( v5_relat_1(k2_relat_1(B_1171),k1_xboole_0)
      | ~ v5_relat_1(B_1171,k1_xboole_0)
      | ~ v1_relat_1(B_1171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_17528])).

tff(c_17626,plain,
    ( v5_relat_1('#skF_3',k1_xboole_0)
    | ~ v5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11929,c_17618])).

tff(c_17635,plain,
    ( v5_relat_1('#skF_3',k1_xboole_0)
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_17626])).

tff(c_17670,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_17635])).

tff(c_17677,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11951,c_17670])).

tff(c_20882,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20836,c_17677])).

tff(c_20931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20882])).

tff(c_20933,plain,(
    v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_17635])).

tff(c_4457,plain,(
    ! [B_380] :
      ( k2_relat_1(B_380) = k1_xboole_0
      | ~ v5_relat_1(B_380,k1_xboole_0)
      | ~ v1_relat_1(B_380) ) ),
    inference(resolution,[status(thm)],[c_4447,c_4374])).

tff(c_20952,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20933,c_4457])).

tff(c_20959,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_11929,c_20952])).

tff(c_17048,plain,(
    ! [C_1123,A_4] :
      ( m1_subset_1(C_1123,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_1123),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_1123),A_4)
      | ~ v1_relat_1(C_1123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_17024])).

tff(c_21489,plain,(
    ! [C_1339,A_1340] :
      ( m1_subset_1(C_1339,k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(k2_relat_1(C_1339),'#skF_3')
      | ~ r1_tarski(k1_relat_1(C_1339),A_1340)
      | ~ v1_relat_1(C_1339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20959,c_20959,c_17048])).

tff(c_21493,plain,(
    ! [A_1340] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski('#skF_3','#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1340)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11929,c_21489])).

tff(c_21500,plain,(
    ! [A_1340] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski('#skF_1',A_1340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_17275,c_6,c_21493])).

tff(c_21628,plain,(
    ! [A_1359] : ~ r1_tarski('#skF_1',A_1359) ),
    inference(splitLeft,[status(thm)],[c_21500])).

tff(c_21633,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_21628])).

tff(c_21634,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_21500])).

tff(c_21644,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_21634,c_16])).

tff(c_21654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17009,c_21644])).

tff(c_21655,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_17001])).

tff(c_21664,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21655,c_11929])).

tff(c_21685,plain,(
    ! [C_1360,A_1361,B_1362] :
      ( m1_subset_1(C_1360,k1_zfmisc_1(k2_zfmisc_1(A_1361,B_1362)))
      | ~ r1_tarski(k2_relat_1(C_1360),B_1362)
      | ~ r1_tarski(k1_relat_1(C_1360),A_1361)
      | ~ v1_relat_1(C_1360) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24053,plain,(
    ! [A_1508,B_1509,C_1510] :
      ( k1_relset_1(A_1508,B_1509,C_1510) = k1_relat_1(C_1510)
      | ~ r1_tarski(k2_relat_1(C_1510),B_1509)
      | ~ r1_tarski(k1_relat_1(C_1510),A_1508)
      | ~ v1_relat_1(C_1510) ) ),
    inference(resolution,[status(thm)],[c_21685,c_36])).

tff(c_24055,plain,(
    ! [A_1508,B_1509] :
      ( k1_relset_1(A_1508,B_1509,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_4',B_1509)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1508)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_24053])).

tff(c_24340,plain,(
    ! [A_1518,B_1519] :
      ( k1_relset_1(A_1518,B_1519,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_4',B_1519)
      | ~ r1_tarski('#skF_1',A_1518) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_21834,c_21834,c_24055])).

tff(c_24423,plain,(
    ! [A_1526] :
      ( k1_relset_1(A_1526,'#skF_4','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_1526) ) ),
    inference(resolution,[status(thm)],[c_6,c_24340])).

tff(c_24428,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_24423])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11463,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11445,c_10])).

tff(c_11469,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_11463])).

tff(c_11498,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11469])).

tff(c_23799,plain,(
    ! [C_1495,A_1496,B_1497] :
      ( r1_tarski(C_1495,k2_zfmisc_1(A_1496,B_1497))
      | ~ r1_tarski(k2_relat_1(C_1495),B_1497)
      | ~ r1_tarski(k1_relat_1(C_1495),A_1496)
      | ~ v1_relat_1(C_1495) ) ),
    inference(resolution,[status(thm)],[c_21685,c_16])).

tff(c_24456,plain,(
    ! [C_1528,A_1529] :
      ( r1_tarski(C_1528,k2_zfmisc_1(A_1529,k2_relat_1(C_1528)))
      | ~ r1_tarski(k1_relat_1(C_1528),A_1529)
      | ~ v1_relat_1(C_1528) ) ),
    inference(resolution,[status(thm)],[c_6,c_23799])).

tff(c_24519,plain,(
    ! [A_1529] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1529,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1529)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21664,c_24456])).

tff(c_24554,plain,(
    ! [A_1529] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1529,'#skF_4'))
      | ~ r1_tarski('#skF_1',A_1529) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_21834,c_24519])).

tff(c_21895,plain,(
    ! [B_1374,C_1375,A_1376] :
      ( k1_xboole_0 = B_1374
      | v1_funct_2(C_1375,A_1376,B_1374)
      | k1_relset_1(A_1376,B_1374,C_1375) != A_1376
      | ~ m1_subset_1(C_1375,k1_zfmisc_1(k2_zfmisc_1(A_1376,B_1374))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_25005,plain,(
    ! [B_1543,A_1544,A_1545] :
      ( k1_xboole_0 = B_1543
      | v1_funct_2(A_1544,A_1545,B_1543)
      | k1_relset_1(A_1545,B_1543,A_1544) != A_1545
      | ~ r1_tarski(A_1544,k2_zfmisc_1(A_1545,B_1543)) ) ),
    inference(resolution,[status(thm)],[c_18,c_21895])).

tff(c_25008,plain,(
    ! [A_1529] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_4',A_1529,'#skF_4')
      | k1_relset_1(A_1529,'#skF_4','#skF_4') != A_1529
      | ~ r1_tarski('#skF_1',A_1529) ) ),
    inference(resolution,[status(thm)],[c_24554,c_25005])).

tff(c_25152,plain,(
    ! [A_1550] :
      ( v1_funct_2('#skF_4',A_1550,'#skF_4')
      | k1_relset_1(A_1550,'#skF_4','#skF_4') != A_1550
      | ~ r1_tarski('#skF_1',A_1550) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11498,c_25008])).

tff(c_21666,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21655,c_4423])).

tff(c_25158,plain,
    ( k1_relset_1('#skF_1','#skF_4','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_25152,c_21666])).

tff(c_25166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_24428,c_25158])).

tff(c_25168,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11469])).

tff(c_25167,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11469])).

tff(c_25186,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25168,c_25167])).

tff(c_25179,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25167,c_25167,c_14])).

tff(c_25269,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25186,c_25186,c_25179])).

tff(c_25388,plain,(
    ! [A_1574,A_1575,B_1576] :
      ( v4_relat_1(A_1574,A_1575)
      | ~ r1_tarski(A_1574,k2_zfmisc_1(A_1575,B_1576)) ) ),
    inference(resolution,[status(thm)],[c_18,c_11472])).

tff(c_25415,plain,(
    ! [A_1575,B_1576] : v4_relat_1(k2_zfmisc_1(A_1575,B_1576),A_1575) ),
    inference(resolution,[status(thm)],[c_6,c_25388])).

tff(c_4399,plain,(
    ! [B_370,A_371] :
      ( r1_tarski(k1_relat_1(B_370),A_371)
      | ~ v4_relat_1(B_370,A_371)
      | ~ v1_relat_1(B_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4409,plain,(
    ! [B_370] :
      ( k1_relat_1(B_370) = k1_xboole_0
      | ~ v4_relat_1(B_370,k1_xboole_0)
      | ~ v1_relat_1(B_370) ) ),
    inference(resolution,[status(thm)],[c_4399,c_4374])).

tff(c_25174,plain,(
    ! [B_370] :
      ( k1_relat_1(B_370) = '#skF_1'
      | ~ v4_relat_1(B_370,'#skF_1')
      | ~ v1_relat_1(B_370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25167,c_25167,c_4409])).

tff(c_25506,plain,(
    ! [B_1584] :
      ( k1_relat_1(B_1584) = '#skF_4'
      | ~ v4_relat_1(B_1584,'#skF_4')
      | ~ v1_relat_1(B_1584) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25186,c_25186,c_25174])).

tff(c_25510,plain,(
    ! [B_1576] :
      ( k1_relat_1(k2_zfmisc_1('#skF_4',B_1576)) = '#skF_4'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4',B_1576)) ) ),
    inference(resolution,[status(thm)],[c_25415,c_25506])).

tff(c_25521,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_25269,c_25510])).

tff(c_25177,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25167,c_25167,c_12])).

tff(c_25245,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25186,c_25186,c_25177])).

tff(c_25301,plain,(
    ! [A_1556,B_1557,C_1558] :
      ( k1_relset_1(A_1556,B_1557,C_1558) = k1_relat_1(C_1558)
      | ~ m1_subset_1(C_1558,k1_zfmisc_1(k2_zfmisc_1(A_1556,B_1557))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_25717,plain,(
    ! [A_1607,C_1608] :
      ( k1_relset_1(A_1607,'#skF_4',C_1608) = k1_relat_1(C_1608)
      | ~ m1_subset_1(C_1608,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25245,c_25301])).

tff(c_25719,plain,(
    ! [A_1607] : k1_relset_1(A_1607,'#skF_4','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11449,c_25717])).

tff(c_25724,plain,(
    ! [A_1607] : k1_relset_1(A_1607,'#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25521,c_25719])).

tff(c_76,plain,(
    ! [B_36] : k2_zfmisc_1(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_30])).

tff(c_7068,plain,(
    ! [A_584,B_583] : v5_relat_1(k2_zfmisc_1(A_584,B_583),B_583) ),
    inference(resolution,[status(thm)],[c_6,c_7038])).

tff(c_7091,plain,(
    ! [B_591] :
      ( k2_relat_1(B_591) = k1_xboole_0
      | ~ v5_relat_1(B_591,k1_xboole_0)
      | ~ v1_relat_1(B_591) ) ),
    inference(resolution,[status(thm)],[c_4447,c_4374])).

tff(c_7095,plain,(
    ! [A_584] :
      ( k2_relat_1(k2_zfmisc_1(A_584,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_584,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_7068,c_7091])).

tff(c_7106,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12,c_12,c_7095])).

tff(c_25169,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25167,c_25167,c_7106])).

tff(c_25208,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25186,c_25186,c_25169])).

tff(c_25181,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25167,c_8])).

tff(c_25228,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25186,c_25181])).

tff(c_25376,plain,(
    ! [A_1571,B_1572,C_1573] :
      ( k2_relset_1(A_1571,B_1572,C_1573) = k2_relat_1(C_1573)
      | ~ m1_subset_1(C_1573,k1_zfmisc_1(k2_zfmisc_1(A_1571,B_1572))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_25761,plain,(
    ! [A_1614,B_1615,A_1616] :
      ( k2_relset_1(A_1614,B_1615,A_1616) = k2_relat_1(A_1616)
      | ~ r1_tarski(A_1616,k2_zfmisc_1(A_1614,B_1615)) ) ),
    inference(resolution,[status(thm)],[c_18,c_25376])).

tff(c_25771,plain,(
    ! [A_1614,B_1615] : k2_relset_1(A_1614,B_1615,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_25228,c_25761])).

tff(c_25785,plain,(
    ! [A_1614,B_1615] : k2_relset_1(A_1614,B_1615,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25208,c_25771])).

tff(c_25194,plain,(
    k2_relset_1('#skF_4','#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25186,c_7027])).

tff(c_25789,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25785,c_25194])).

tff(c_46,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_68,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_25647,plain,(
    ! [C_1597,B_1598] :
      ( v1_funct_2(C_1597,'#skF_4',B_1598)
      | k1_relset_1('#skF_4',B_1598,C_1597) != '#skF_4'
      | ~ m1_subset_1(C_1597,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25168,c_25168,c_25168,c_25168,c_68])).

tff(c_25655,plain,(
    ! [B_1599] :
      ( v1_funct_2('#skF_4','#skF_4',B_1599)
      | k1_relset_1('#skF_4',B_1599,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_11449,c_25647])).

tff(c_25195,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25186,c_4423])).

tff(c_25671,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_25655,c_25195])).

tff(c_25797,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25789,c_25671])).

tff(c_25802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25724,c_25797])).

tff(c_25803,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_26244,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26229,c_25803])).

tff(c_26263,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_26117,c_26244])).

tff(c_26270,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_26263])).

tff(c_26274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_25942,c_26270])).

tff(c_26275,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_26277,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26275,c_8])).

tff(c_26289,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26275,c_26275,c_14])).

tff(c_26276,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_26282,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26275,c_26276])).

tff(c_26319,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26289,c_26282,c_60])).

tff(c_26321,plain,(
    ! [A_1678,B_1679] :
      ( r1_tarski(A_1678,B_1679)
      | ~ m1_subset_1(A_1678,k1_zfmisc_1(B_1679)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26329,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_26319,c_26321])).

tff(c_26341,plain,(
    ! [B_1682,A_1683] :
      ( B_1682 = A_1683
      | ~ r1_tarski(B_1682,A_1683)
      | ~ r1_tarski(A_1683,B_1682) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26343,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_26329,c_26341])).

tff(c_26352,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26277,c_26343])).

tff(c_26360,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26352,c_26319])).

tff(c_26365,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26352,c_26352,c_26289])).

tff(c_26478,plain,(
    ! [C_1694,A_1695,B_1696] :
      ( v4_relat_1(C_1694,A_1695)
      | ~ m1_subset_1(C_1694,k1_zfmisc_1(k2_zfmisc_1(A_1695,B_1696))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26528,plain,(
    ! [A_1707,A_1708,B_1709] :
      ( v4_relat_1(A_1707,A_1708)
      | ~ r1_tarski(A_1707,k2_zfmisc_1(A_1708,B_1709)) ) ),
    inference(resolution,[status(thm)],[c_18,c_26478])).

tff(c_26550,plain,(
    ! [A_1708,B_1709] : v4_relat_1(k2_zfmisc_1(A_1708,B_1709),A_1708) ),
    inference(resolution,[status(thm)],[c_6,c_26528])).

tff(c_26515,plain,(
    ! [B_1705,A_1706] :
      ( r1_tarski(k1_relat_1(B_1705),A_1706)
      | ~ v4_relat_1(B_1705,A_1706)
      | ~ v1_relat_1(B_1705) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26354,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26277,c_26341])).

tff(c_26440,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26352,c_26352,c_26354])).

tff(c_26560,plain,(
    ! [B_1712] :
      ( k1_relat_1(B_1712) = '#skF_4'
      | ~ v4_relat_1(B_1712,'#skF_4')
      | ~ v1_relat_1(B_1712) ) ),
    inference(resolution,[status(thm)],[c_26515,c_26440])).

tff(c_26564,plain,(
    ! [B_1709] :
      ( k1_relat_1(k2_zfmisc_1('#skF_4',B_1709)) = '#skF_4'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4',B_1709)) ) ),
    inference(resolution,[status(thm)],[c_26550,c_26560])).

tff(c_26575,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26365,c_26564])).

tff(c_26811,plain,(
    ! [A_1739,B_1740,C_1741] :
      ( k1_relset_1(A_1739,B_1740,C_1741) = k1_relat_1(C_1741)
      | ~ m1_subset_1(C_1741,k1_zfmisc_1(k2_zfmisc_1(A_1739,B_1740))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26850,plain,(
    ! [B_1746,C_1747] :
      ( k1_relset_1('#skF_4',B_1746,C_1747) = k1_relat_1(C_1747)
      | ~ m1_subset_1(C_1747,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26365,c_26811])).

tff(c_26852,plain,(
    ! [B_1746] : k1_relset_1('#skF_4',B_1746,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26360,c_26850])).

tff(c_26857,plain,(
    ! [B_1746] : k1_relset_1('#skF_4',B_1746,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26575,c_26852])).

tff(c_26368,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26352,c_26275])).

tff(c_27122,plain,(
    ! [C_1779,B_1780] :
      ( v1_funct_2(C_1779,'#skF_4',B_1780)
      | k1_relset_1('#skF_4',B_1780,C_1779) != '#skF_4'
      | ~ m1_subset_1(C_1779,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26368,c_26368,c_26368,c_26368,c_68])).

tff(c_27124,plain,(
    ! [B_1780] :
      ( v1_funct_2('#skF_4','#skF_4',B_1780)
      | k1_relset_1('#skF_4',B_1780,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_26360,c_27122])).

tff(c_27130,plain,(
    ! [B_1780] : v1_funct_2('#skF_4','#skF_4',B_1780) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26857,c_27124])).

tff(c_26379,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26352,c_26352,c_66])).

tff(c_26380,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26379])).

tff(c_27135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27130,c_26380])).

tff(c_27136,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_26379])).

tff(c_27212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26360,c_26365,c_27136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.06/4.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.16/4.46  
% 11.16/4.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.44/4.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.44/4.46  
% 11.44/4.46  %Foreground sorts:
% 11.44/4.46  
% 11.44/4.46  
% 11.44/4.46  %Background operators:
% 11.44/4.46  
% 11.44/4.46  
% 11.44/4.46  %Foreground operators:
% 11.44/4.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.44/4.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.44/4.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.44/4.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.44/4.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.44/4.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.44/4.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.44/4.46  tff('#skF_2', type, '#skF_2': $i).
% 11.44/4.46  tff('#skF_3', type, '#skF_3': $i).
% 11.44/4.46  tff('#skF_1', type, '#skF_1': $i).
% 11.44/4.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.44/4.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.44/4.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.44/4.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.44/4.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.44/4.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.44/4.46  tff('#skF_4', type, '#skF_4': $i).
% 11.44/4.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.44/4.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.44/4.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.44/4.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.44/4.46  
% 11.51/4.51  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.51/4.51  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 11.51/4.51  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.51/4.51  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.51/4.51  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 11.51/4.51  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.51/4.51  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 11.51/4.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.51/4.51  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.51/4.51  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.51/4.51  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.51/4.51  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.51/4.51  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 11.51/4.51  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.51/4.51  tff(c_30, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.51/4.51  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.51/4.51  tff(c_113, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.51/4.51  tff(c_119, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_113])).
% 11.51/4.51  tff(c_123, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_119])).
% 11.51/4.51  tff(c_25927, plain, (![C_1641, A_1642, B_1643]: (v4_relat_1(C_1641, A_1642) | ~m1_subset_1(C_1641, k1_zfmisc_1(k2_zfmisc_1(A_1642, B_1643))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.51/4.51  tff(c_25942, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_25927])).
% 11.51/4.51  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.51/4.51  tff(c_26083, plain, (![A_1656, B_1657, C_1658]: (k2_relset_1(A_1656, B_1657, C_1658)=k2_relat_1(C_1658) | ~m1_subset_1(C_1658, k1_zfmisc_1(k2_zfmisc_1(A_1656, B_1657))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.51/4.51  tff(c_26098, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_26083])).
% 11.51/4.51  tff(c_58, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.51/4.51  tff(c_26117, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26098, c_58])).
% 11.51/4.51  tff(c_26229, plain, (![C_1670, A_1671, B_1672]: (m1_subset_1(C_1670, k1_zfmisc_1(k2_zfmisc_1(A_1671, B_1672))) | ~r1_tarski(k2_relat_1(C_1670), B_1672) | ~r1_tarski(k1_relat_1(C_1670), A_1671) | ~v1_relat_1(C_1670))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.51/4.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.51/4.51  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.51/4.51  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.51/4.51  tff(c_56, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.51/4.51  tff(c_75, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 11.51/4.51  tff(c_7277, plain, (![A_602, B_603, C_604]: (k1_relset_1(A_602, B_603, C_604)=k1_relat_1(C_604) | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(A_602, B_603))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.51/4.51  tff(c_7292, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_7277])).
% 11.51/4.51  tff(c_7541, plain, (![B_635, A_636, C_637]: (k1_xboole_0=B_635 | k1_relset_1(A_636, B_635, C_637)=A_636 | ~v1_funct_2(C_637, A_636, B_635) | ~m1_subset_1(C_637, k1_zfmisc_1(k2_zfmisc_1(A_636, B_635))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_7551, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_7541])).
% 11.51/4.51  tff(c_7562, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_7292, c_7551])).
% 11.51/4.51  tff(c_7563, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_75, c_7562])).
% 11.51/4.51  tff(c_4658, plain, (![A_409, B_410, C_411]: (k1_relset_1(A_409, B_410, C_411)=k1_relat_1(C_411) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_409, B_410))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.51/4.51  tff(c_4673, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_4658])).
% 11.51/4.51  tff(c_5122, plain, (![B_460, A_461, C_462]: (k1_xboole_0=B_460 | k1_relset_1(A_461, B_460, C_462)=A_461 | ~v1_funct_2(C_462, A_461, B_460) | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(A_461, B_460))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_5132, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_5122])).
% 11.51/4.51  tff(c_5143, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4673, c_5132])).
% 11.51/4.51  tff(c_5144, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_75, c_5143])).
% 11.51/4.51  tff(c_4773, plain, (![A_418, B_419, C_420]: (k2_relset_1(A_418, B_419, C_420)=k2_relat_1(C_420) | ~m1_subset_1(C_420, k1_zfmisc_1(k2_zfmisc_1(A_418, B_419))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.51/4.51  tff(c_4788, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_4773])).
% 11.51/4.51  tff(c_4798, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4788, c_58])).
% 11.51/4.51  tff(c_4844, plain, (![C_426, A_427, B_428]: (m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(A_427, B_428))) | ~r1_tarski(k2_relat_1(C_426), B_428) | ~r1_tarski(k1_relat_1(C_426), A_427) | ~v1_relat_1(C_426))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.51/4.51  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.51/4.51  tff(c_6551, plain, (![C_558, A_559, B_560]: (r1_tarski(C_558, k2_zfmisc_1(A_559, B_560)) | ~r1_tarski(k2_relat_1(C_558), B_560) | ~r1_tarski(k1_relat_1(C_558), A_559) | ~v1_relat_1(C_558))), inference(resolution, [status(thm)], [c_4844, c_16])).
% 11.51/4.51  tff(c_6553, plain, (![A_559]: (r1_tarski('#skF_4', k2_zfmisc_1(A_559, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_559) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4798, c_6551])).
% 11.51/4.51  tff(c_6568, plain, (![A_561]: (r1_tarski('#skF_4', k2_zfmisc_1(A_561, '#skF_3')) | ~r1_tarski('#skF_1', A_561))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_5144, c_6553])).
% 11.51/4.51  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.51/4.51  tff(c_4672, plain, (![A_409, B_410, A_6]: (k1_relset_1(A_409, B_410, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_409, B_410)))), inference(resolution, [status(thm)], [c_18, c_4658])).
% 11.51/4.51  tff(c_6574, plain, (![A_561]: (k1_relset_1(A_561, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_561))), inference(resolution, [status(thm)], [c_6568, c_4672])).
% 11.51/4.51  tff(c_6601, plain, (![A_562]: (k1_relset_1(A_562, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_562))), inference(demodulation, [status(thm), theory('equality')], [c_5144, c_6574])).
% 11.51/4.51  tff(c_6606, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_6601])).
% 11.51/4.51  tff(c_6563, plain, (![A_559]: (r1_tarski('#skF_4', k2_zfmisc_1(A_559, '#skF_3')) | ~r1_tarski('#skF_1', A_559))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_5144, c_6553])).
% 11.51/4.51  tff(c_4982, plain, (![B_444, C_445, A_446]: (k1_xboole_0=B_444 | v1_funct_2(C_445, A_446, B_444) | k1_relset_1(A_446, B_444, C_445)!=A_446 | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_446, B_444))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_6726, plain, (![B_569, A_570, A_571]: (k1_xboole_0=B_569 | v1_funct_2(A_570, A_571, B_569) | k1_relset_1(A_571, B_569, A_570)!=A_571 | ~r1_tarski(A_570, k2_zfmisc_1(A_571, B_569)))), inference(resolution, [status(thm)], [c_18, c_4982])).
% 11.51/4.51  tff(c_6759, plain, (![A_559]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_559, '#skF_3') | k1_relset_1(A_559, '#skF_3', '#skF_4')!=A_559 | ~r1_tarski('#skF_1', A_559))), inference(resolution, [status(thm)], [c_6563, c_6726])).
% 11.51/4.51  tff(c_6817, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_6759])).
% 11.51/4.51  tff(c_6889, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_6817, c_8])).
% 11.51/4.51  tff(c_4359, plain, (![B_365, A_366]: (B_365=A_366 | ~r1_tarski(B_365, A_366) | ~r1_tarski(A_366, B_365))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.51/4.51  tff(c_4369, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_4359])).
% 11.51/4.51  tff(c_4467, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_4369])).
% 11.51/4.51  tff(c_4796, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4788, c_4467])).
% 11.51/4.51  tff(c_7012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6889, c_4796])).
% 11.51/4.51  tff(c_7015, plain, (![A_581]: (v1_funct_2('#skF_4', A_581, '#skF_3') | k1_relset_1(A_581, '#skF_3', '#skF_4')!=A_581 | ~r1_tarski('#skF_1', A_581))), inference(splitRight, [status(thm)], [c_6759])).
% 11.51/4.51  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.51/4.51  tff(c_54, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.51/4.51  tff(c_66, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54])).
% 11.51/4.51  tff(c_4423, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 11.51/4.51  tff(c_7021, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_7015, c_4423])).
% 11.51/4.51  tff(c_7026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6606, c_7021])).
% 11.51/4.51  tff(c_7027, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_4369])).
% 11.51/4.51  tff(c_7199, plain, (![A_597, B_598, C_599]: (k2_relset_1(A_597, B_598, C_599)=k2_relat_1(C_599) | ~m1_subset_1(C_599, k1_zfmisc_1(k2_zfmisc_1(A_597, B_598))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.51/4.51  tff(c_7206, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_7199])).
% 11.51/4.51  tff(c_7215, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7027, c_7206])).
% 11.51/4.51  tff(c_7396, plain, (![C_617, A_618, B_619]: (m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(A_618, B_619))) | ~r1_tarski(k2_relat_1(C_617), B_619) | ~r1_tarski(k1_relat_1(C_617), A_618) | ~v1_relat_1(C_617))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.51/4.51  tff(c_9173, plain, (![C_751, A_752, B_753]: (r1_tarski(C_751, k2_zfmisc_1(A_752, B_753)) | ~r1_tarski(k2_relat_1(C_751), B_753) | ~r1_tarski(k1_relat_1(C_751), A_752) | ~v1_relat_1(C_751))), inference(resolution, [status(thm)], [c_7396, c_16])).
% 11.51/4.51  tff(c_9175, plain, (![A_752, B_753]: (r1_tarski('#skF_4', k2_zfmisc_1(A_752, B_753)) | ~r1_tarski('#skF_3', B_753) | ~r1_tarski(k1_relat_1('#skF_4'), A_752) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7215, c_9173])).
% 11.51/4.51  tff(c_9189, plain, (![A_754, B_755]: (r1_tarski('#skF_4', k2_zfmisc_1(A_754, B_755)) | ~r1_tarski('#skF_3', B_755) | ~r1_tarski('#skF_1', A_754))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_7563, c_9175])).
% 11.51/4.51  tff(c_7291, plain, (![A_602, B_603, A_6]: (k1_relset_1(A_602, B_603, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_602, B_603)))), inference(resolution, [status(thm)], [c_18, c_7277])).
% 11.51/4.51  tff(c_9195, plain, (![A_754, B_755]: (k1_relset_1(A_754, B_755, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_755) | ~r1_tarski('#skF_1', A_754))), inference(resolution, [status(thm)], [c_9189, c_7291])).
% 11.51/4.51  tff(c_9261, plain, (![A_762, B_763]: (k1_relset_1(A_762, B_763, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_763) | ~r1_tarski('#skF_1', A_762))), inference(demodulation, [status(thm), theory('equality')], [c_7563, c_9195])).
% 11.51/4.51  tff(c_9276, plain, (![A_765]: (k1_relset_1(A_765, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_765))), inference(resolution, [status(thm)], [c_6, c_9261])).
% 11.51/4.51  tff(c_9281, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_9276])).
% 11.51/4.51  tff(c_9469, plain, (![C_777, A_778]: (r1_tarski(C_777, k2_zfmisc_1(A_778, k2_relat_1(C_777))) | ~r1_tarski(k1_relat_1(C_777), A_778) | ~v1_relat_1(C_777))), inference(resolution, [status(thm)], [c_6, c_9173])).
% 11.51/4.51  tff(c_9525, plain, (![A_778]: (r1_tarski('#skF_4', k2_zfmisc_1(A_778, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_778) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7215, c_9469])).
% 11.51/4.51  tff(c_9556, plain, (![A_778]: (r1_tarski('#skF_4', k2_zfmisc_1(A_778, '#skF_3')) | ~r1_tarski('#skF_1', A_778))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_7563, c_9525])).
% 11.51/4.51  tff(c_7685, plain, (![B_648, C_649, A_650]: (k1_xboole_0=B_648 | v1_funct_2(C_649, A_650, B_648) | k1_relset_1(A_650, B_648, C_649)!=A_650 | ~m1_subset_1(C_649, k1_zfmisc_1(k2_zfmisc_1(A_650, B_648))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_10159, plain, (![B_799, A_800, A_801]: (k1_xboole_0=B_799 | v1_funct_2(A_800, A_801, B_799) | k1_relset_1(A_801, B_799, A_800)!=A_801 | ~r1_tarski(A_800, k2_zfmisc_1(A_801, B_799)))), inference(resolution, [status(thm)], [c_18, c_7685])).
% 11.51/4.51  tff(c_10194, plain, (![A_778]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_778, '#skF_3') | k1_relset_1(A_778, '#skF_3', '#skF_4')!=A_778 | ~r1_tarski('#skF_1', A_778))), inference(resolution, [status(thm)], [c_9556, c_10159])).
% 11.51/4.51  tff(c_10554, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_10194])).
% 11.51/4.51  tff(c_26, plain, (![B_14, A_13]: (v5_relat_1(B_14, A_13) | ~r1_tarski(k2_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.51/4.51  tff(c_7222, plain, (![A_13]: (v5_relat_1('#skF_4', A_13) | ~r1_tarski('#skF_3', A_13) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7215, c_26])).
% 11.51/4.51  tff(c_7231, plain, (![A_13]: (v5_relat_1('#skF_4', A_13) | ~r1_tarski('#skF_3', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_7222])).
% 11.51/4.51  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.51/4.51  tff(c_28, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.51/4.51  tff(c_7157, plain, (![C_593, A_594, B_595]: (v4_relat_1(C_593, A_594) | ~m1_subset_1(C_593, k1_zfmisc_1(k2_zfmisc_1(A_594, B_595))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.51/4.51  tff(c_7347, plain, (![A_612, A_613, B_614]: (v4_relat_1(A_612, A_613) | ~r1_tarski(A_612, k2_zfmisc_1(A_613, B_614)))), inference(resolution, [status(thm)], [c_18, c_7157])).
% 11.51/4.51  tff(c_8038, plain, (![B_680, A_681, B_682]: (v4_relat_1(k2_relat_1(B_680), A_681) | ~v5_relat_1(B_680, k2_zfmisc_1(A_681, B_682)) | ~v1_relat_1(B_680))), inference(resolution, [status(thm)], [c_28, c_7347])).
% 11.51/4.51  tff(c_8124, plain, (![B_689, A_690]: (v4_relat_1(k2_relat_1(B_689), A_690) | ~v5_relat_1(B_689, k1_xboole_0) | ~v1_relat_1(B_689))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8038])).
% 11.51/4.51  tff(c_8133, plain, (![A_690]: (v4_relat_1('#skF_3', A_690) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7215, c_8124])).
% 11.51/4.51  tff(c_8140, plain, (![A_690]: (v4_relat_1('#skF_3', A_690) | ~v5_relat_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_8133])).
% 11.51/4.51  tff(c_8143, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8140])).
% 11.51/4.51  tff(c_8182, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_7231, c_8143])).
% 11.51/4.51  tff(c_10598, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10554, c_8182])).
% 11.51/4.51  tff(c_10644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10598])).
% 11.51/4.51  tff(c_10647, plain, (![A_812]: (v1_funct_2('#skF_4', A_812, '#skF_3') | k1_relset_1(A_812, '#skF_3', '#skF_4')!=A_812 | ~r1_tarski('#skF_1', A_812))), inference(splitRight, [status(thm)], [c_10194])).
% 11.51/4.51  tff(c_10658, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_10647, c_4423])).
% 11.51/4.51  tff(c_10671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9281, c_10658])).
% 11.51/4.51  tff(c_10673, plain, (v5_relat_1('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8140])).
% 11.51/4.51  tff(c_4447, plain, (![B_380, A_381]: (r1_tarski(k2_relat_1(B_380), A_381) | ~v5_relat_1(B_380, A_381) | ~v1_relat_1(B_380))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.51/4.51  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.51/4.51  tff(c_7964, plain, (![B_677, A_678]: (k2_relat_1(B_677)=A_678 | ~r1_tarski(A_678, k2_relat_1(B_677)) | ~v5_relat_1(B_677, A_678) | ~v1_relat_1(B_677))), inference(resolution, [status(thm)], [c_4447, c_2])).
% 11.51/4.51  tff(c_7967, plain, (![A_678]: (k2_relat_1('#skF_4')=A_678 | ~r1_tarski(A_678, '#skF_3') | ~v5_relat_1('#skF_4', A_678) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7215, c_7964])).
% 11.51/4.51  tff(c_7988, plain, (![A_678]: (A_678='#skF_3' | ~r1_tarski(A_678, '#skF_3') | ~v5_relat_1('#skF_4', A_678))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_7215, c_7967])).
% 11.51/4.51  tff(c_10689, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_10673, c_7988])).
% 11.51/4.51  tff(c_10700, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10689])).
% 11.51/4.51  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.51/4.51  tff(c_4425, plain, (![C_376, B_377, A_378]: (v5_relat_1(C_376, B_377) | ~m1_subset_1(C_376, k1_zfmisc_1(k2_zfmisc_1(A_378, B_377))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.51/4.51  tff(c_4461, plain, (![C_383, B_384]: (v5_relat_1(C_383, B_384) | ~m1_subset_1(C_383, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_4425])).
% 11.51/4.51  tff(c_4465, plain, (![A_6, B_384]: (v5_relat_1(A_6, B_384) | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_4461])).
% 11.51/4.51  tff(c_7225, plain, (![A_13]: (r1_tarski('#skF_3', A_13) | ~v5_relat_1('#skF_4', A_13) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7215, c_28])).
% 11.51/4.51  tff(c_7243, plain, (![A_601]: (r1_tarski('#skF_3', A_601) | ~v5_relat_1('#skF_4', A_601))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_7225])).
% 11.51/4.51  tff(c_7267, plain, (![B_384]: (r1_tarski('#skF_3', B_384) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_4465, c_7243])).
% 11.51/4.51  tff(c_7298, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7267])).
% 11.51/4.51  tff(c_10766, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10700, c_7298])).
% 11.51/4.51  tff(c_7417, plain, (![C_617, A_4]: (m1_subset_1(C_617, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_617), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_617), A_4) | ~v1_relat_1(C_617))), inference(superposition, [status(thm), theory('equality')], [c_12, c_7396])).
% 11.51/4.51  tff(c_11124, plain, (![C_826, A_827]: (m1_subset_1(C_826, k1_zfmisc_1('#skF_3')) | ~r1_tarski(k2_relat_1(C_826), '#skF_3') | ~r1_tarski(k1_relat_1(C_826), A_827) | ~v1_relat_1(C_826))), inference(demodulation, [status(thm), theory('equality')], [c_10700, c_10700, c_7417])).
% 11.51/4.51  tff(c_11128, plain, (![A_827]: (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), A_827) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7215, c_11124])).
% 11.51/4.51  tff(c_11135, plain, (![A_827]: (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~r1_tarski('#skF_1', A_827))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_7563, c_6, c_11128])).
% 11.51/4.51  tff(c_11148, plain, (![A_830]: (~r1_tarski('#skF_1', A_830))), inference(splitLeft, [status(thm)], [c_11135])).
% 11.51/4.51  tff(c_11153, plain, $false, inference(resolution, [status(thm)], [c_6, c_11148])).
% 11.51/4.51  tff(c_11154, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_11135])).
% 11.51/4.51  tff(c_11160, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_11154, c_16])).
% 11.51/4.51  tff(c_11167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10766, c_11160])).
% 11.51/4.51  tff(c_11168, plain, (![B_384]: (r1_tarski('#skF_3', B_384))), inference(splitRight, [status(thm)], [c_7267])).
% 11.51/4.51  tff(c_11174, plain, (![B_831]: (r1_tarski('#skF_3', B_831))), inference(splitRight, [status(thm)], [c_7267])).
% 11.51/4.51  tff(c_4374, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_4359])).
% 11.51/4.51  tff(c_11196, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_11174, c_4374])).
% 11.51/4.51  tff(c_11169, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_7267])).
% 11.51/4.51  tff(c_11224, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11196, c_11169])).
% 11.51/4.51  tff(c_11226, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_11224, c_2])).
% 11.51/4.51  tff(c_11232, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11168, c_11226])).
% 11.51/4.51  tff(c_11213, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11196, c_11196, c_14])).
% 11.51/4.51  tff(c_11314, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11232, c_11232, c_11213])).
% 11.51/4.51  tff(c_42, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_29, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_70, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 11.51/4.51  tff(c_7173, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_70])).
% 11.51/4.51  tff(c_7176, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_7173])).
% 11.51/4.51  tff(c_7180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7176])).
% 11.51/4.51  tff(c_7181, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29)), inference(splitRight, [status(thm)], [c_70])).
% 11.51/4.51  tff(c_11200, plain, (![A_29]: (v1_funct_2('#skF_3', A_29, '#skF_3') | A_29='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11196, c_11196, c_11196, c_7181])).
% 11.51/4.51  tff(c_11423, plain, (![A_843]: (v1_funct_2('#skF_4', A_843, '#skF_4') | A_843='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11232, c_11232, c_11232, c_11200])).
% 11.51/4.51  tff(c_11245, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11232, c_4423])).
% 11.51/4.51  tff(c_11430, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_11423, c_11245])).
% 11.51/4.51  tff(c_103, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.51/4.51  tff(c_107, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_103])).
% 11.51/4.51  tff(c_4368, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_107, c_4359])).
% 11.51/4.51  tff(c_7130, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_4368])).
% 11.51/4.51  tff(c_11439, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11430, c_7130])).
% 11.51/4.51  tff(c_11444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_11314, c_11439])).
% 11.51/4.51  tff(c_11445, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_4368])).
% 11.51/4.51  tff(c_11449, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11445, c_60])).
% 11.51/4.51  tff(c_11601, plain, (![A_859, B_860, C_861]: (k1_relset_1(A_859, B_860, C_861)=k1_relat_1(C_861) | ~m1_subset_1(C_861, k1_zfmisc_1(k2_zfmisc_1(A_859, B_860))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.51/4.51  tff(c_11692, plain, (![C_868]: (k1_relset_1('#skF_1', '#skF_2', C_868)=k1_relat_1(C_868) | ~m1_subset_1(C_868, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11445, c_11601])).
% 11.51/4.51  tff(c_11700, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_11449, c_11692])).
% 11.51/4.51  tff(c_21794, plain, (![B_1365, A_1366, C_1367]: (k1_xboole_0=B_1365 | k1_relset_1(A_1366, B_1365, C_1367)=A_1366 | ~v1_funct_2(C_1367, A_1366, B_1365) | ~m1_subset_1(C_1367, k1_zfmisc_1(k2_zfmisc_1(A_1366, B_1365))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_21800, plain, (![C_1367]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_1367)='#skF_1' | ~v1_funct_2(C_1367, '#skF_1', '#skF_2') | ~m1_subset_1(C_1367, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11445, c_21794])).
% 11.51/4.51  tff(c_21824, plain, (![C_1370]: (k1_relset_1('#skF_1', '#skF_2', C_1370)='#skF_1' | ~v1_funct_2(C_1370, '#skF_1', '#skF_2') | ~m1_subset_1(C_1370, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_75, c_21800])).
% 11.51/4.51  tff(c_21827, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_11449, c_21824])).
% 11.51/4.51  tff(c_21834, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_11700, c_21827])).
% 11.51/4.51  tff(c_12451, plain, (![B_934, A_935, C_936]: (k1_xboole_0=B_934 | k1_relset_1(A_935, B_934, C_936)=A_935 | ~v1_funct_2(C_936, A_935, B_934) | ~m1_subset_1(C_936, k1_zfmisc_1(k2_zfmisc_1(A_935, B_934))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_12457, plain, (![C_936]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_936)='#skF_1' | ~v1_funct_2(C_936, '#skF_1', '#skF_2') | ~m1_subset_1(C_936, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11445, c_12451])).
% 11.51/4.51  tff(c_12526, plain, (![C_944]: (k1_relset_1('#skF_1', '#skF_2', C_944)='#skF_1' | ~v1_funct_2(C_944, '#skF_1', '#skF_2') | ~m1_subset_1(C_944, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_75, c_12457])).
% 11.51/4.51  tff(c_12532, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_11449, c_12526])).
% 11.51/4.51  tff(c_12542, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_11700, c_12532])).
% 11.51/4.51  tff(c_11883, plain, (![A_886, B_887, C_888]: (k2_relset_1(A_886, B_887, C_888)=k2_relat_1(C_888) | ~m1_subset_1(C_888, k1_zfmisc_1(k2_zfmisc_1(A_886, B_887))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.51/4.51  tff(c_11920, plain, (![C_893]: (k2_relset_1('#skF_1', '#skF_2', C_893)=k2_relat_1(C_893) | ~m1_subset_1(C_893, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11445, c_11883])).
% 11.51/4.51  tff(c_11923, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_11449, c_11920])).
% 11.51/4.51  tff(c_11929, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7027, c_11923])).
% 11.51/4.51  tff(c_12192, plain, (![C_914, A_915, B_916]: (m1_subset_1(C_914, k1_zfmisc_1(k2_zfmisc_1(A_915, B_916))) | ~r1_tarski(k2_relat_1(C_914), B_916) | ~r1_tarski(k1_relat_1(C_914), A_915) | ~v1_relat_1(C_914))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.51/4.51  tff(c_13851, plain, (![C_1026, A_1027, B_1028]: (r1_tarski(C_1026, k2_zfmisc_1(A_1027, B_1028)) | ~r1_tarski(k2_relat_1(C_1026), B_1028) | ~r1_tarski(k1_relat_1(C_1026), A_1027) | ~v1_relat_1(C_1026))), inference(resolution, [status(thm)], [c_12192, c_16])).
% 11.51/4.51  tff(c_13853, plain, (![A_1027, B_1028]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1027, B_1028)) | ~r1_tarski('#skF_3', B_1028) | ~r1_tarski(k1_relat_1('#skF_4'), A_1027) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11929, c_13851])).
% 11.51/4.51  tff(c_14032, plain, (![A_1035, B_1036]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1035, B_1036)) | ~r1_tarski('#skF_3', B_1036) | ~r1_tarski('#skF_1', A_1035))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_12542, c_13853])).
% 11.51/4.51  tff(c_11615, plain, (![A_859, B_860, A_6]: (k1_relset_1(A_859, B_860, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_859, B_860)))), inference(resolution, [status(thm)], [c_18, c_11601])).
% 11.51/4.51  tff(c_14038, plain, (![A_1035, B_1036]: (k1_relset_1(A_1035, B_1036, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_1036) | ~r1_tarski('#skF_1', A_1035))), inference(resolution, [status(thm)], [c_14032, c_11615])).
% 11.51/4.51  tff(c_14098, plain, (![A_1041, B_1042]: (k1_relset_1(A_1041, B_1042, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_1042) | ~r1_tarski('#skF_1', A_1041))), inference(demodulation, [status(thm), theory('equality')], [c_12542, c_14038])).
% 11.51/4.51  tff(c_14178, plain, (![A_1049]: (k1_relset_1(A_1049, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_1049))), inference(resolution, [status(thm)], [c_6, c_14098])).
% 11.51/4.51  tff(c_14183, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_14178])).
% 11.51/4.51  tff(c_40, plain, (![C_28, A_26, B_27]: (m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~r1_tarski(k2_relat_1(C_28), B_27) | ~r1_tarski(k1_relat_1(C_28), A_26) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.51/4.51  tff(c_12320, plain, (![B_920, C_921, A_922]: (k1_xboole_0=B_920 | v1_funct_2(C_921, A_922, B_920) | k1_relset_1(A_922, B_920, C_921)!=A_922 | ~m1_subset_1(C_921, k1_zfmisc_1(k2_zfmisc_1(A_922, B_920))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_15984, plain, (![B_1097, C_1098, A_1099]: (k1_xboole_0=B_1097 | v1_funct_2(C_1098, A_1099, B_1097) | k1_relset_1(A_1099, B_1097, C_1098)!=A_1099 | ~r1_tarski(k2_relat_1(C_1098), B_1097) | ~r1_tarski(k1_relat_1(C_1098), A_1099) | ~v1_relat_1(C_1098))), inference(resolution, [status(thm)], [c_40, c_12320])).
% 11.51/4.51  tff(c_15997, plain, (![B_1097, A_1099]: (k1_xboole_0=B_1097 | v1_funct_2('#skF_4', A_1099, B_1097) | k1_relset_1(A_1099, B_1097, '#skF_4')!=A_1099 | ~r1_tarski('#skF_3', B_1097) | ~r1_tarski(k1_relat_1('#skF_4'), A_1099) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11929, c_15984])).
% 11.51/4.51  tff(c_16619, plain, (![B_1113, A_1114]: (k1_xboole_0=B_1113 | v1_funct_2('#skF_4', A_1114, B_1113) | k1_relset_1(A_1114, B_1113, '#skF_4')!=A_1114 | ~r1_tarski('#skF_3', B_1113) | ~r1_tarski('#skF_1', A_1114))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_12542, c_15997])).
% 11.51/4.51  tff(c_16638, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_16619, c_4423])).
% 11.51/4.51  tff(c_16655, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_14183, c_16638])).
% 11.51/4.51  tff(c_11940, plain, (![A_13]: (v5_relat_1('#skF_4', A_13) | ~r1_tarski('#skF_3', A_13) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11929, c_26])).
% 11.51/4.51  tff(c_11951, plain, (![A_13]: (v5_relat_1('#skF_4', A_13) | ~r1_tarski('#skF_3', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_11940])).
% 11.51/4.51  tff(c_11472, plain, (![C_844, A_845, B_846]: (v4_relat_1(C_844, A_845) | ~m1_subset_1(C_844, k1_zfmisc_1(k2_zfmisc_1(A_845, B_846))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.51/4.51  tff(c_11616, plain, (![A_862, A_863, B_864]: (v4_relat_1(A_862, A_863) | ~r1_tarski(A_862, k2_zfmisc_1(A_863, B_864)))), inference(resolution, [status(thm)], [c_18, c_11472])).
% 11.51/4.51  tff(c_12895, plain, (![B_965, A_966, B_967]: (v4_relat_1(k2_relat_1(B_965), A_966) | ~v5_relat_1(B_965, k2_zfmisc_1(A_966, B_967)) | ~v1_relat_1(B_965))), inference(resolution, [status(thm)], [c_28, c_11616])).
% 11.51/4.51  tff(c_12977, plain, (![B_974, A_975]: (v4_relat_1(k2_relat_1(B_974), A_975) | ~v5_relat_1(B_974, k1_xboole_0) | ~v1_relat_1(B_974))), inference(superposition, [status(thm), theory('equality')], [c_12, c_12895])).
% 11.51/4.51  tff(c_12989, plain, (![A_975]: (v4_relat_1('#skF_3', A_975) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11929, c_12977])).
% 11.51/4.51  tff(c_12997, plain, (![A_975]: (v4_relat_1('#skF_3', A_975) | ~v5_relat_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_12989])).
% 11.51/4.51  tff(c_13014, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_12997])).
% 11.51/4.51  tff(c_13021, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_11951, c_13014])).
% 11.51/4.51  tff(c_16701, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16655, c_13021])).
% 11.51/4.51  tff(c_16755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_16701])).
% 11.51/4.51  tff(c_16757, plain, (v5_relat_1('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_12997])).
% 11.51/4.51  tff(c_12771, plain, (![B_958, A_959]: (k2_relat_1(B_958)=A_959 | ~r1_tarski(A_959, k2_relat_1(B_958)) | ~v5_relat_1(B_958, A_959) | ~v1_relat_1(B_958))), inference(resolution, [status(thm)], [c_4447, c_2])).
% 11.51/4.51  tff(c_12774, plain, (![A_959]: (k2_relat_1('#skF_4')=A_959 | ~r1_tarski(A_959, '#skF_3') | ~v5_relat_1('#skF_4', A_959) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11929, c_12771])).
% 11.51/4.51  tff(c_12795, plain, (![A_959]: (A_959='#skF_3' | ~r1_tarski(A_959, '#skF_3') | ~v5_relat_1('#skF_4', A_959))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_11929, c_12774])).
% 11.51/4.51  tff(c_16779, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_16757, c_12795])).
% 11.51/4.51  tff(c_16790, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16779])).
% 11.51/4.51  tff(c_16848, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_16790, c_8])).
% 11.51/4.51  tff(c_11731, plain, (![A_870]: (k1_relset_1('#skF_1', '#skF_2', A_870)=k1_relat_1(A_870) | ~r1_tarski(A_870, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_11692])).
% 11.51/4.51  tff(c_11748, plain, (![B_14]: (k1_relset_1('#skF_1', '#skF_2', k2_relat_1(B_14))=k1_relat_1(k2_relat_1(B_14)) | ~v5_relat_1(B_14, '#skF_4') | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_28, c_11731])).
% 11.51/4.51  tff(c_11934, plain, (k1_relat_1(k2_relat_1('#skF_4'))=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | ~v5_relat_1('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11929, c_11748])).
% 11.51/4.51  tff(c_11947, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3') | ~v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_11929, c_11934])).
% 11.51/4.51  tff(c_12091, plain, (~v5_relat_1('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_11947])).
% 11.51/4.51  tff(c_12098, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_11951, c_12091])).
% 11.51/4.51  tff(c_16981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16848, c_12098])).
% 11.51/4.51  tff(c_16983, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_11947])).
% 11.51/4.51  tff(c_11943, plain, (![A_13]: (r1_tarski('#skF_3', A_13) | ~v5_relat_1('#skF_4', A_13) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11929, c_28])).
% 11.51/4.51  tff(c_11953, plain, (![A_13]: (r1_tarski('#skF_3', A_13) | ~v5_relat_1('#skF_4', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_11943])).
% 11.51/4.51  tff(c_16987, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_16983, c_11953])).
% 11.51/4.51  tff(c_17001, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_16987, c_2])).
% 11.51/4.51  tff(c_17009, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_17001])).
% 11.51/4.51  tff(c_17214, plain, (![B_1135, A_1136, C_1137]: (k1_xboole_0=B_1135 | k1_relset_1(A_1136, B_1135, C_1137)=A_1136 | ~v1_funct_2(C_1137, A_1136, B_1135) | ~m1_subset_1(C_1137, k1_zfmisc_1(k2_zfmisc_1(A_1136, B_1135))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_17220, plain, (![C_1137]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_1137)='#skF_1' | ~v1_funct_2(C_1137, '#skF_1', '#skF_2') | ~m1_subset_1(C_1137, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11445, c_17214])).
% 11.51/4.51  tff(c_17260, plain, (![C_1139]: (k1_relset_1('#skF_1', '#skF_2', C_1139)='#skF_1' | ~v1_funct_2(C_1139, '#skF_1', '#skF_2') | ~m1_subset_1(C_1139, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_75, c_17220])).
% 11.51/4.51  tff(c_17266, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_11449, c_17260])).
% 11.51/4.51  tff(c_17275, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_11700, c_17266])).
% 11.51/4.51  tff(c_17024, plain, (![C_1123, A_1124, B_1125]: (m1_subset_1(C_1123, k1_zfmisc_1(k2_zfmisc_1(A_1124, B_1125))) | ~r1_tarski(k2_relat_1(C_1123), B_1125) | ~r1_tarski(k1_relat_1(C_1123), A_1124) | ~v1_relat_1(C_1123))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.51/4.51  tff(c_36, plain, (![A_20, B_21, C_22]: (k1_relset_1(A_20, B_21, C_22)=k1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.51/4.51  tff(c_19143, plain, (![A_1264, B_1265, C_1266]: (k1_relset_1(A_1264, B_1265, C_1266)=k1_relat_1(C_1266) | ~r1_tarski(k2_relat_1(C_1266), B_1265) | ~r1_tarski(k1_relat_1(C_1266), A_1264) | ~v1_relat_1(C_1266))), inference(resolution, [status(thm)], [c_17024, c_36])).
% 11.51/4.51  tff(c_19145, plain, (![A_1264, B_1265]: (k1_relset_1(A_1264, B_1265, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_1265) | ~r1_tarski(k1_relat_1('#skF_4'), A_1264) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11929, c_19143])).
% 11.51/4.51  tff(c_19159, plain, (![A_1267, B_1268]: (k1_relset_1(A_1267, B_1268, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_1268) | ~r1_tarski('#skF_1', A_1267))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_17275, c_17275, c_19145])).
% 11.51/4.51  tff(c_19170, plain, (![A_1269]: (k1_relset_1(A_1269, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_1269))), inference(resolution, [status(thm)], [c_6, c_19159])).
% 11.51/4.51  tff(c_19175, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_19170])).
% 11.51/4.51  tff(c_17322, plain, (![B_1141, C_1142, A_1143]: (k1_xboole_0=B_1141 | v1_funct_2(C_1142, A_1143, B_1141) | k1_relset_1(A_1143, B_1141, C_1142)!=A_1143 | ~m1_subset_1(C_1142, k1_zfmisc_1(k2_zfmisc_1(A_1143, B_1141))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_20279, plain, (![B_1299, C_1300, A_1301]: (k1_xboole_0=B_1299 | v1_funct_2(C_1300, A_1301, B_1299) | k1_relset_1(A_1301, B_1299, C_1300)!=A_1301 | ~r1_tarski(k2_relat_1(C_1300), B_1299) | ~r1_tarski(k1_relat_1(C_1300), A_1301) | ~v1_relat_1(C_1300))), inference(resolution, [status(thm)], [c_40, c_17322])).
% 11.51/4.51  tff(c_20288, plain, (![B_1299, A_1301]: (k1_xboole_0=B_1299 | v1_funct_2('#skF_4', A_1301, B_1299) | k1_relset_1(A_1301, B_1299, '#skF_4')!=A_1301 | ~r1_tarski('#skF_3', B_1299) | ~r1_tarski(k1_relat_1('#skF_4'), A_1301) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11929, c_20279])).
% 11.51/4.51  tff(c_20800, plain, (![B_1317, A_1318]: (k1_xboole_0=B_1317 | v1_funct_2('#skF_4', A_1318, B_1317) | k1_relset_1(A_1318, B_1317, '#skF_4')!=A_1318 | ~r1_tarski('#skF_3', B_1317) | ~r1_tarski('#skF_1', A_1318))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_17275, c_20288])).
% 11.51/4.51  tff(c_20819, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_20800, c_4423])).
% 11.51/4.51  tff(c_20836, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_19175, c_20819])).
% 11.51/4.51  tff(c_7038, plain, (![A_582, B_583, A_584]: (v5_relat_1(A_582, B_583) | ~r1_tarski(A_582, k2_zfmisc_1(A_584, B_583)))), inference(resolution, [status(thm)], [c_18, c_4425])).
% 11.51/4.51  tff(c_17528, plain, (![B_1162, B_1163, A_1164]: (v5_relat_1(k2_relat_1(B_1162), B_1163) | ~v5_relat_1(B_1162, k2_zfmisc_1(A_1164, B_1163)) | ~v1_relat_1(B_1162))), inference(resolution, [status(thm)], [c_28, c_7038])).
% 11.51/4.51  tff(c_17618, plain, (![B_1171]: (v5_relat_1(k2_relat_1(B_1171), k1_xboole_0) | ~v5_relat_1(B_1171, k1_xboole_0) | ~v1_relat_1(B_1171))), inference(superposition, [status(thm), theory('equality')], [c_12, c_17528])).
% 11.51/4.51  tff(c_17626, plain, (v5_relat_1('#skF_3', k1_xboole_0) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11929, c_17618])).
% 11.51/4.51  tff(c_17635, plain, (v5_relat_1('#skF_3', k1_xboole_0) | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_123, c_17626])).
% 11.51/4.51  tff(c_17670, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_17635])).
% 11.51/4.51  tff(c_17677, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_11951, c_17670])).
% 11.51/4.51  tff(c_20882, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20836, c_17677])).
% 11.51/4.51  tff(c_20931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_20882])).
% 11.51/4.51  tff(c_20933, plain, (v5_relat_1('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_17635])).
% 11.51/4.51  tff(c_4457, plain, (![B_380]: (k2_relat_1(B_380)=k1_xboole_0 | ~v5_relat_1(B_380, k1_xboole_0) | ~v1_relat_1(B_380))), inference(resolution, [status(thm)], [c_4447, c_4374])).
% 11.51/4.51  tff(c_20952, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20933, c_4457])).
% 11.51/4.51  tff(c_20959, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_11929, c_20952])).
% 11.51/4.51  tff(c_17048, plain, (![C_1123, A_4]: (m1_subset_1(C_1123, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_1123), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_1123), A_4) | ~v1_relat_1(C_1123))), inference(superposition, [status(thm), theory('equality')], [c_12, c_17024])).
% 11.51/4.51  tff(c_21489, plain, (![C_1339, A_1340]: (m1_subset_1(C_1339, k1_zfmisc_1('#skF_3')) | ~r1_tarski(k2_relat_1(C_1339), '#skF_3') | ~r1_tarski(k1_relat_1(C_1339), A_1340) | ~v1_relat_1(C_1339))), inference(demodulation, [status(thm), theory('equality')], [c_20959, c_20959, c_17048])).
% 11.51/4.51  tff(c_21493, plain, (![A_1340]: (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), A_1340) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11929, c_21489])).
% 11.51/4.51  tff(c_21500, plain, (![A_1340]: (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~r1_tarski('#skF_1', A_1340))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_17275, c_6, c_21493])).
% 11.51/4.51  tff(c_21628, plain, (![A_1359]: (~r1_tarski('#skF_1', A_1359))), inference(splitLeft, [status(thm)], [c_21500])).
% 11.51/4.51  tff(c_21633, plain, $false, inference(resolution, [status(thm)], [c_6, c_21628])).
% 11.51/4.51  tff(c_21634, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_21500])).
% 11.51/4.51  tff(c_21644, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_21634, c_16])).
% 11.51/4.51  tff(c_21654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17009, c_21644])).
% 11.51/4.51  tff(c_21655, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_17001])).
% 11.51/4.51  tff(c_21664, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21655, c_11929])).
% 11.51/4.51  tff(c_21685, plain, (![C_1360, A_1361, B_1362]: (m1_subset_1(C_1360, k1_zfmisc_1(k2_zfmisc_1(A_1361, B_1362))) | ~r1_tarski(k2_relat_1(C_1360), B_1362) | ~r1_tarski(k1_relat_1(C_1360), A_1361) | ~v1_relat_1(C_1360))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.51/4.51  tff(c_24053, plain, (![A_1508, B_1509, C_1510]: (k1_relset_1(A_1508, B_1509, C_1510)=k1_relat_1(C_1510) | ~r1_tarski(k2_relat_1(C_1510), B_1509) | ~r1_tarski(k1_relat_1(C_1510), A_1508) | ~v1_relat_1(C_1510))), inference(resolution, [status(thm)], [c_21685, c_36])).
% 11.51/4.51  tff(c_24055, plain, (![A_1508, B_1509]: (k1_relset_1(A_1508, B_1509, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_4', B_1509) | ~r1_tarski(k1_relat_1('#skF_4'), A_1508) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_24053])).
% 11.51/4.51  tff(c_24340, plain, (![A_1518, B_1519]: (k1_relset_1(A_1518, B_1519, '#skF_4')='#skF_1' | ~r1_tarski('#skF_4', B_1519) | ~r1_tarski('#skF_1', A_1518))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_21834, c_21834, c_24055])).
% 11.51/4.51  tff(c_24423, plain, (![A_1526]: (k1_relset_1(A_1526, '#skF_4', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_1526))), inference(resolution, [status(thm)], [c_6, c_24340])).
% 11.51/4.51  tff(c_24428, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_24423])).
% 11.51/4.51  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.51/4.51  tff(c_11463, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11445, c_10])).
% 11.51/4.51  tff(c_11469, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_75, c_11463])).
% 11.51/4.51  tff(c_11498, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_11469])).
% 11.51/4.51  tff(c_23799, plain, (![C_1495, A_1496, B_1497]: (r1_tarski(C_1495, k2_zfmisc_1(A_1496, B_1497)) | ~r1_tarski(k2_relat_1(C_1495), B_1497) | ~r1_tarski(k1_relat_1(C_1495), A_1496) | ~v1_relat_1(C_1495))), inference(resolution, [status(thm)], [c_21685, c_16])).
% 11.51/4.51  tff(c_24456, plain, (![C_1528, A_1529]: (r1_tarski(C_1528, k2_zfmisc_1(A_1529, k2_relat_1(C_1528))) | ~r1_tarski(k1_relat_1(C_1528), A_1529) | ~v1_relat_1(C_1528))), inference(resolution, [status(thm)], [c_6, c_23799])).
% 11.51/4.51  tff(c_24519, plain, (![A_1529]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1529, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_4'), A_1529) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21664, c_24456])).
% 11.51/4.51  tff(c_24554, plain, (![A_1529]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1529, '#skF_4')) | ~r1_tarski('#skF_1', A_1529))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_21834, c_24519])).
% 11.51/4.51  tff(c_21895, plain, (![B_1374, C_1375, A_1376]: (k1_xboole_0=B_1374 | v1_funct_2(C_1375, A_1376, B_1374) | k1_relset_1(A_1376, B_1374, C_1375)!=A_1376 | ~m1_subset_1(C_1375, k1_zfmisc_1(k2_zfmisc_1(A_1376, B_1374))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_25005, plain, (![B_1543, A_1544, A_1545]: (k1_xboole_0=B_1543 | v1_funct_2(A_1544, A_1545, B_1543) | k1_relset_1(A_1545, B_1543, A_1544)!=A_1545 | ~r1_tarski(A_1544, k2_zfmisc_1(A_1545, B_1543)))), inference(resolution, [status(thm)], [c_18, c_21895])).
% 11.51/4.51  tff(c_25008, plain, (![A_1529]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_4', A_1529, '#skF_4') | k1_relset_1(A_1529, '#skF_4', '#skF_4')!=A_1529 | ~r1_tarski('#skF_1', A_1529))), inference(resolution, [status(thm)], [c_24554, c_25005])).
% 11.51/4.51  tff(c_25152, plain, (![A_1550]: (v1_funct_2('#skF_4', A_1550, '#skF_4') | k1_relset_1(A_1550, '#skF_4', '#skF_4')!=A_1550 | ~r1_tarski('#skF_1', A_1550))), inference(negUnitSimplification, [status(thm)], [c_11498, c_25008])).
% 11.51/4.51  tff(c_21666, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21655, c_4423])).
% 11.51/4.51  tff(c_25158, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_25152, c_21666])).
% 11.51/4.51  tff(c_25166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_24428, c_25158])).
% 11.51/4.51  tff(c_25168, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_11469])).
% 11.51/4.51  tff(c_25167, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_11469])).
% 11.51/4.51  tff(c_25186, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25168, c_25167])).
% 11.51/4.51  tff(c_25179, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25167, c_25167, c_14])).
% 11.51/4.51  tff(c_25269, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25186, c_25186, c_25179])).
% 11.51/4.51  tff(c_25388, plain, (![A_1574, A_1575, B_1576]: (v4_relat_1(A_1574, A_1575) | ~r1_tarski(A_1574, k2_zfmisc_1(A_1575, B_1576)))), inference(resolution, [status(thm)], [c_18, c_11472])).
% 11.51/4.51  tff(c_25415, plain, (![A_1575, B_1576]: (v4_relat_1(k2_zfmisc_1(A_1575, B_1576), A_1575))), inference(resolution, [status(thm)], [c_6, c_25388])).
% 11.51/4.51  tff(c_4399, plain, (![B_370, A_371]: (r1_tarski(k1_relat_1(B_370), A_371) | ~v4_relat_1(B_370, A_371) | ~v1_relat_1(B_370))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.51/4.51  tff(c_4409, plain, (![B_370]: (k1_relat_1(B_370)=k1_xboole_0 | ~v4_relat_1(B_370, k1_xboole_0) | ~v1_relat_1(B_370))), inference(resolution, [status(thm)], [c_4399, c_4374])).
% 11.51/4.51  tff(c_25174, plain, (![B_370]: (k1_relat_1(B_370)='#skF_1' | ~v4_relat_1(B_370, '#skF_1') | ~v1_relat_1(B_370))), inference(demodulation, [status(thm), theory('equality')], [c_25167, c_25167, c_4409])).
% 11.51/4.51  tff(c_25506, plain, (![B_1584]: (k1_relat_1(B_1584)='#skF_4' | ~v4_relat_1(B_1584, '#skF_4') | ~v1_relat_1(B_1584))), inference(demodulation, [status(thm), theory('equality')], [c_25186, c_25186, c_25174])).
% 11.51/4.51  tff(c_25510, plain, (![B_1576]: (k1_relat_1(k2_zfmisc_1('#skF_4', B_1576))='#skF_4' | ~v1_relat_1(k2_zfmisc_1('#skF_4', B_1576)))), inference(resolution, [status(thm)], [c_25415, c_25506])).
% 11.51/4.51  tff(c_25521, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_25269, c_25510])).
% 11.51/4.51  tff(c_25177, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25167, c_25167, c_12])).
% 11.51/4.51  tff(c_25245, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25186, c_25186, c_25177])).
% 11.51/4.51  tff(c_25301, plain, (![A_1556, B_1557, C_1558]: (k1_relset_1(A_1556, B_1557, C_1558)=k1_relat_1(C_1558) | ~m1_subset_1(C_1558, k1_zfmisc_1(k2_zfmisc_1(A_1556, B_1557))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.51/4.51  tff(c_25717, plain, (![A_1607, C_1608]: (k1_relset_1(A_1607, '#skF_4', C_1608)=k1_relat_1(C_1608) | ~m1_subset_1(C_1608, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_25245, c_25301])).
% 11.51/4.51  tff(c_25719, plain, (![A_1607]: (k1_relset_1(A_1607, '#skF_4', '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11449, c_25717])).
% 11.51/4.51  tff(c_25724, plain, (![A_1607]: (k1_relset_1(A_1607, '#skF_4', '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25521, c_25719])).
% 11.51/4.51  tff(c_76, plain, (![B_36]: (k2_zfmisc_1(k1_xboole_0, B_36)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.51/4.51  tff(c_80, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_76, c_30])).
% 11.51/4.51  tff(c_7068, plain, (![A_584, B_583]: (v5_relat_1(k2_zfmisc_1(A_584, B_583), B_583))), inference(resolution, [status(thm)], [c_6, c_7038])).
% 11.51/4.51  tff(c_7091, plain, (![B_591]: (k2_relat_1(B_591)=k1_xboole_0 | ~v5_relat_1(B_591, k1_xboole_0) | ~v1_relat_1(B_591))), inference(resolution, [status(thm)], [c_4447, c_4374])).
% 11.51/4.51  tff(c_7095, plain, (![A_584]: (k2_relat_1(k2_zfmisc_1(A_584, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_584, k1_xboole_0)))), inference(resolution, [status(thm)], [c_7068, c_7091])).
% 11.51/4.51  tff(c_7106, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12, c_12, c_7095])).
% 11.51/4.51  tff(c_25169, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25167, c_25167, c_7106])).
% 11.51/4.51  tff(c_25208, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25186, c_25186, c_25169])).
% 11.51/4.51  tff(c_25181, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_25167, c_8])).
% 11.51/4.51  tff(c_25228, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_25186, c_25181])).
% 11.51/4.51  tff(c_25376, plain, (![A_1571, B_1572, C_1573]: (k2_relset_1(A_1571, B_1572, C_1573)=k2_relat_1(C_1573) | ~m1_subset_1(C_1573, k1_zfmisc_1(k2_zfmisc_1(A_1571, B_1572))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.51/4.51  tff(c_25761, plain, (![A_1614, B_1615, A_1616]: (k2_relset_1(A_1614, B_1615, A_1616)=k2_relat_1(A_1616) | ~r1_tarski(A_1616, k2_zfmisc_1(A_1614, B_1615)))), inference(resolution, [status(thm)], [c_18, c_25376])).
% 11.51/4.51  tff(c_25771, plain, (![A_1614, B_1615]: (k2_relset_1(A_1614, B_1615, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_25228, c_25761])).
% 11.51/4.51  tff(c_25785, plain, (![A_1614, B_1615]: (k2_relset_1(A_1614, B_1615, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25208, c_25771])).
% 11.51/4.51  tff(c_25194, plain, (k2_relset_1('#skF_4', '#skF_2', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25186, c_7027])).
% 11.51/4.51  tff(c_25789, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25785, c_25194])).
% 11.51/4.51  tff(c_46, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.51/4.51  tff(c_68, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_46])).
% 11.51/4.51  tff(c_25647, plain, (![C_1597, B_1598]: (v1_funct_2(C_1597, '#skF_4', B_1598) | k1_relset_1('#skF_4', B_1598, C_1597)!='#skF_4' | ~m1_subset_1(C_1597, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_25168, c_25168, c_25168, c_25168, c_68])).
% 11.51/4.51  tff(c_25655, plain, (![B_1599]: (v1_funct_2('#skF_4', '#skF_4', B_1599) | k1_relset_1('#skF_4', B_1599, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_11449, c_25647])).
% 11.51/4.51  tff(c_25195, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25186, c_4423])).
% 11.51/4.51  tff(c_25671, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_25655, c_25195])).
% 11.51/4.51  tff(c_25797, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25789, c_25671])).
% 11.51/4.51  tff(c_25802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25724, c_25797])).
% 11.51/4.51  tff(c_25803, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 11.51/4.51  tff(c_26244, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26229, c_25803])).
% 11.51/4.51  tff(c_26263, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_26117, c_26244])).
% 11.51/4.51  tff(c_26270, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_26263])).
% 11.51/4.51  tff(c_26274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_25942, c_26270])).
% 11.51/4.51  tff(c_26275, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_56])).
% 11.51/4.51  tff(c_26277, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_26275, c_8])).
% 11.51/4.51  tff(c_26289, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26275, c_26275, c_14])).
% 11.51/4.51  tff(c_26276, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 11.51/4.51  tff(c_26282, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26275, c_26276])).
% 11.51/4.51  tff(c_26319, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26289, c_26282, c_60])).
% 11.51/4.51  tff(c_26321, plain, (![A_1678, B_1679]: (r1_tarski(A_1678, B_1679) | ~m1_subset_1(A_1678, k1_zfmisc_1(B_1679)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.51/4.51  tff(c_26329, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_26319, c_26321])).
% 11.51/4.51  tff(c_26341, plain, (![B_1682, A_1683]: (B_1682=A_1683 | ~r1_tarski(B_1682, A_1683) | ~r1_tarski(A_1683, B_1682))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.51/4.51  tff(c_26343, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_26329, c_26341])).
% 11.51/4.51  tff(c_26352, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26277, c_26343])).
% 11.51/4.51  tff(c_26360, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26352, c_26319])).
% 11.51/4.51  tff(c_26365, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26352, c_26352, c_26289])).
% 11.51/4.51  tff(c_26478, plain, (![C_1694, A_1695, B_1696]: (v4_relat_1(C_1694, A_1695) | ~m1_subset_1(C_1694, k1_zfmisc_1(k2_zfmisc_1(A_1695, B_1696))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.51/4.51  tff(c_26528, plain, (![A_1707, A_1708, B_1709]: (v4_relat_1(A_1707, A_1708) | ~r1_tarski(A_1707, k2_zfmisc_1(A_1708, B_1709)))), inference(resolution, [status(thm)], [c_18, c_26478])).
% 11.51/4.51  tff(c_26550, plain, (![A_1708, B_1709]: (v4_relat_1(k2_zfmisc_1(A_1708, B_1709), A_1708))), inference(resolution, [status(thm)], [c_6, c_26528])).
% 11.51/4.51  tff(c_26515, plain, (![B_1705, A_1706]: (r1_tarski(k1_relat_1(B_1705), A_1706) | ~v4_relat_1(B_1705, A_1706) | ~v1_relat_1(B_1705))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.51/4.51  tff(c_26354, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(resolution, [status(thm)], [c_26277, c_26341])).
% 11.51/4.51  tff(c_26440, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26352, c_26352, c_26354])).
% 11.51/4.51  tff(c_26560, plain, (![B_1712]: (k1_relat_1(B_1712)='#skF_4' | ~v4_relat_1(B_1712, '#skF_4') | ~v1_relat_1(B_1712))), inference(resolution, [status(thm)], [c_26515, c_26440])).
% 11.51/4.51  tff(c_26564, plain, (![B_1709]: (k1_relat_1(k2_zfmisc_1('#skF_4', B_1709))='#skF_4' | ~v1_relat_1(k2_zfmisc_1('#skF_4', B_1709)))), inference(resolution, [status(thm)], [c_26550, c_26560])).
% 11.51/4.51  tff(c_26575, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26365, c_26564])).
% 11.51/4.51  tff(c_26811, plain, (![A_1739, B_1740, C_1741]: (k1_relset_1(A_1739, B_1740, C_1741)=k1_relat_1(C_1741) | ~m1_subset_1(C_1741, k1_zfmisc_1(k2_zfmisc_1(A_1739, B_1740))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.51/4.51  tff(c_26850, plain, (![B_1746, C_1747]: (k1_relset_1('#skF_4', B_1746, C_1747)=k1_relat_1(C_1747) | ~m1_subset_1(C_1747, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_26365, c_26811])).
% 11.51/4.51  tff(c_26852, plain, (![B_1746]: (k1_relset_1('#skF_4', B_1746, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26360, c_26850])).
% 11.51/4.51  tff(c_26857, plain, (![B_1746]: (k1_relset_1('#skF_4', B_1746, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26575, c_26852])).
% 11.51/4.51  tff(c_26368, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26352, c_26275])).
% 11.51/4.51  tff(c_27122, plain, (![C_1779, B_1780]: (v1_funct_2(C_1779, '#skF_4', B_1780) | k1_relset_1('#skF_4', B_1780, C_1779)!='#skF_4' | ~m1_subset_1(C_1779, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_26368, c_26368, c_26368, c_26368, c_68])).
% 11.51/4.51  tff(c_27124, plain, (![B_1780]: (v1_funct_2('#skF_4', '#skF_4', B_1780) | k1_relset_1('#skF_4', B_1780, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_26360, c_27122])).
% 11.51/4.51  tff(c_27130, plain, (![B_1780]: (v1_funct_2('#skF_4', '#skF_4', B_1780))), inference(demodulation, [status(thm), theory('equality')], [c_26857, c_27124])).
% 11.51/4.51  tff(c_26379, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26352, c_26352, c_66])).
% 11.51/4.51  tff(c_26380, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_26379])).
% 11.51/4.51  tff(c_27135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27130, c_26380])).
% 11.51/4.51  tff(c_27136, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_26379])).
% 11.51/4.51  tff(c_27212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26360, c_26365, c_27136])).
% 11.51/4.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.51/4.51  
% 11.51/4.51  Inference rules
% 11.51/4.51  ----------------------
% 11.51/4.51  #Ref     : 0
% 11.51/4.51  #Sup     : 5511
% 11.51/4.51  #Fact    : 0
% 11.51/4.51  #Define  : 0
% 11.51/4.51  #Split   : 82
% 11.51/4.51  #Chain   : 0
% 11.51/4.51  #Close   : 0
% 11.51/4.51  
% 11.51/4.51  Ordering : KBO
% 11.51/4.51  
% 11.51/4.51  Simplification rules
% 11.51/4.51  ----------------------
% 11.51/4.51  #Subsume      : 1514
% 11.51/4.51  #Demod        : 7448
% 11.51/4.51  #Tautology    : 2315
% 11.51/4.51  #SimpNegUnit  : 335
% 11.51/4.51  #BackRed      : 757
% 11.51/4.51  
% 11.51/4.51  #Partial instantiations: 0
% 11.51/4.51  #Strategies tried      : 1
% 11.51/4.51  
% 11.51/4.51  Timing (in seconds)
% 11.51/4.51  ----------------------
% 11.51/4.51  Preprocessing        : 0.33
% 11.51/4.51  Parsing              : 0.17
% 11.51/4.51  CNF conversion       : 0.02
% 11.51/4.51  Main loop            : 3.32
% 11.51/4.51  Inferencing          : 0.94
% 11.51/4.51  Reduction            : 1.23
% 11.51/4.51  Demodulation         : 0.88
% 11.51/4.51  BG Simplification    : 0.09
% 11.51/4.51  Subsumption          : 0.80
% 11.51/4.51  Abstraction          : 0.12
% 11.51/4.51  MUC search           : 0.00
% 11.51/4.51  Cooper               : 0.00
% 11.51/4.51  Total                : 3.79
% 11.51/4.51  Index Insertion      : 0.00
% 11.70/4.51  Index Deletion       : 0.00
% 11.70/4.51  Index Matching       : 0.00
% 11.70/4.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
