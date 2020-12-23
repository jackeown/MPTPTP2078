%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:11 EST 2020

% Result     : Theorem 9.14s
% Output     : CNFRefutation 9.14s
% Verified   : 
% Statistics : Number of formulae       :  251 (1890 expanded)
%              Number of leaves         :   43 ( 628 expanded)
%              Depth                    :   14
%              Number of atoms          :  430 (5380 expanded)
%              Number of equality atoms :  136 (1683 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_140,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_102,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(c_32,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_14664,plain,(
    ! [B_1104,A_1105] :
      ( v1_relat_1(B_1104)
      | ~ m1_subset_1(B_1104,k1_zfmisc_1(A_1105))
      | ~ v1_relat_1(A_1105) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14676,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_14664])).

tff(c_14686,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14676])).

tff(c_14801,plain,(
    ! [C_1123,A_1124,B_1125] :
      ( v4_relat_1(C_1123,A_1124)
      | ~ m1_subset_1(C_1123,k1_zfmisc_1(k2_zfmisc_1(A_1124,B_1125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14820,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_14801])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_15086,plain,(
    ! [A_1165,B_1166,C_1167] :
      ( k2_relset_1(A_1165,B_1166,C_1167) = k2_relat_1(C_1167)
      | ~ m1_subset_1(C_1167,k1_zfmisc_1(k2_zfmisc_1(A_1165,B_1166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_15105,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_15086])).

tff(c_64,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_15107,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15105,c_64])).

tff(c_15256,plain,(
    ! [C_1180,A_1181,B_1182] :
      ( m1_subset_1(C_1180,k1_zfmisc_1(k2_zfmisc_1(A_1181,B_1182)))
      | ~ r1_tarski(k2_relat_1(C_1180),B_1182)
      | ~ r1_tarski(k1_relat_1(C_1180),A_1181)
      | ~ v1_relat_1(C_1180) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_240,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_252,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_240])).

tff(c_262,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_252])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_79,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_8421,plain,(
    ! [A_646,B_647,C_648] :
      ( k1_relset_1(A_646,B_647,C_648) = k1_relat_1(C_648)
      | ~ m1_subset_1(C_648,k1_zfmisc_1(k2_zfmisc_1(A_646,B_647))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8440,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_8421])).

tff(c_8833,plain,(
    ! [B_691,A_692,C_693] :
      ( k1_xboole_0 = B_691
      | k1_relset_1(A_692,B_691,C_693) = A_692
      | ~ v1_funct_2(C_693,A_692,B_691)
      | ~ m1_subset_1(C_693,k1_zfmisc_1(k2_zfmisc_1(A_692,B_691))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8846,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_8833])).

tff(c_8859,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8440,c_8846])).

tff(c_8860,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_8859])).

tff(c_4783,plain,(
    ! [A_376,B_377,C_378] :
      ( k1_relset_1(A_376,B_377,C_378) = k1_relat_1(C_378)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4802,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_4783])).

tff(c_5131,plain,(
    ! [B_417,A_418,C_419] :
      ( k1_xboole_0 = B_417
      | k1_relset_1(A_418,B_417,C_419) = A_418
      | ~ v1_funct_2(C_419,A_418,B_417)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(A_418,B_417))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5144,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_5131])).

tff(c_5157,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4802,c_5144])).

tff(c_5158,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_5157])).

tff(c_4825,plain,(
    ! [A_386,B_387,C_388] :
      ( k2_relset_1(A_386,B_387,C_388) = k2_relat_1(C_388)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4844,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_4825])).

tff(c_4847,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4844,c_64])).

tff(c_4984,plain,(
    ! [C_399,A_400,B_401] :
      ( m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401)))
      | ~ r1_tarski(k2_relat_1(C_399),B_401)
      | ~ r1_tarski(k1_relat_1(C_399),A_400)
      | ~ v1_relat_1(C_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7115,plain,(
    ! [C_558,A_559,B_560] :
      ( r1_tarski(C_558,k2_zfmisc_1(A_559,B_560))
      | ~ r1_tarski(k2_relat_1(C_558),B_560)
      | ~ r1_tarski(k1_relat_1(C_558),A_559)
      | ~ v1_relat_1(C_558) ) ),
    inference(resolution,[status(thm)],[c_4984,c_20])).

tff(c_7117,plain,(
    ! [A_559] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_559,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_559)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4847,c_7115])).

tff(c_7125,plain,(
    ! [A_561] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_561,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_5158,c_7117])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4800,plain,(
    ! [A_376,B_377,A_8] :
      ( k1_relset_1(A_376,B_377,A_8) = k1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_376,B_377)) ) ),
    inference(resolution,[status(thm)],[c_22,c_4783])).

tff(c_7128,plain,(
    ! [A_561] :
      ( k1_relset_1(A_561,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_561) ) ),
    inference(resolution,[status(thm)],[c_7125,c_4800])).

tff(c_7162,plain,(
    ! [A_562] :
      ( k1_relset_1(A_562,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5158,c_7128])).

tff(c_7167,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_7162])).

tff(c_263,plain,(
    ! [C_60,B_61,A_62] :
      ( ~ v1_xboole_0(C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4527,plain,(
    ! [B_344,A_345,A_346] :
      ( ~ v1_xboole_0(B_344)
      | ~ r2_hidden(A_345,A_346)
      | ~ r1_tarski(A_346,B_344) ) ),
    inference(resolution,[status(thm)],[c_22,c_263])).

tff(c_4531,plain,(
    ! [B_347,A_348] :
      ( ~ v1_xboole_0(B_347)
      | ~ r1_tarski(A_348,B_347)
      | k1_xboole_0 = A_348 ) ),
    inference(resolution,[status(thm)],[c_4,c_4527])).

tff(c_4555,plain,
    ( ~ v1_xboole_0('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_4531])).

tff(c_4643,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4555])).

tff(c_7123,plain,(
    ! [A_559] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_559,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_559) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_5158,c_7117])).

tff(c_5256,plain,(
    ! [B_428,C_429,A_430] :
      ( k1_xboole_0 = B_428
      | v1_funct_2(C_429,A_430,B_428)
      | k1_relset_1(A_430,B_428,C_429) != A_430
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(A_430,B_428))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_7501,plain,(
    ! [B_581,A_582,A_583] :
      ( k1_xboole_0 = B_581
      | v1_funct_2(A_582,A_583,B_581)
      | k1_relset_1(A_583,B_581,A_582) != A_583
      | ~ r1_tarski(A_582,k2_zfmisc_1(A_583,B_581)) ) ),
    inference(resolution,[status(thm)],[c_22,c_5256])).

tff(c_7533,plain,(
    ! [A_559] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_559,'#skF_4')
      | k1_relset_1(A_559,'#skF_4','#skF_5') != A_559
      | ~ r1_tarski('#skF_2',A_559) ) ),
    inference(resolution,[status(thm)],[c_7123,c_7501])).

tff(c_7631,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7533])).

tff(c_7711,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7631,c_2])).

tff(c_7714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4643,c_7711])).

tff(c_8058,plain,(
    ! [A_600] :
      ( v1_funct_2('#skF_5',A_600,'#skF_4')
      | k1_relset_1(A_600,'#skF_4','#skF_5') != A_600
      | ~ r1_tarski('#skF_2',A_600) ) ),
    inference(splitRight,[status(thm)],[c_7533])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60])).

tff(c_142,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_8064,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_8058,c_142])).

tff(c_8069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_7167,c_8064])).

tff(c_8071,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4555])).

tff(c_4556,plain,(
    ! [B_4] :
      ( ~ v1_xboole_0(B_4)
      | k1_xboole_0 = B_4 ) ),
    inference(resolution,[status(thm)],[c_10,c_4531])).

tff(c_8075,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8071,c_4556])).

tff(c_18,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_115,plain,(
    ! [A_44,B_45] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_44,B_45)),A_44) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_119,plain,(
    ! [B_45] : k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_45)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_115,c_12])).

tff(c_127,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_119])).

tff(c_16,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,(
    ! [A_6] : r1_tarski(k1_relat_1(k1_xboole_0),A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_134,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_122])).

tff(c_8085,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8075,c_134])).

tff(c_207,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_224,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_207])).

tff(c_4520,plain,(
    ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_8103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8085,c_4520])).

tff(c_8104,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_8288,plain,(
    ! [A_630,B_631,C_632] :
      ( k2_relset_1(A_630,B_631,C_632) = k2_relat_1(C_632)
      | ~ m1_subset_1(C_632,k1_zfmisc_1(k2_zfmisc_1(A_630,B_631))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8298,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_8288])).

tff(c_8308,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8104,c_8298])).

tff(c_8586,plain,(
    ! [C_664,A_665,B_666] :
      ( m1_subset_1(C_664,k1_zfmisc_1(k2_zfmisc_1(A_665,B_666)))
      | ~ r1_tarski(k2_relat_1(C_664),B_666)
      | ~ r1_tarski(k1_relat_1(C_664),A_665)
      | ~ v1_relat_1(C_664) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    ! [A_25,B_26,C_27] :
      ( k1_relset_1(A_25,B_26,C_27) = k1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_11164,plain,(
    ! [A_851,B_852,C_853] :
      ( k1_relset_1(A_851,B_852,C_853) = k1_relat_1(C_853)
      | ~ r1_tarski(k2_relat_1(C_853),B_852)
      | ~ r1_tarski(k1_relat_1(C_853),A_851)
      | ~ v1_relat_1(C_853) ) ),
    inference(resolution,[status(thm)],[c_8586,c_40])).

tff(c_11166,plain,(
    ! [A_851,B_852] :
      ( k1_relset_1(A_851,B_852,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_4',B_852)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_851)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8308,c_11164])).

tff(c_11173,plain,(
    ! [A_854,B_855] :
      ( k1_relset_1(A_854,B_855,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_4',B_855)
      | ~ r1_tarski('#skF_2',A_854) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_8860,c_8860,c_11166])).

tff(c_11178,plain,(
    ! [A_856] :
      ( k1_relset_1(A_856,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_856) ) ),
    inference(resolution,[status(thm)],[c_10,c_11173])).

tff(c_11183,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_11178])).

tff(c_10530,plain,(
    ! [C_806,A_807,B_808] :
      ( r1_tarski(C_806,k2_zfmisc_1(A_807,B_808))
      | ~ r1_tarski(k2_relat_1(C_806),B_808)
      | ~ r1_tarski(k1_relat_1(C_806),A_807)
      | ~ v1_relat_1(C_806) ) ),
    inference(resolution,[status(thm)],[c_8586,c_20])).

tff(c_10532,plain,(
    ! [A_807,B_808] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_807,B_808))
      | ~ r1_tarski('#skF_4',B_808)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_807)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8308,c_10530])).

tff(c_10537,plain,(
    ! [A_807,B_808] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_807,B_808))
      | ~ r1_tarski('#skF_4',B_808)
      | ~ r1_tarski('#skF_2',A_807) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_8860,c_10532])).

tff(c_8736,plain,(
    ! [B_680,C_681,A_682] :
      ( k1_xboole_0 = B_680
      | v1_funct_2(C_681,A_682,B_680)
      | k1_relset_1(A_682,B_680,C_681) != A_682
      | ~ m1_subset_1(C_681,k1_zfmisc_1(k2_zfmisc_1(A_682,B_680))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_11406,plain,(
    ! [B_865,A_866,A_867] :
      ( k1_xboole_0 = B_865
      | v1_funct_2(A_866,A_867,B_865)
      | k1_relset_1(A_867,B_865,A_866) != A_867
      | ~ r1_tarski(A_866,k2_zfmisc_1(A_867,B_865)) ) ),
    inference(resolution,[status(thm)],[c_22,c_8736])).

tff(c_11540,plain,(
    ! [B_872,A_873] :
      ( k1_xboole_0 = B_872
      | v1_funct_2('#skF_5',A_873,B_872)
      | k1_relset_1(A_873,B_872,'#skF_5') != A_873
      | ~ r1_tarski('#skF_4',B_872)
      | ~ r1_tarski('#skF_2',A_873) ) ),
    inference(resolution,[status(thm)],[c_10537,c_11406])).

tff(c_11549,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_11540,c_142])).

tff(c_11554,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_11183,c_11549])).

tff(c_10200,plain,(
    ! [C_789,A_790] :
      ( m1_subset_1(C_789,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_789),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_789),A_790)
      | ~ v1_relat_1(C_789) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8586])).

tff(c_10202,plain,(
    ! [A_790] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_4',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_790)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8308,c_10200])).

tff(c_10204,plain,(
    ! [A_790] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_4',k1_xboole_0)
      | ~ r1_tarski('#skF_2',A_790) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_8860,c_10202])).

tff(c_10205,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_10204])).

tff(c_11583,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11554,c_10205])).

tff(c_11644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11583])).

tff(c_11646,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_10204])).

tff(c_8170,plain,(
    ! [B_608,A_609,A_610] :
      ( ~ v1_xboole_0(B_608)
      | ~ r2_hidden(A_609,A_610)
      | ~ r1_tarski(A_610,B_608) ) ),
    inference(resolution,[status(thm)],[c_22,c_263])).

tff(c_8173,plain,(
    ! [B_608,A_1] :
      ( ~ v1_xboole_0(B_608)
      | ~ r1_tarski(A_1,B_608)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_8170])).

tff(c_11663,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11646,c_8173])).

tff(c_11683,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11663])).

tff(c_8224,plain,(
    ! [C_617,A_618,B_619] :
      ( v4_relat_1(C_617,A_618)
      | ~ m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(A_618,B_619))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8329,plain,(
    ! [C_635,A_636] :
      ( v4_relat_1(C_635,A_636)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8224])).

tff(c_8337,plain,(
    ! [A_8,A_636] :
      ( v4_relat_1(A_8,A_636)
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_8329])).

tff(c_8869,plain,(
    ! [A_16] :
      ( r1_tarski('#skF_2',A_16)
      | ~ v4_relat_1('#skF_5',A_16)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8860,c_30])).

tff(c_8886,plain,(
    ! [A_694] :
      ( r1_tarski('#skF_2',A_694)
      | ~ v4_relat_1('#skF_5',A_694) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_8869])).

tff(c_8898,plain,(
    ! [A_636] :
      ( r1_tarski('#skF_2',A_636)
      | ~ r1_tarski('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8337,c_8886])).

tff(c_8916,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8898])).

tff(c_11713,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11683,c_8916])).

tff(c_12128,plain,(
    ! [A_892] : k2_zfmisc_1(A_892,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11683,c_11683,c_16])).

tff(c_11741,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11683,c_134])).

tff(c_11923,plain,(
    ! [C_879,A_880,B_881] :
      ( r1_tarski(C_879,k2_zfmisc_1(A_880,B_881))
      | ~ r1_tarski(k2_relat_1(C_879),B_881)
      | ~ r1_tarski(k1_relat_1(C_879),A_880)
      | ~ v1_relat_1(C_879) ) ),
    inference(resolution,[status(thm)],[c_8586,c_20])).

tff(c_11925,plain,(
    ! [A_880,B_881] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_880,B_881))
      | ~ r1_tarski('#skF_4',B_881)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_880)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8308,c_11923])).

tff(c_11930,plain,(
    ! [A_880,B_881] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_880,B_881))
      | ~ r1_tarski('#skF_2',A_880) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_8860,c_11741,c_11925])).

tff(c_12136,plain,(
    ! [A_892] :
      ( r1_tarski('#skF_5','#skF_4')
      | ~ r1_tarski('#skF_2',A_892) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12128,c_11930])).

tff(c_12279,plain,(
    ! [A_893] : ~ r1_tarski('#skF_2',A_893) ),
    inference(negUnitSimplification,[status(thm)],[c_11713,c_12136])).

tff(c_12284,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_12279])).

tff(c_12290,plain,(
    ! [A_894] : r1_tarski('#skF_2',A_894) ),
    inference(splitRight,[status(thm)],[c_8898])).

tff(c_12329,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12290,c_12])).

tff(c_12377,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12329,c_2])).

tff(c_12375,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_2',B_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12329,c_12329,c_18])).

tff(c_277,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_62,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_263])).

tff(c_289,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_12550,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12375,c_289])).

tff(c_12553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12377,c_12550])).

tff(c_12556,plain,(
    ! [A_906] : ~ r2_hidden(A_906,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_12561,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4,c_12556])).

tff(c_12573,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12561,c_79])).

tff(c_12555,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_12568,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12561,c_4])).

tff(c_13004,plain,(
    ! [B_956,A_957,A_958] :
      ( ~ v1_xboole_0(B_956)
      | ~ r2_hidden(A_957,A_958)
      | ~ r1_tarski(A_958,B_956) ) ),
    inference(resolution,[status(thm)],[c_22,c_263])).

tff(c_13008,plain,(
    ! [B_959,A_960] :
      ( ~ v1_xboole_0(B_959)
      | ~ r1_tarski(A_960,B_959)
      | A_960 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_12568,c_13004])).

tff(c_13034,plain,(
    ! [B_961] :
      ( ~ v1_xboole_0(B_961)
      | B_961 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_10,c_13008])).

tff(c_13041,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12555,c_13034])).

tff(c_153,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_165,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_153])).

tff(c_221,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_165,c_207])).

tff(c_12754,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_13052,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13041,c_12754])).

tff(c_13057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13052])).

tff(c_13058,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_13638,plain,(
    ! [B_1033,A_1034] :
      ( B_1033 = '#skF_5'
      | A_1034 = '#skF_5'
      | k2_zfmisc_1(A_1034,B_1033) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12561,c_12561,c_12561,c_14])).

tff(c_13641,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_13058,c_13638])).

tff(c_13650,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_12573,c_13641])).

tff(c_12567,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12561,c_12561,c_127])).

tff(c_13685,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13650,c_13650,c_12567])).

tff(c_12566,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12561,c_134])).

tff(c_13684,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13650,c_12566])).

tff(c_13230,plain,(
    ! [A_983,B_984,C_985] :
      ( k1_relset_1(A_983,B_984,C_985) = k1_relat_1(C_985)
      | ~ m1_subset_1(C_985,k1_zfmisc_1(k2_zfmisc_1(A_983,B_984))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14154,plain,(
    ! [A_1058,B_1059,A_1060] :
      ( k1_relset_1(A_1058,B_1059,A_1060) = k1_relat_1(A_1060)
      | ~ r1_tarski(A_1060,k2_zfmisc_1(A_1058,B_1059)) ) ),
    inference(resolution,[status(thm)],[c_22,c_13230])).

tff(c_14164,plain,(
    ! [A_1058,B_1059] : k1_relset_1(A_1058,B_1059,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_13684,c_14154])).

tff(c_14181,plain,(
    ! [A_1058,B_1059] : k1_relset_1(A_1058,B_1059,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13685,c_14164])).

tff(c_143,plain,(
    ! [A_48] : m1_subset_1(k6_relat_1(A_48),k1_zfmisc_1(k2_zfmisc_1(A_48,A_48))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_147,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_143])).

tff(c_163,plain,(
    r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_147,c_153])).

tff(c_174,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_163,c_12])).

tff(c_12565,plain,(
    k6_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12561,c_12561,c_174])).

tff(c_12645,plain,(
    ! [B_911] : k2_zfmisc_1('#skF_5',B_911) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12561,c_12561,c_18])).

tff(c_46,plain,(
    ! [A_34] : m1_subset_1(k6_relat_1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12658,plain,(
    m1_subset_1(k6_relat_1('#skF_5'),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12645,c_46])).

tff(c_12672,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12565,c_12658])).

tff(c_52,plain,(
    ! [C_37,B_36] :
      ( v1_funct_2(C_37,k1_xboole_0,B_36)
      | k1_relset_1(k1_xboole_0,B_36,C_37) != k1_xboole_0
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_74,plain,(
    ! [C_37,B_36] :
      ( v1_funct_2(C_37,k1_xboole_0,B_36)
      | k1_relset_1(k1_xboole_0,B_36,C_37) != k1_xboole_0
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52])).

tff(c_13518,plain,(
    ! [C_1019,B_1020] :
      ( v1_funct_2(C_1019,'#skF_5',B_1020)
      | k1_relset_1('#skF_5',B_1020,C_1019) != '#skF_5'
      | ~ m1_subset_1(C_1019,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12561,c_12561,c_12561,c_12561,c_74])).

tff(c_13524,plain,(
    ! [B_1020] :
      ( v1_funct_2('#skF_5','#skF_5',B_1020)
      | k1_relset_1('#skF_5',B_1020,'#skF_5') != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_12672,c_13518])).

tff(c_14567,plain,(
    ! [B_1020] : v1_funct_2('#skF_2','#skF_2',B_1020) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14181,c_13650,c_13650,c_13650,c_13650,c_13650,c_13524])).

tff(c_13691,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13650,c_142])).

tff(c_14571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14567,c_13691])).

tff(c_14572,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_15279,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_15256,c_14572])).

tff(c_15297,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14686,c_15107,c_15279])).

tff(c_15300,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_15297])).

tff(c_15304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14686,c_14820,c_15300])).

tff(c_15306,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_15323,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_3',B_7) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15306,c_15306,c_18])).

tff(c_15363,plain,(
    ! [A_1188,B_1189] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_1188,B_1189)),A_1188) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_15354,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ r1_tarski(A_5,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15306,c_15306,c_12])).

tff(c_15367,plain,(
    ! [B_1189] : k1_relat_1(k2_zfmisc_1('#skF_3',B_1189)) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_15363,c_15354])).

tff(c_15375,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15323,c_15367])).

tff(c_15305,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_15312,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15306,c_15305])).

tff(c_15362,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15323,c_15312,c_66])).

tff(c_15403,plain,(
    ! [A_1193,B_1194] :
      ( r1_tarski(A_1193,B_1194)
      | ~ m1_subset_1(A_1193,k1_zfmisc_1(B_1194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_15415,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_15362,c_15403])).

tff(c_15424,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_15415,c_15354])).

tff(c_15427,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15424,c_15362])).

tff(c_15784,plain,(
    ! [A_1248,B_1249,C_1250] :
      ( k1_relset_1(A_1248,B_1249,C_1250) = k1_relat_1(C_1250)
      | ~ m1_subset_1(C_1250,k1_zfmisc_1(k2_zfmisc_1(A_1248,B_1249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16191,plain,(
    ! [B_1294,C_1295] :
      ( k1_relset_1('#skF_3',B_1294,C_1295) = k1_relat_1(C_1295)
      | ~ m1_subset_1(C_1295,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15323,c_15784])).

tff(c_16193,plain,(
    ! [B_1294] : k1_relset_1('#skF_3',B_1294,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15427,c_16191])).

tff(c_16198,plain,(
    ! [B_1294] : k1_relset_1('#skF_3',B_1294,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15375,c_16193])).

tff(c_16098,plain,(
    ! [C_1281,B_1282] :
      ( v1_funct_2(C_1281,'#skF_3',B_1282)
      | k1_relset_1('#skF_3',B_1282,C_1281) != '#skF_3'
      | ~ m1_subset_1(C_1281,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15306,c_15306,c_15306,c_15306,c_74])).

tff(c_16106,plain,(
    ! [B_1283] :
      ( v1_funct_2('#skF_3','#skF_3',B_1283)
      | k1_relset_1('#skF_3',B_1283,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_15427,c_16098])).

tff(c_15390,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15312,c_15362,c_15323,c_15312,c_72])).

tff(c_15426,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15424,c_15390])).

tff(c_16117,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_16106,c_15426])).

tff(c_16223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16198,c_16117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.14/3.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.14/3.31  
% 9.14/3.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.14/3.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 9.14/3.31  
% 9.14/3.31  %Foreground sorts:
% 9.14/3.31  
% 9.14/3.31  
% 9.14/3.31  %Background operators:
% 9.14/3.31  
% 9.14/3.31  
% 9.14/3.31  %Foreground operators:
% 9.14/3.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.14/3.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.14/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.14/3.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.14/3.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.14/3.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.14/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.14/3.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.14/3.31  tff('#skF_5', type, '#skF_5': $i).
% 9.14/3.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.14/3.31  tff('#skF_2', type, '#skF_2': $i).
% 9.14/3.31  tff('#skF_3', type, '#skF_3': $i).
% 9.14/3.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.14/3.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.14/3.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.14/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.14/3.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.14/3.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.14/3.31  tff('#skF_4', type, '#skF_4': $i).
% 9.14/3.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.14/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.14/3.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.14/3.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.14/3.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.14/3.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.14/3.31  
% 9.14/3.34  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.14/3.34  tff(f_140, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 9.14/3.34  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.14/3.34  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.14/3.34  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.14/3.34  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.14/3.34  tff(f_100, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 9.14/3.34  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.14/3.34  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.14/3.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.14/3.34  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.14/3.34  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.14/3.34  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.14/3.34  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 9.14/3.34  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.14/3.34  tff(f_78, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 9.14/3.34  tff(f_44, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.14/3.34  tff(f_102, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.14/3.34  tff(c_32, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.14/3.34  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.14/3.34  tff(c_14664, plain, (![B_1104, A_1105]: (v1_relat_1(B_1104) | ~m1_subset_1(B_1104, k1_zfmisc_1(A_1105)) | ~v1_relat_1(A_1105))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.14/3.34  tff(c_14676, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_14664])).
% 9.14/3.34  tff(c_14686, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14676])).
% 9.14/3.34  tff(c_14801, plain, (![C_1123, A_1124, B_1125]: (v4_relat_1(C_1123, A_1124) | ~m1_subset_1(C_1123, k1_zfmisc_1(k2_zfmisc_1(A_1124, B_1125))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.14/3.34  tff(c_14820, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_14801])).
% 9.14/3.34  tff(c_30, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.14/3.34  tff(c_15086, plain, (![A_1165, B_1166, C_1167]: (k2_relset_1(A_1165, B_1166, C_1167)=k2_relat_1(C_1167) | ~m1_subset_1(C_1167, k1_zfmisc_1(k2_zfmisc_1(A_1165, B_1166))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.14/3.34  tff(c_15105, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_15086])).
% 9.14/3.34  tff(c_64, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.14/3.34  tff(c_15107, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15105, c_64])).
% 9.14/3.34  tff(c_15256, plain, (![C_1180, A_1181, B_1182]: (m1_subset_1(C_1180, k1_zfmisc_1(k2_zfmisc_1(A_1181, B_1182))) | ~r1_tarski(k2_relat_1(C_1180), B_1182) | ~r1_tarski(k1_relat_1(C_1180), A_1181) | ~v1_relat_1(C_1180))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.14/3.34  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.14/3.34  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.14/3.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.14/3.34  tff(c_240, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.14/3.34  tff(c_252, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_240])).
% 9.14/3.34  tff(c_262, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_252])).
% 9.14/3.34  tff(c_62, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.14/3.34  tff(c_79, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_62])).
% 9.14/3.34  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.14/3.34  tff(c_8421, plain, (![A_646, B_647, C_648]: (k1_relset_1(A_646, B_647, C_648)=k1_relat_1(C_648) | ~m1_subset_1(C_648, k1_zfmisc_1(k2_zfmisc_1(A_646, B_647))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.14/3.34  tff(c_8440, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_8421])).
% 9.14/3.34  tff(c_8833, plain, (![B_691, A_692, C_693]: (k1_xboole_0=B_691 | k1_relset_1(A_692, B_691, C_693)=A_692 | ~v1_funct_2(C_693, A_692, B_691) | ~m1_subset_1(C_693, k1_zfmisc_1(k2_zfmisc_1(A_692, B_691))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.14/3.34  tff(c_8846, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_8833])).
% 9.14/3.34  tff(c_8859, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8440, c_8846])).
% 9.14/3.34  tff(c_8860, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_79, c_8859])).
% 9.14/3.34  tff(c_4783, plain, (![A_376, B_377, C_378]: (k1_relset_1(A_376, B_377, C_378)=k1_relat_1(C_378) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.14/3.34  tff(c_4802, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_4783])).
% 9.14/3.34  tff(c_5131, plain, (![B_417, A_418, C_419]: (k1_xboole_0=B_417 | k1_relset_1(A_418, B_417, C_419)=A_418 | ~v1_funct_2(C_419, A_418, B_417) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(A_418, B_417))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.14/3.35  tff(c_5144, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_5131])).
% 9.14/3.35  tff(c_5157, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4802, c_5144])).
% 9.14/3.35  tff(c_5158, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_79, c_5157])).
% 9.14/3.35  tff(c_4825, plain, (![A_386, B_387, C_388]: (k2_relset_1(A_386, B_387, C_388)=k2_relat_1(C_388) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.14/3.35  tff(c_4844, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_4825])).
% 9.14/3.35  tff(c_4847, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4844, c_64])).
% 9.14/3.35  tff(c_4984, plain, (![C_399, A_400, B_401]: (m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))) | ~r1_tarski(k2_relat_1(C_399), B_401) | ~r1_tarski(k1_relat_1(C_399), A_400) | ~v1_relat_1(C_399))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.14/3.35  tff(c_20, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.14/3.35  tff(c_7115, plain, (![C_558, A_559, B_560]: (r1_tarski(C_558, k2_zfmisc_1(A_559, B_560)) | ~r1_tarski(k2_relat_1(C_558), B_560) | ~r1_tarski(k1_relat_1(C_558), A_559) | ~v1_relat_1(C_558))), inference(resolution, [status(thm)], [c_4984, c_20])).
% 9.14/3.35  tff(c_7117, plain, (![A_559]: (r1_tarski('#skF_5', k2_zfmisc_1(A_559, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_559) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4847, c_7115])).
% 9.14/3.35  tff(c_7125, plain, (![A_561]: (r1_tarski('#skF_5', k2_zfmisc_1(A_561, '#skF_4')) | ~r1_tarski('#skF_2', A_561))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_5158, c_7117])).
% 9.14/3.35  tff(c_22, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.14/3.35  tff(c_4800, plain, (![A_376, B_377, A_8]: (k1_relset_1(A_376, B_377, A_8)=k1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_376, B_377)))), inference(resolution, [status(thm)], [c_22, c_4783])).
% 9.14/3.35  tff(c_7128, plain, (![A_561]: (k1_relset_1(A_561, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_561))), inference(resolution, [status(thm)], [c_7125, c_4800])).
% 9.14/3.35  tff(c_7162, plain, (![A_562]: (k1_relset_1(A_562, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_562))), inference(demodulation, [status(thm), theory('equality')], [c_5158, c_7128])).
% 9.14/3.35  tff(c_7167, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_10, c_7162])).
% 9.14/3.35  tff(c_263, plain, (![C_60, B_61, A_62]: (~v1_xboole_0(C_60) | ~m1_subset_1(B_61, k1_zfmisc_1(C_60)) | ~r2_hidden(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.14/3.35  tff(c_4527, plain, (![B_344, A_345, A_346]: (~v1_xboole_0(B_344) | ~r2_hidden(A_345, A_346) | ~r1_tarski(A_346, B_344))), inference(resolution, [status(thm)], [c_22, c_263])).
% 9.14/3.35  tff(c_4531, plain, (![B_347, A_348]: (~v1_xboole_0(B_347) | ~r1_tarski(A_348, B_347) | k1_xboole_0=A_348)), inference(resolution, [status(thm)], [c_4, c_4527])).
% 9.14/3.35  tff(c_4555, plain, (~v1_xboole_0('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_4531])).
% 9.14/3.35  tff(c_4643, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_4555])).
% 9.14/3.35  tff(c_7123, plain, (![A_559]: (r1_tarski('#skF_5', k2_zfmisc_1(A_559, '#skF_4')) | ~r1_tarski('#skF_2', A_559))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_5158, c_7117])).
% 9.14/3.35  tff(c_5256, plain, (![B_428, C_429, A_430]: (k1_xboole_0=B_428 | v1_funct_2(C_429, A_430, B_428) | k1_relset_1(A_430, B_428, C_429)!=A_430 | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(A_430, B_428))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.14/3.35  tff(c_7501, plain, (![B_581, A_582, A_583]: (k1_xboole_0=B_581 | v1_funct_2(A_582, A_583, B_581) | k1_relset_1(A_583, B_581, A_582)!=A_583 | ~r1_tarski(A_582, k2_zfmisc_1(A_583, B_581)))), inference(resolution, [status(thm)], [c_22, c_5256])).
% 9.14/3.35  tff(c_7533, plain, (![A_559]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_559, '#skF_4') | k1_relset_1(A_559, '#skF_4', '#skF_5')!=A_559 | ~r1_tarski('#skF_2', A_559))), inference(resolution, [status(thm)], [c_7123, c_7501])).
% 9.14/3.35  tff(c_7631, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_7533])).
% 9.14/3.35  tff(c_7711, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7631, c_2])).
% 9.14/3.35  tff(c_7714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4643, c_7711])).
% 9.14/3.35  tff(c_8058, plain, (![A_600]: (v1_funct_2('#skF_5', A_600, '#skF_4') | k1_relset_1(A_600, '#skF_4', '#skF_5')!=A_600 | ~r1_tarski('#skF_2', A_600))), inference(splitRight, [status(thm)], [c_7533])).
% 9.14/3.35  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.14/3.35  tff(c_60, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.14/3.35  tff(c_72, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60])).
% 9.14/3.35  tff(c_142, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_72])).
% 9.14/3.35  tff(c_8064, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_8058, c_142])).
% 9.14/3.35  tff(c_8069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_7167, c_8064])).
% 9.14/3.35  tff(c_8071, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_4555])).
% 9.14/3.35  tff(c_4556, plain, (![B_4]: (~v1_xboole_0(B_4) | k1_xboole_0=B_4)), inference(resolution, [status(thm)], [c_10, c_4531])).
% 9.14/3.35  tff(c_8075, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8071, c_4556])).
% 9.14/3.35  tff(c_18, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.14/3.35  tff(c_115, plain, (![A_44, B_45]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_44, B_45)), A_44))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.14/3.35  tff(c_12, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.14/3.35  tff(c_119, plain, (![B_45]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_45))=k1_xboole_0)), inference(resolution, [status(thm)], [c_115, c_12])).
% 9.14/3.35  tff(c_127, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_119])).
% 9.14/3.35  tff(c_16, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.14/3.35  tff(c_122, plain, (![A_6]: (r1_tarski(k1_relat_1(k1_xboole_0), A_6))), inference(superposition, [status(thm), theory('equality')], [c_16, c_115])).
% 9.14/3.35  tff(c_134, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_122])).
% 9.14/3.35  tff(c_8085, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_8075, c_134])).
% 9.14/3.35  tff(c_207, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.14/3.35  tff(c_224, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_207])).
% 9.14/3.35  tff(c_4520, plain, (~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_224])).
% 9.14/3.35  tff(c_8103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8085, c_4520])).
% 9.14/3.35  tff(c_8104, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_224])).
% 9.14/3.35  tff(c_8288, plain, (![A_630, B_631, C_632]: (k2_relset_1(A_630, B_631, C_632)=k2_relat_1(C_632) | ~m1_subset_1(C_632, k1_zfmisc_1(k2_zfmisc_1(A_630, B_631))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.14/3.35  tff(c_8298, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_8288])).
% 9.14/3.35  tff(c_8308, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8104, c_8298])).
% 9.14/3.35  tff(c_8586, plain, (![C_664, A_665, B_666]: (m1_subset_1(C_664, k1_zfmisc_1(k2_zfmisc_1(A_665, B_666))) | ~r1_tarski(k2_relat_1(C_664), B_666) | ~r1_tarski(k1_relat_1(C_664), A_665) | ~v1_relat_1(C_664))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.14/3.35  tff(c_40, plain, (![A_25, B_26, C_27]: (k1_relset_1(A_25, B_26, C_27)=k1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.14/3.35  tff(c_11164, plain, (![A_851, B_852, C_853]: (k1_relset_1(A_851, B_852, C_853)=k1_relat_1(C_853) | ~r1_tarski(k2_relat_1(C_853), B_852) | ~r1_tarski(k1_relat_1(C_853), A_851) | ~v1_relat_1(C_853))), inference(resolution, [status(thm)], [c_8586, c_40])).
% 9.14/3.35  tff(c_11166, plain, (![A_851, B_852]: (k1_relset_1(A_851, B_852, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_4', B_852) | ~r1_tarski(k1_relat_1('#skF_5'), A_851) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8308, c_11164])).
% 9.14/3.35  tff(c_11173, plain, (![A_854, B_855]: (k1_relset_1(A_854, B_855, '#skF_5')='#skF_2' | ~r1_tarski('#skF_4', B_855) | ~r1_tarski('#skF_2', A_854))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_8860, c_8860, c_11166])).
% 9.14/3.35  tff(c_11178, plain, (![A_856]: (k1_relset_1(A_856, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_856))), inference(resolution, [status(thm)], [c_10, c_11173])).
% 9.14/3.35  tff(c_11183, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_10, c_11178])).
% 9.14/3.35  tff(c_10530, plain, (![C_806, A_807, B_808]: (r1_tarski(C_806, k2_zfmisc_1(A_807, B_808)) | ~r1_tarski(k2_relat_1(C_806), B_808) | ~r1_tarski(k1_relat_1(C_806), A_807) | ~v1_relat_1(C_806))), inference(resolution, [status(thm)], [c_8586, c_20])).
% 9.14/3.35  tff(c_10532, plain, (![A_807, B_808]: (r1_tarski('#skF_5', k2_zfmisc_1(A_807, B_808)) | ~r1_tarski('#skF_4', B_808) | ~r1_tarski(k1_relat_1('#skF_5'), A_807) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8308, c_10530])).
% 9.14/3.35  tff(c_10537, plain, (![A_807, B_808]: (r1_tarski('#skF_5', k2_zfmisc_1(A_807, B_808)) | ~r1_tarski('#skF_4', B_808) | ~r1_tarski('#skF_2', A_807))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_8860, c_10532])).
% 9.14/3.35  tff(c_8736, plain, (![B_680, C_681, A_682]: (k1_xboole_0=B_680 | v1_funct_2(C_681, A_682, B_680) | k1_relset_1(A_682, B_680, C_681)!=A_682 | ~m1_subset_1(C_681, k1_zfmisc_1(k2_zfmisc_1(A_682, B_680))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.14/3.35  tff(c_11406, plain, (![B_865, A_866, A_867]: (k1_xboole_0=B_865 | v1_funct_2(A_866, A_867, B_865) | k1_relset_1(A_867, B_865, A_866)!=A_867 | ~r1_tarski(A_866, k2_zfmisc_1(A_867, B_865)))), inference(resolution, [status(thm)], [c_22, c_8736])).
% 9.14/3.35  tff(c_11540, plain, (![B_872, A_873]: (k1_xboole_0=B_872 | v1_funct_2('#skF_5', A_873, B_872) | k1_relset_1(A_873, B_872, '#skF_5')!=A_873 | ~r1_tarski('#skF_4', B_872) | ~r1_tarski('#skF_2', A_873))), inference(resolution, [status(thm)], [c_10537, c_11406])).
% 9.14/3.35  tff(c_11549, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_11540, c_142])).
% 9.14/3.35  tff(c_11554, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_11183, c_11549])).
% 9.14/3.35  tff(c_10200, plain, (![C_789, A_790]: (m1_subset_1(C_789, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_789), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_789), A_790) | ~v1_relat_1(C_789))), inference(superposition, [status(thm), theory('equality')], [c_16, c_8586])).
% 9.14/3.35  tff(c_10202, plain, (![A_790]: (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_5'), A_790) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8308, c_10200])).
% 9.14/3.35  tff(c_10204, plain, (![A_790]: (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski('#skF_2', A_790))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_8860, c_10202])).
% 9.14/3.35  tff(c_10205, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10204])).
% 9.14/3.35  tff(c_11583, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11554, c_10205])).
% 9.14/3.35  tff(c_11644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_11583])).
% 9.14/3.35  tff(c_11646, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_10204])).
% 9.14/3.35  tff(c_8170, plain, (![B_608, A_609, A_610]: (~v1_xboole_0(B_608) | ~r2_hidden(A_609, A_610) | ~r1_tarski(A_610, B_608))), inference(resolution, [status(thm)], [c_22, c_263])).
% 9.14/3.35  tff(c_8173, plain, (![B_608, A_1]: (~v1_xboole_0(B_608) | ~r1_tarski(A_1, B_608) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_8170])).
% 9.14/3.35  tff(c_11663, plain, (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_11646, c_8173])).
% 9.14/3.35  tff(c_11683, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_11663])).
% 9.14/3.35  tff(c_8224, plain, (![C_617, A_618, B_619]: (v4_relat_1(C_617, A_618) | ~m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(A_618, B_619))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.14/3.35  tff(c_8329, plain, (![C_635, A_636]: (v4_relat_1(C_635, A_636) | ~m1_subset_1(C_635, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_8224])).
% 9.14/3.35  tff(c_8337, plain, (![A_8, A_636]: (v4_relat_1(A_8, A_636) | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_8329])).
% 9.14/3.35  tff(c_8869, plain, (![A_16]: (r1_tarski('#skF_2', A_16) | ~v4_relat_1('#skF_5', A_16) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8860, c_30])).
% 9.14/3.35  tff(c_8886, plain, (![A_694]: (r1_tarski('#skF_2', A_694) | ~v4_relat_1('#skF_5', A_694))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_8869])).
% 9.14/3.35  tff(c_8898, plain, (![A_636]: (r1_tarski('#skF_2', A_636) | ~r1_tarski('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_8337, c_8886])).
% 9.14/3.35  tff(c_8916, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8898])).
% 9.14/3.35  tff(c_11713, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11683, c_8916])).
% 9.14/3.35  tff(c_12128, plain, (![A_892]: (k2_zfmisc_1(A_892, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11683, c_11683, c_16])).
% 9.14/3.35  tff(c_11741, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_11683, c_134])).
% 9.14/3.35  tff(c_11923, plain, (![C_879, A_880, B_881]: (r1_tarski(C_879, k2_zfmisc_1(A_880, B_881)) | ~r1_tarski(k2_relat_1(C_879), B_881) | ~r1_tarski(k1_relat_1(C_879), A_880) | ~v1_relat_1(C_879))), inference(resolution, [status(thm)], [c_8586, c_20])).
% 9.14/3.35  tff(c_11925, plain, (![A_880, B_881]: (r1_tarski('#skF_5', k2_zfmisc_1(A_880, B_881)) | ~r1_tarski('#skF_4', B_881) | ~r1_tarski(k1_relat_1('#skF_5'), A_880) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8308, c_11923])).
% 9.14/3.35  tff(c_11930, plain, (![A_880, B_881]: (r1_tarski('#skF_5', k2_zfmisc_1(A_880, B_881)) | ~r1_tarski('#skF_2', A_880))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_8860, c_11741, c_11925])).
% 9.14/3.35  tff(c_12136, plain, (![A_892]: (r1_tarski('#skF_5', '#skF_4') | ~r1_tarski('#skF_2', A_892))), inference(superposition, [status(thm), theory('equality')], [c_12128, c_11930])).
% 9.14/3.35  tff(c_12279, plain, (![A_893]: (~r1_tarski('#skF_2', A_893))), inference(negUnitSimplification, [status(thm)], [c_11713, c_12136])).
% 9.14/3.35  tff(c_12284, plain, $false, inference(resolution, [status(thm)], [c_10, c_12279])).
% 9.14/3.35  tff(c_12290, plain, (![A_894]: (r1_tarski('#skF_2', A_894))), inference(splitRight, [status(thm)], [c_8898])).
% 9.14/3.35  tff(c_12329, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_12290, c_12])).
% 9.14/3.35  tff(c_12377, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12329, c_2])).
% 9.14/3.35  tff(c_12375, plain, (![B_7]: (k2_zfmisc_1('#skF_2', B_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12329, c_12329, c_18])).
% 9.14/3.35  tff(c_277, plain, (![A_62]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_62, '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_263])).
% 9.14/3.35  tff(c_289, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_277])).
% 9.14/3.35  tff(c_12550, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12375, c_289])).
% 9.14/3.35  tff(c_12553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12377, c_12550])).
% 9.14/3.35  tff(c_12556, plain, (![A_906]: (~r2_hidden(A_906, '#skF_5'))), inference(splitRight, [status(thm)], [c_277])).
% 9.14/3.35  tff(c_12561, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4, c_12556])).
% 9.14/3.35  tff(c_12573, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12561, c_79])).
% 9.14/3.35  tff(c_12555, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_277])).
% 9.14/3.35  tff(c_12568, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12561, c_4])).
% 9.14/3.35  tff(c_13004, plain, (![B_956, A_957, A_958]: (~v1_xboole_0(B_956) | ~r2_hidden(A_957, A_958) | ~r1_tarski(A_958, B_956))), inference(resolution, [status(thm)], [c_22, c_263])).
% 9.14/3.35  tff(c_13008, plain, (![B_959, A_960]: (~v1_xboole_0(B_959) | ~r1_tarski(A_960, B_959) | A_960='#skF_5')), inference(resolution, [status(thm)], [c_12568, c_13004])).
% 9.14/3.35  tff(c_13034, plain, (![B_961]: (~v1_xboole_0(B_961) | B_961='#skF_5')), inference(resolution, [status(thm)], [c_10, c_13008])).
% 9.14/3.35  tff(c_13041, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_12555, c_13034])).
% 9.14/3.35  tff(c_153, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.14/3.35  tff(c_165, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_153])).
% 9.14/3.35  tff(c_221, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_165, c_207])).
% 9.14/3.35  tff(c_12754, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_221])).
% 9.14/3.35  tff(c_13052, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13041, c_12754])).
% 9.14/3.35  tff(c_13057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_13052])).
% 9.14/3.35  tff(c_13058, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_221])).
% 9.14/3.35  tff(c_14, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.14/3.35  tff(c_13638, plain, (![B_1033, A_1034]: (B_1033='#skF_5' | A_1034='#skF_5' | k2_zfmisc_1(A_1034, B_1033)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12561, c_12561, c_12561, c_14])).
% 9.14/3.35  tff(c_13641, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_13058, c_13638])).
% 9.14/3.35  tff(c_13650, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_12573, c_13641])).
% 9.14/3.35  tff(c_12567, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12561, c_12561, c_127])).
% 9.14/3.35  tff(c_13685, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13650, c_13650, c_12567])).
% 9.14/3.35  tff(c_12566, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_12561, c_134])).
% 9.14/3.35  tff(c_13684, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_13650, c_12566])).
% 9.14/3.35  tff(c_13230, plain, (![A_983, B_984, C_985]: (k1_relset_1(A_983, B_984, C_985)=k1_relat_1(C_985) | ~m1_subset_1(C_985, k1_zfmisc_1(k2_zfmisc_1(A_983, B_984))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.14/3.35  tff(c_14154, plain, (![A_1058, B_1059, A_1060]: (k1_relset_1(A_1058, B_1059, A_1060)=k1_relat_1(A_1060) | ~r1_tarski(A_1060, k2_zfmisc_1(A_1058, B_1059)))), inference(resolution, [status(thm)], [c_22, c_13230])).
% 9.14/3.35  tff(c_14164, plain, (![A_1058, B_1059]: (k1_relset_1(A_1058, B_1059, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_13684, c_14154])).
% 9.14/3.35  tff(c_14181, plain, (![A_1058, B_1059]: (k1_relset_1(A_1058, B_1059, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13685, c_14164])).
% 9.14/3.35  tff(c_143, plain, (![A_48]: (m1_subset_1(k6_relat_1(A_48), k1_zfmisc_1(k2_zfmisc_1(A_48, A_48))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.14/3.35  tff(c_147, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_143])).
% 9.14/3.35  tff(c_163, plain, (r1_tarski(k6_relat_1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_147, c_153])).
% 9.14/3.35  tff(c_174, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_163, c_12])).
% 9.14/3.35  tff(c_12565, plain, (k6_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12561, c_12561, c_174])).
% 9.14/3.35  tff(c_12645, plain, (![B_911]: (k2_zfmisc_1('#skF_5', B_911)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12561, c_12561, c_18])).
% 9.14/3.35  tff(c_46, plain, (![A_34]: (m1_subset_1(k6_relat_1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.14/3.35  tff(c_12658, plain, (m1_subset_1(k6_relat_1('#skF_5'), k1_zfmisc_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12645, c_46])).
% 9.14/3.35  tff(c_12672, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_12565, c_12658])).
% 9.14/3.35  tff(c_52, plain, (![C_37, B_36]: (v1_funct_2(C_37, k1_xboole_0, B_36) | k1_relset_1(k1_xboole_0, B_36, C_37)!=k1_xboole_0 | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.14/3.35  tff(c_74, plain, (![C_37, B_36]: (v1_funct_2(C_37, k1_xboole_0, B_36) | k1_relset_1(k1_xboole_0, B_36, C_37)!=k1_xboole_0 | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_52])).
% 9.14/3.35  tff(c_13518, plain, (![C_1019, B_1020]: (v1_funct_2(C_1019, '#skF_5', B_1020) | k1_relset_1('#skF_5', B_1020, C_1019)!='#skF_5' | ~m1_subset_1(C_1019, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_12561, c_12561, c_12561, c_12561, c_74])).
% 9.14/3.35  tff(c_13524, plain, (![B_1020]: (v1_funct_2('#skF_5', '#skF_5', B_1020) | k1_relset_1('#skF_5', B_1020, '#skF_5')!='#skF_5')), inference(resolution, [status(thm)], [c_12672, c_13518])).
% 9.14/3.35  tff(c_14567, plain, (![B_1020]: (v1_funct_2('#skF_2', '#skF_2', B_1020))), inference(demodulation, [status(thm), theory('equality')], [c_14181, c_13650, c_13650, c_13650, c_13650, c_13650, c_13524])).
% 9.14/3.35  tff(c_13691, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13650, c_142])).
% 9.14/3.35  tff(c_14571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14567, c_13691])).
% 9.14/3.35  tff(c_14572, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_72])).
% 9.14/3.35  tff(c_15279, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_15256, c_14572])).
% 9.14/3.35  tff(c_15297, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14686, c_15107, c_15279])).
% 9.14/3.35  tff(c_15300, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_15297])).
% 9.14/3.35  tff(c_15304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14686, c_14820, c_15300])).
% 9.14/3.35  tff(c_15306, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_62])).
% 9.14/3.35  tff(c_15323, plain, (![B_7]: (k2_zfmisc_1('#skF_3', B_7)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15306, c_15306, c_18])).
% 9.14/3.35  tff(c_15363, plain, (![A_1188, B_1189]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_1188, B_1189)), A_1188))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.14/3.35  tff(c_15354, plain, (![A_5]: (A_5='#skF_3' | ~r1_tarski(A_5, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15306, c_15306, c_12])).
% 9.14/3.35  tff(c_15367, plain, (![B_1189]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_1189))='#skF_3')), inference(resolution, [status(thm)], [c_15363, c_15354])).
% 9.14/3.35  tff(c_15375, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15323, c_15367])).
% 9.14/3.35  tff(c_15305, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 9.14/3.35  tff(c_15312, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15306, c_15305])).
% 9.14/3.35  tff(c_15362, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15323, c_15312, c_66])).
% 9.14/3.35  tff(c_15403, plain, (![A_1193, B_1194]: (r1_tarski(A_1193, B_1194) | ~m1_subset_1(A_1193, k1_zfmisc_1(B_1194)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.14/3.35  tff(c_15415, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_15362, c_15403])).
% 9.14/3.35  tff(c_15424, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_15415, c_15354])).
% 9.14/3.35  tff(c_15427, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15424, c_15362])).
% 9.14/3.35  tff(c_15784, plain, (![A_1248, B_1249, C_1250]: (k1_relset_1(A_1248, B_1249, C_1250)=k1_relat_1(C_1250) | ~m1_subset_1(C_1250, k1_zfmisc_1(k2_zfmisc_1(A_1248, B_1249))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.14/3.35  tff(c_16191, plain, (![B_1294, C_1295]: (k1_relset_1('#skF_3', B_1294, C_1295)=k1_relat_1(C_1295) | ~m1_subset_1(C_1295, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_15323, c_15784])).
% 9.14/3.35  tff(c_16193, plain, (![B_1294]: (k1_relset_1('#skF_3', B_1294, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15427, c_16191])).
% 9.14/3.35  tff(c_16198, plain, (![B_1294]: (k1_relset_1('#skF_3', B_1294, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15375, c_16193])).
% 9.14/3.35  tff(c_16098, plain, (![C_1281, B_1282]: (v1_funct_2(C_1281, '#skF_3', B_1282) | k1_relset_1('#skF_3', B_1282, C_1281)!='#skF_3' | ~m1_subset_1(C_1281, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_15306, c_15306, c_15306, c_15306, c_74])).
% 9.14/3.35  tff(c_16106, plain, (![B_1283]: (v1_funct_2('#skF_3', '#skF_3', B_1283) | k1_relset_1('#skF_3', B_1283, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_15427, c_16098])).
% 9.14/3.35  tff(c_15390, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15312, c_15362, c_15323, c_15312, c_72])).
% 9.14/3.35  tff(c_15426, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15424, c_15390])).
% 9.14/3.35  tff(c_16117, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_16106, c_15426])).
% 9.14/3.35  tff(c_16223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16198, c_16117])).
% 9.14/3.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.14/3.35  
% 9.14/3.35  Inference rules
% 9.14/3.35  ----------------------
% 9.14/3.35  #Ref     : 0
% 9.14/3.35  #Sup     : 3270
% 9.14/3.35  #Fact    : 0
% 9.14/3.35  #Define  : 0
% 9.14/3.35  #Split   : 50
% 9.14/3.35  #Chain   : 0
% 9.14/3.35  #Close   : 0
% 9.14/3.35  
% 9.14/3.35  Ordering : KBO
% 9.14/3.35  
% 9.14/3.35  Simplification rules
% 9.14/3.35  ----------------------
% 9.14/3.35  #Subsume      : 666
% 9.14/3.35  #Demod        : 4352
% 9.14/3.35  #Tautology    : 1637
% 9.14/3.35  #SimpNegUnit  : 100
% 9.14/3.35  #BackRed      : 533
% 9.14/3.35  
% 9.14/3.35  #Partial instantiations: 0
% 9.14/3.35  #Strategies tried      : 1
% 9.14/3.35  
% 9.14/3.35  Timing (in seconds)
% 9.14/3.35  ----------------------
% 9.14/3.35  Preprocessing        : 0.40
% 9.14/3.35  Parsing              : 0.21
% 9.14/3.35  CNF conversion       : 0.03
% 9.14/3.35  Main loop            : 2.09
% 9.14/3.35  Inferencing          : 0.66
% 9.14/3.35  Reduction            : 0.80
% 9.14/3.35  Demodulation         : 0.58
% 9.14/3.35  BG Simplification    : 0.07
% 9.14/3.35  Subsumption          : 0.40
% 9.14/3.35  Abstraction          : 0.08
% 9.14/3.35  MUC search           : 0.00
% 9.14/3.35  Cooper               : 0.00
% 9.14/3.35  Total                : 2.57
% 9.14/3.35  Index Insertion      : 0.00
% 9.14/3.35  Index Deletion       : 0.00
% 9.14/3.35  Index Matching       : 0.00
% 9.14/3.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
