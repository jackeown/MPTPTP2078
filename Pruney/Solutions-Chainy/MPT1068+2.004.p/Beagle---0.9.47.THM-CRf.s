%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:41 EST 2020

% Result     : Theorem 9.86s
% Output     : CNFRefutation 9.86s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 370 expanded)
%              Number of leaves         :   52 ( 146 expanded)
%              Depth                    :   22
%              Number of atoms          :  277 ( 976 expanded)
%              Number of equality atoms :   69 ( 194 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_230,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_195,axiom,(
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

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_140,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_205,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_126,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_160,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_177,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_84,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_155,plain,(
    ! [B_97,A_98] :
      ( v1_xboole_0(B_97)
      | ~ m1_subset_1(B_97,A_98)
      | ~ v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_180,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_155])).

tff(c_181,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_86,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_194,plain,(
    ! [B_103,A_104] :
      ( v1_relat_1(B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_104))
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_204,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_86,c_194])).

tff(c_215,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_204])).

tff(c_88,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_90,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_207,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_194])).

tff(c_218,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_207])).

tff(c_94,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_92,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_10056,plain,(
    ! [A_748,B_749,C_750] :
      ( k1_relset_1(A_748,B_749,C_750) = k1_relat_1(C_750)
      | ~ m1_subset_1(C_750,k1_zfmisc_1(k2_zfmisc_1(A_748,B_749))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_10083,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_10056])).

tff(c_10406,plain,(
    ! [B_784,A_785,C_786] :
      ( k1_xboole_0 = B_784
      | k1_relset_1(A_785,B_784,C_786) = A_785
      | ~ v1_funct_2(C_786,A_785,B_784)
      | ~ m1_subset_1(C_786,k1_zfmisc_1(k2_zfmisc_1(A_785,B_784))) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_10428,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_10406])).

tff(c_10441,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_10083,c_10428])).

tff(c_10444,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10441])).

tff(c_10690,plain,(
    ! [B_807,C_808,A_809] :
      ( k1_funct_1(k5_relat_1(B_807,C_808),A_809) = k1_funct_1(C_808,k1_funct_1(B_807,A_809))
      | ~ r2_hidden(A_809,k1_relat_1(B_807))
      | ~ v1_funct_1(C_808)
      | ~ v1_relat_1(C_808)
      | ~ v1_funct_1(B_807)
      | ~ v1_relat_1(B_807) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_10692,plain,(
    ! [C_808,A_809] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_808),A_809) = k1_funct_1(C_808,k1_funct_1('#skF_5',A_809))
      | ~ r2_hidden(A_809,'#skF_3')
      | ~ v1_funct_1(C_808)
      | ~ v1_relat_1(C_808)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10444,c_10690])).

tff(c_10702,plain,(
    ! [C_808,A_809] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_808),A_809) = k1_funct_1(C_808,k1_funct_1('#skF_5',A_809))
      | ~ r2_hidden(A_809,'#skF_3')
      | ~ v1_funct_1(C_808)
      | ~ v1_relat_1(C_808) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_94,c_10692])).

tff(c_10082,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_10056])).

tff(c_9964,plain,(
    ! [A_743,B_744,C_745] :
      ( k2_relset_1(A_743,B_744,C_745) = k2_relat_1(C_745)
      | ~ m1_subset_1(C_745,k1_zfmisc_1(k2_zfmisc_1(A_743,B_744))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_9991,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_9964])).

tff(c_82,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_9999,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9991,c_82])).

tff(c_10093,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10082,c_9999])).

tff(c_10757,plain,(
    ! [E_818,A_817,B_816,F_814,D_815,C_813] :
      ( k1_partfun1(A_817,B_816,C_813,D_815,E_818,F_814) = k5_relat_1(E_818,F_814)
      | ~ m1_subset_1(F_814,k1_zfmisc_1(k2_zfmisc_1(C_813,D_815)))
      | ~ v1_funct_1(F_814)
      | ~ m1_subset_1(E_818,k1_zfmisc_1(k2_zfmisc_1(A_817,B_816)))
      | ~ v1_funct_1(E_818) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_10771,plain,(
    ! [A_817,B_816,E_818] :
      ( k1_partfun1(A_817,B_816,'#skF_4','#skF_2',E_818,'#skF_6') = k5_relat_1(E_818,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_818,k1_zfmisc_1(k2_zfmisc_1(A_817,B_816)))
      | ~ v1_funct_1(E_818) ) ),
    inference(resolution,[status(thm)],[c_86,c_10757])).

tff(c_11351,plain,(
    ! [A_855,B_856,E_857] :
      ( k1_partfun1(A_855,B_856,'#skF_4','#skF_2',E_857,'#skF_6') = k5_relat_1(E_857,'#skF_6')
      | ~ m1_subset_1(E_857,k1_zfmisc_1(k2_zfmisc_1(A_855,B_856)))
      | ~ v1_funct_1(E_857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_10771])).

tff(c_11373,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_11351])).

tff(c_11387,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_11373])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_219,plain,(
    ! [A_10] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_194])).

tff(c_221,plain,(
    ! [A_10] : ~ v1_relat_1(A_10) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_218])).

tff(c_228,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_7911,plain,(
    ! [C_586,A_587,B_588] :
      ( v4_relat_1(C_586,A_587)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_zfmisc_1(A_587,B_588))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_7952,plain,(
    ! [A_589] : v4_relat_1(k1_xboole_0,A_589) ),
    inference(resolution,[status(thm)],[c_18,c_7911])).

tff(c_38,plain,(
    ! [B_29,A_28] :
      ( k7_relat_1(B_29,A_28) = B_29
      | ~ v4_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7955,plain,(
    ! [A_589] :
      ( k7_relat_1(k1_xboole_0,A_589) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7952,c_38])).

tff(c_7968,plain,(
    ! [A_590] : k7_relat_1(k1_xboole_0,A_590) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_7955])).

tff(c_40,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_31,A_30)),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7973,plain,(
    ! [A_590] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_590)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7968,c_40])).

tff(c_7993,plain,(
    ! [A_591] : r1_tarski(k1_relat_1(k1_xboole_0),A_591) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_7973])).

tff(c_105,plain,(
    ! [A_87] :
      ( v1_xboole_0(A_87)
      | r2_hidden('#skF_1'(A_87),A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [B_38,A_37] :
      ( ~ r1_tarski(B_38,A_37)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_112,plain,(
    ! [A_87] :
      ( ~ r1_tarski(A_87,'#skF_1'(A_87))
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_105,c_46])).

tff(c_8007,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_7993,c_112])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8017,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8007,c_6])).

tff(c_10078,plain,(
    ! [A_748,B_749] : k1_relset_1(A_748,B_749,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_10056])).

tff(c_10085,plain,(
    ! [A_748,B_749] : k1_relset_1(A_748,B_749,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8017,c_10078])).

tff(c_10472,plain,(
    ! [B_787,C_788,A_789] :
      ( k1_xboole_0 = B_787
      | v1_funct_2(C_788,A_789,B_787)
      | k1_relset_1(A_789,B_787,C_788) != A_789
      | ~ m1_subset_1(C_788,k1_zfmisc_1(k2_zfmisc_1(A_789,B_787))) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_10498,plain,(
    ! [B_787,A_789] :
      ( k1_xboole_0 = B_787
      | v1_funct_2(k1_xboole_0,A_789,B_787)
      | k1_relset_1(A_789,B_787,k1_xboole_0) != A_789 ) ),
    inference(resolution,[status(thm)],[c_18,c_10472])).

tff(c_10508,plain,(
    ! [B_787,A_789] :
      ( k1_xboole_0 = B_787
      | v1_funct_2(k1_xboole_0,A_789,B_787)
      | k1_xboole_0 != A_789 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10085,c_10498])).

tff(c_116,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(A_90,B_91)
      | ~ m1_subset_1(A_90,k1_zfmisc_1(B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_129,plain,(
    ! [A_92] : r1_tarski(k1_xboole_0,A_92) ),
    inference(resolution,[status(thm)],[c_18,c_116])).

tff(c_134,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_129,c_112])).

tff(c_42,plain,(
    ! [A_32] :
      ( v1_funct_1(A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_143,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_134,c_42])).

tff(c_10559,plain,(
    ! [C_800,A_801,B_802] :
      ( ~ v1_xboole_0(C_800)
      | ~ v1_funct_2(C_800,A_801,B_802)
      | ~ v1_funct_1(C_800)
      | ~ m1_subset_1(C_800,k1_zfmisc_1(k2_zfmisc_1(A_801,B_802)))
      | v1_xboole_0(B_802)
      | v1_xboole_0(A_801) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_10585,plain,(
    ! [A_801,B_802] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,A_801,B_802)
      | ~ v1_funct_1(k1_xboole_0)
      | v1_xboole_0(B_802)
      | v1_xboole_0(A_801) ) ),
    inference(resolution,[status(thm)],[c_18,c_10559])).

tff(c_10601,plain,(
    ! [A_803,B_804] :
      ( ~ v1_funct_2(k1_xboole_0,A_803,B_804)
      | v1_xboole_0(B_804)
      | v1_xboole_0(A_803) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_134,c_10585])).

tff(c_10611,plain,(
    ! [B_787,A_789] :
      ( v1_xboole_0(B_787)
      | v1_xboole_0(A_789)
      | k1_xboole_0 = B_787
      | k1_xboole_0 != A_789 ) ),
    inference(resolution,[status(thm)],[c_10508,c_10601])).

tff(c_10619,plain,(
    ! [A_805] :
      ( v1_xboole_0(A_805)
      | k1_xboole_0 != A_805 ) ),
    inference(splitLeft,[status(thm)],[c_10611])).

tff(c_10686,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_10619,c_96])).

tff(c_10971,plain,(
    ! [A_831,E_833,B_832,C_835,D_834] :
      ( k1_partfun1(A_831,B_832,B_832,C_835,D_834,E_833) = k8_funct_2(A_831,B_832,C_835,D_834,E_833)
      | k1_xboole_0 = B_832
      | ~ r1_tarski(k2_relset_1(A_831,B_832,D_834),k1_relset_1(B_832,C_835,E_833))
      | ~ m1_subset_1(E_833,k1_zfmisc_1(k2_zfmisc_1(B_832,C_835)))
      | ~ v1_funct_1(E_833)
      | ~ m1_subset_1(D_834,k1_zfmisc_1(k2_zfmisc_1(A_831,B_832)))
      | ~ v1_funct_2(D_834,A_831,B_832)
      | ~ v1_funct_1(D_834) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_10989,plain,(
    ! [C_835,E_833] :
      ( k1_partfun1('#skF_3','#skF_4','#skF_4',C_835,'#skF_5',E_833) = k8_funct_2('#skF_3','#skF_4',C_835,'#skF_5',E_833)
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',C_835,E_833))
      | ~ m1_subset_1(E_833,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_835)))
      | ~ v1_funct_1(E_833)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9991,c_10971])).

tff(c_11005,plain,(
    ! [C_835,E_833] :
      ( k1_partfun1('#skF_3','#skF_4','#skF_4',C_835,'#skF_5',E_833) = k8_funct_2('#skF_3','#skF_4',C_835,'#skF_5',E_833)
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',C_835,E_833))
      | ~ m1_subset_1(E_833,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_835)))
      | ~ v1_funct_1(E_833) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_10989])).

tff(c_11561,plain,(
    ! [C_869,E_870] :
      ( k1_partfun1('#skF_3','#skF_4','#skF_4',C_869,'#skF_5',E_870) = k8_funct_2('#skF_3','#skF_4',C_869,'#skF_5',E_870)
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',C_869,E_870))
      | ~ m1_subset_1(E_870,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_869)))
      | ~ v1_funct_1(E_870) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10686,c_11005])).

tff(c_11567,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10082,c_11561])).

tff(c_11574,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_10093,c_11387,c_11567])).

tff(c_78,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_11577,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11574,c_78])).

tff(c_11584,plain,
    ( ~ r2_hidden('#skF_7','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10702,c_11577])).

tff(c_11587,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_88,c_11584])).

tff(c_11590,plain,
    ( ~ m1_subset_1('#skF_7','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_11587])).

tff(c_11593,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_11590])).

tff(c_11595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_11593])).

tff(c_11597,plain,(
    ! [B_871] :
      ( v1_xboole_0(B_871)
      | k1_xboole_0 = B_871 ) ),
    inference(splitRight,[status(thm)],[c_10611])).

tff(c_11638,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11597,c_181])).

tff(c_11664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_11638])).

tff(c_11665,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10441])).

tff(c_11690,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11665,c_134])).

tff(c_11698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_11690])).

tff(c_11700,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_11737,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11700,c_6])).

tff(c_11744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_11737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.86/3.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.86/3.32  
% 9.86/3.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.86/3.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 9.86/3.32  
% 9.86/3.32  %Foreground sorts:
% 9.86/3.32  
% 9.86/3.32  
% 9.86/3.32  %Background operators:
% 9.86/3.32  
% 9.86/3.32  
% 9.86/3.32  %Foreground operators:
% 9.86/3.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.86/3.32  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 9.86/3.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.86/3.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.86/3.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.86/3.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.86/3.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.86/3.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.86/3.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.86/3.32  tff('#skF_7', type, '#skF_7': $i).
% 9.86/3.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.86/3.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.86/3.32  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.86/3.32  tff('#skF_5', type, '#skF_5': $i).
% 9.86/3.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.86/3.32  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 9.86/3.32  tff('#skF_6', type, '#skF_6': $i).
% 9.86/3.32  tff('#skF_2', type, '#skF_2': $i).
% 9.86/3.32  tff('#skF_3', type, '#skF_3': $i).
% 9.86/3.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.86/3.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.86/3.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.86/3.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.86/3.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.86/3.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.86/3.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.86/3.32  tff('#skF_4', type, '#skF_4': $i).
% 9.86/3.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.86/3.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.86/3.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.86/3.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.86/3.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.86/3.32  
% 9.86/3.34  tff(f_230, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 9.86/3.34  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 9.86/3.34  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.86/3.34  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.86/3.34  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.86/3.34  tff(f_195, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.86/3.34  tff(f_121, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 9.86/3.34  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.86/3.34  tff(f_205, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.86/3.34  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.86/3.34  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.86/3.34  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 9.86/3.34  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 9.86/3.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.86/3.34  tff(f_126, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.86/3.34  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.86/3.34  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.86/3.34  tff(f_108, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 9.86/3.34  tff(f_160, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 9.86/3.34  tff(f_177, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 9.86/3.34  tff(c_80, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_230])).
% 9.86/3.34  tff(c_96, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 9.86/3.34  tff(c_84, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 9.86/3.34  tff(c_155, plain, (![B_97, A_98]: (v1_xboole_0(B_97) | ~m1_subset_1(B_97, A_98) | ~v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.86/3.34  tff(c_180, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_155])).
% 9.86/3.34  tff(c_181, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_180])).
% 9.86/3.34  tff(c_12, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.86/3.34  tff(c_32, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.86/3.34  tff(c_86, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 9.86/3.34  tff(c_194, plain, (![B_103, A_104]: (v1_relat_1(B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(A_104)) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.86/3.34  tff(c_204, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_194])).
% 9.86/3.34  tff(c_215, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_204])).
% 9.86/3.34  tff(c_88, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_230])).
% 9.86/3.34  tff(c_90, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 9.86/3.34  tff(c_207, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_194])).
% 9.86/3.34  tff(c_218, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_207])).
% 9.86/3.34  tff(c_94, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 9.86/3.34  tff(c_92, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 9.86/3.34  tff(c_10056, plain, (![A_748, B_749, C_750]: (k1_relset_1(A_748, B_749, C_750)=k1_relat_1(C_750) | ~m1_subset_1(C_750, k1_zfmisc_1(k2_zfmisc_1(A_748, B_749))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.86/3.34  tff(c_10083, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_10056])).
% 9.86/3.34  tff(c_10406, plain, (![B_784, A_785, C_786]: (k1_xboole_0=B_784 | k1_relset_1(A_785, B_784, C_786)=A_785 | ~v1_funct_2(C_786, A_785, B_784) | ~m1_subset_1(C_786, k1_zfmisc_1(k2_zfmisc_1(A_785, B_784))))), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.86/3.34  tff(c_10428, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_90, c_10406])).
% 9.86/3.34  tff(c_10441, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_10083, c_10428])).
% 9.86/3.34  tff(c_10444, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_10441])).
% 9.86/3.34  tff(c_10690, plain, (![B_807, C_808, A_809]: (k1_funct_1(k5_relat_1(B_807, C_808), A_809)=k1_funct_1(C_808, k1_funct_1(B_807, A_809)) | ~r2_hidden(A_809, k1_relat_1(B_807)) | ~v1_funct_1(C_808) | ~v1_relat_1(C_808) | ~v1_funct_1(B_807) | ~v1_relat_1(B_807))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.86/3.34  tff(c_10692, plain, (![C_808, A_809]: (k1_funct_1(k5_relat_1('#skF_5', C_808), A_809)=k1_funct_1(C_808, k1_funct_1('#skF_5', A_809)) | ~r2_hidden(A_809, '#skF_3') | ~v1_funct_1(C_808) | ~v1_relat_1(C_808) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10444, c_10690])).
% 9.86/3.34  tff(c_10702, plain, (![C_808, A_809]: (k1_funct_1(k5_relat_1('#skF_5', C_808), A_809)=k1_funct_1(C_808, k1_funct_1('#skF_5', A_809)) | ~r2_hidden(A_809, '#skF_3') | ~v1_funct_1(C_808) | ~v1_relat_1(C_808))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_94, c_10692])).
% 9.86/3.34  tff(c_10082, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_10056])).
% 9.86/3.34  tff(c_9964, plain, (![A_743, B_744, C_745]: (k2_relset_1(A_743, B_744, C_745)=k2_relat_1(C_745) | ~m1_subset_1(C_745, k1_zfmisc_1(k2_zfmisc_1(A_743, B_744))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.86/3.34  tff(c_9991, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_9964])).
% 9.86/3.34  tff(c_82, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 9.86/3.34  tff(c_9999, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9991, c_82])).
% 9.86/3.34  tff(c_10093, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10082, c_9999])).
% 9.86/3.34  tff(c_10757, plain, (![E_818, A_817, B_816, F_814, D_815, C_813]: (k1_partfun1(A_817, B_816, C_813, D_815, E_818, F_814)=k5_relat_1(E_818, F_814) | ~m1_subset_1(F_814, k1_zfmisc_1(k2_zfmisc_1(C_813, D_815))) | ~v1_funct_1(F_814) | ~m1_subset_1(E_818, k1_zfmisc_1(k2_zfmisc_1(A_817, B_816))) | ~v1_funct_1(E_818))), inference(cnfTransformation, [status(thm)], [f_205])).
% 9.86/3.34  tff(c_10771, plain, (![A_817, B_816, E_818]: (k1_partfun1(A_817, B_816, '#skF_4', '#skF_2', E_818, '#skF_6')=k5_relat_1(E_818, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_818, k1_zfmisc_1(k2_zfmisc_1(A_817, B_816))) | ~v1_funct_1(E_818))), inference(resolution, [status(thm)], [c_86, c_10757])).
% 9.86/3.34  tff(c_11351, plain, (![A_855, B_856, E_857]: (k1_partfun1(A_855, B_856, '#skF_4', '#skF_2', E_857, '#skF_6')=k5_relat_1(E_857, '#skF_6') | ~m1_subset_1(E_857, k1_zfmisc_1(k2_zfmisc_1(A_855, B_856))) | ~v1_funct_1(E_857))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_10771])).
% 9.86/3.34  tff(c_11373, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_11351])).
% 9.86/3.34  tff(c_11387, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_11373])).
% 9.86/3.34  tff(c_18, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.86/3.34  tff(c_219, plain, (![A_10]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_18, c_194])).
% 9.86/3.34  tff(c_221, plain, (![A_10]: (~v1_relat_1(A_10))), inference(splitLeft, [status(thm)], [c_219])).
% 9.86/3.34  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_218])).
% 9.86/3.34  tff(c_228, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_219])).
% 9.86/3.34  tff(c_7911, plain, (![C_586, A_587, B_588]: (v4_relat_1(C_586, A_587) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_zfmisc_1(A_587, B_588))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.86/3.34  tff(c_7952, plain, (![A_589]: (v4_relat_1(k1_xboole_0, A_589))), inference(resolution, [status(thm)], [c_18, c_7911])).
% 9.86/3.34  tff(c_38, plain, (![B_29, A_28]: (k7_relat_1(B_29, A_28)=B_29 | ~v4_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.86/3.34  tff(c_7955, plain, (![A_589]: (k7_relat_1(k1_xboole_0, A_589)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_7952, c_38])).
% 9.86/3.34  tff(c_7968, plain, (![A_590]: (k7_relat_1(k1_xboole_0, A_590)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_228, c_7955])).
% 9.86/3.34  tff(c_40, plain, (![B_31, A_30]: (r1_tarski(k1_relat_1(k7_relat_1(B_31, A_30)), A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.86/3.34  tff(c_7973, plain, (![A_590]: (r1_tarski(k1_relat_1(k1_xboole_0), A_590) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7968, c_40])).
% 9.86/3.34  tff(c_7993, plain, (![A_591]: (r1_tarski(k1_relat_1(k1_xboole_0), A_591))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_7973])).
% 9.86/3.34  tff(c_105, plain, (![A_87]: (v1_xboole_0(A_87) | r2_hidden('#skF_1'(A_87), A_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.86/3.34  tff(c_46, plain, (![B_38, A_37]: (~r1_tarski(B_38, A_37) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.86/3.34  tff(c_112, plain, (![A_87]: (~r1_tarski(A_87, '#skF_1'(A_87)) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_105, c_46])).
% 9.86/3.34  tff(c_8007, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_7993, c_112])).
% 9.86/3.34  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.86/3.34  tff(c_8017, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8007, c_6])).
% 9.86/3.34  tff(c_10078, plain, (![A_748, B_749]: (k1_relset_1(A_748, B_749, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_10056])).
% 9.86/3.34  tff(c_10085, plain, (![A_748, B_749]: (k1_relset_1(A_748, B_749, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8017, c_10078])).
% 9.86/3.34  tff(c_10472, plain, (![B_787, C_788, A_789]: (k1_xboole_0=B_787 | v1_funct_2(C_788, A_789, B_787) | k1_relset_1(A_789, B_787, C_788)!=A_789 | ~m1_subset_1(C_788, k1_zfmisc_1(k2_zfmisc_1(A_789, B_787))))), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.86/3.34  tff(c_10498, plain, (![B_787, A_789]: (k1_xboole_0=B_787 | v1_funct_2(k1_xboole_0, A_789, B_787) | k1_relset_1(A_789, B_787, k1_xboole_0)!=A_789)), inference(resolution, [status(thm)], [c_18, c_10472])).
% 9.86/3.34  tff(c_10508, plain, (![B_787, A_789]: (k1_xboole_0=B_787 | v1_funct_2(k1_xboole_0, A_789, B_787) | k1_xboole_0!=A_789)), inference(demodulation, [status(thm), theory('equality')], [c_10085, c_10498])).
% 9.86/3.34  tff(c_116, plain, (![A_90, B_91]: (r1_tarski(A_90, B_91) | ~m1_subset_1(A_90, k1_zfmisc_1(B_91)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.86/3.34  tff(c_129, plain, (![A_92]: (r1_tarski(k1_xboole_0, A_92))), inference(resolution, [status(thm)], [c_18, c_116])).
% 9.86/3.34  tff(c_134, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_129, c_112])).
% 9.86/3.34  tff(c_42, plain, (![A_32]: (v1_funct_1(A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.86/3.34  tff(c_143, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_134, c_42])).
% 9.86/3.34  tff(c_10559, plain, (![C_800, A_801, B_802]: (~v1_xboole_0(C_800) | ~v1_funct_2(C_800, A_801, B_802) | ~v1_funct_1(C_800) | ~m1_subset_1(C_800, k1_zfmisc_1(k2_zfmisc_1(A_801, B_802))) | v1_xboole_0(B_802) | v1_xboole_0(A_801))), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.86/3.34  tff(c_10585, plain, (![A_801, B_802]: (~v1_xboole_0(k1_xboole_0) | ~v1_funct_2(k1_xboole_0, A_801, B_802) | ~v1_funct_1(k1_xboole_0) | v1_xboole_0(B_802) | v1_xboole_0(A_801))), inference(resolution, [status(thm)], [c_18, c_10559])).
% 9.86/3.34  tff(c_10601, plain, (![A_803, B_804]: (~v1_funct_2(k1_xboole_0, A_803, B_804) | v1_xboole_0(B_804) | v1_xboole_0(A_803))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_134, c_10585])).
% 9.86/3.34  tff(c_10611, plain, (![B_787, A_789]: (v1_xboole_0(B_787) | v1_xboole_0(A_789) | k1_xboole_0=B_787 | k1_xboole_0!=A_789)), inference(resolution, [status(thm)], [c_10508, c_10601])).
% 9.86/3.34  tff(c_10619, plain, (![A_805]: (v1_xboole_0(A_805) | k1_xboole_0!=A_805)), inference(splitLeft, [status(thm)], [c_10611])).
% 9.86/3.34  tff(c_10686, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_10619, c_96])).
% 9.86/3.34  tff(c_10971, plain, (![A_831, E_833, B_832, C_835, D_834]: (k1_partfun1(A_831, B_832, B_832, C_835, D_834, E_833)=k8_funct_2(A_831, B_832, C_835, D_834, E_833) | k1_xboole_0=B_832 | ~r1_tarski(k2_relset_1(A_831, B_832, D_834), k1_relset_1(B_832, C_835, E_833)) | ~m1_subset_1(E_833, k1_zfmisc_1(k2_zfmisc_1(B_832, C_835))) | ~v1_funct_1(E_833) | ~m1_subset_1(D_834, k1_zfmisc_1(k2_zfmisc_1(A_831, B_832))) | ~v1_funct_2(D_834, A_831, B_832) | ~v1_funct_1(D_834))), inference(cnfTransformation, [status(thm)], [f_177])).
% 9.86/3.34  tff(c_10989, plain, (![C_835, E_833]: (k1_partfun1('#skF_3', '#skF_4', '#skF_4', C_835, '#skF_5', E_833)=k8_funct_2('#skF_3', '#skF_4', C_835, '#skF_5', E_833) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', C_835, E_833)) | ~m1_subset_1(E_833, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_835))) | ~v1_funct_1(E_833) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9991, c_10971])).
% 9.86/3.34  tff(c_11005, plain, (![C_835, E_833]: (k1_partfun1('#skF_3', '#skF_4', '#skF_4', C_835, '#skF_5', E_833)=k8_funct_2('#skF_3', '#skF_4', C_835, '#skF_5', E_833) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', C_835, E_833)) | ~m1_subset_1(E_833, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_835))) | ~v1_funct_1(E_833))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_90, c_10989])).
% 9.86/3.34  tff(c_11561, plain, (![C_869, E_870]: (k1_partfun1('#skF_3', '#skF_4', '#skF_4', C_869, '#skF_5', E_870)=k8_funct_2('#skF_3', '#skF_4', C_869, '#skF_5', E_870) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', C_869, E_870)) | ~m1_subset_1(E_870, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_869))) | ~v1_funct_1(E_870))), inference(negUnitSimplification, [status(thm)], [c_10686, c_11005])).
% 9.86/3.34  tff(c_11567, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10082, c_11561])).
% 9.86/3.34  tff(c_11574, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_10093, c_11387, c_11567])).
% 9.86/3.34  tff(c_78, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 9.86/3.34  tff(c_11577, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_11574, c_78])).
% 9.86/3.34  tff(c_11584, plain, (~r2_hidden('#skF_7', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10702, c_11577])).
% 9.86/3.34  tff(c_11587, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_88, c_11584])).
% 9.86/3.34  tff(c_11590, plain, (~m1_subset_1('#skF_7', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_11587])).
% 9.86/3.34  tff(c_11593, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_11590])).
% 9.86/3.34  tff(c_11595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_11593])).
% 9.86/3.34  tff(c_11597, plain, (![B_871]: (v1_xboole_0(B_871) | k1_xboole_0=B_871)), inference(splitRight, [status(thm)], [c_10611])).
% 9.86/3.34  tff(c_11638, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_11597, c_181])).
% 9.86/3.34  tff(c_11664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_11638])).
% 9.86/3.34  tff(c_11665, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_10441])).
% 9.86/3.34  tff(c_11690, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11665, c_134])).
% 9.86/3.34  tff(c_11698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_11690])).
% 9.86/3.34  tff(c_11700, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_180])).
% 9.86/3.34  tff(c_11737, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_11700, c_6])).
% 9.86/3.34  tff(c_11744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_11737])).
% 9.86/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.86/3.34  
% 9.86/3.34  Inference rules
% 9.86/3.34  ----------------------
% 9.86/3.34  #Ref     : 0
% 9.86/3.34  #Sup     : 2459
% 9.86/3.34  #Fact    : 0
% 9.86/3.34  #Define  : 0
% 9.86/3.34  #Split   : 82
% 9.86/3.34  #Chain   : 0
% 9.86/3.34  #Close   : 0
% 9.86/3.34  
% 9.86/3.34  Ordering : KBO
% 9.86/3.34  
% 9.86/3.34  Simplification rules
% 9.86/3.34  ----------------------
% 9.86/3.34  #Subsume      : 510
% 9.86/3.34  #Demod        : 1453
% 9.86/3.34  #Tautology    : 737
% 9.86/3.34  #SimpNegUnit  : 152
% 9.86/3.34  #BackRed      : 139
% 9.86/3.34  
% 9.86/3.34  #Partial instantiations: 0
% 9.86/3.34  #Strategies tried      : 1
% 9.86/3.34  
% 9.86/3.34  Timing (in seconds)
% 9.86/3.34  ----------------------
% 9.86/3.35  Preprocessing        : 0.39
% 9.86/3.35  Parsing              : 0.20
% 9.86/3.35  CNF conversion       : 0.03
% 9.86/3.35  Main loop            : 2.18
% 9.86/3.35  Inferencing          : 0.63
% 9.86/3.35  Reduction            : 0.77
% 9.86/3.35  Demodulation         : 0.52
% 9.86/3.35  BG Simplification    : 0.07
% 9.86/3.35  Subsumption          : 0.53
% 9.86/3.35  Abstraction          : 0.10
% 9.86/3.35  MUC search           : 0.00
% 9.86/3.35  Cooper               : 0.00
% 9.86/3.35  Total                : 2.61
% 9.86/3.35  Index Insertion      : 0.00
% 9.86/3.35  Index Deletion       : 0.00
% 9.86/3.35  Index Matching       : 0.00
% 9.86/3.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
