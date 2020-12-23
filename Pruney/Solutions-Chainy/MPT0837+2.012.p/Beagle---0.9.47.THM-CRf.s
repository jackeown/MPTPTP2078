%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:06 EST 2020

% Result     : Theorem 8.31s
% Output     : CNFRefutation 8.63s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 215 expanded)
%              Number of leaves         :   40 (  91 expanded)
%              Depth                    :    8
%              Number of atoms          :  172 ( 480 expanded)
%              Number of equality atoms :   12 (  28 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_28,plain,(
    ! [A_32,B_33] : v1_relat_1(k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_65,plain,(
    ! [B_93,A_94] :
      ( v1_relat_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_46,c_65])).

tff(c_71,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_68])).

tff(c_111,plain,(
    ! [C_106,A_107,B_108] :
      ( v4_relat_1(C_106,A_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_120,plain,(
    v4_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_111])).

tff(c_5448,plain,(
    ! [A_744,B_745,C_746] :
      ( k2_relset_1(A_744,B_745,C_746) = k2_relat_1(C_746)
      | ~ m1_subset_1(C_746,k1_zfmisc_1(k2_zfmisc_1(A_744,B_745))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5457,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_5448])).

tff(c_62,plain,
    ( m1_subset_1('#skF_11','#skF_8')
    | r2_hidden('#skF_12',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_83,plain,(
    r2_hidden('#skF_12',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_5462,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5457,c_83])).

tff(c_38,plain,(
    ! [A_40] :
      ( k9_relat_1(A_40,k1_relat_1(A_40)) = k2_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5581,plain,(
    ! [A_770,B_771,C_772] :
      ( r2_hidden('#skF_6'(A_770,B_771,C_772),k1_relat_1(C_772))
      | ~ r2_hidden(A_770,k9_relat_1(C_772,B_771))
      | ~ v1_relat_1(C_772) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6402,plain,(
    ! [A_894,B_895,C_896,B_897] :
      ( r2_hidden('#skF_6'(A_894,B_895,C_896),B_897)
      | ~ r1_tarski(k1_relat_1(C_896),B_897)
      | ~ r2_hidden(A_894,k9_relat_1(C_896,B_895))
      | ~ v1_relat_1(C_896) ) ),
    inference(resolution,[status(thm)],[c_5581,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6436,plain,(
    ! [A_900,B_901,C_902,B_903] :
      ( m1_subset_1('#skF_6'(A_900,B_901,C_902),B_903)
      | ~ r1_tarski(k1_relat_1(C_902),B_903)
      | ~ r2_hidden(A_900,k9_relat_1(C_902,B_901))
      | ~ v1_relat_1(C_902) ) ),
    inference(resolution,[status(thm)],[c_6402,c_8])).

tff(c_6521,plain,(
    ! [A_910,B_911,B_912,A_913] :
      ( m1_subset_1('#skF_6'(A_910,B_911,B_912),A_913)
      | ~ r2_hidden(A_910,k9_relat_1(B_912,B_911))
      | ~ v4_relat_1(B_912,A_913)
      | ~ v1_relat_1(B_912) ) ),
    inference(resolution,[status(thm)],[c_14,c_6436])).

tff(c_8531,plain,(
    ! [A_1097,A_1098,A_1099] :
      ( m1_subset_1('#skF_6'(A_1097,k1_relat_1(A_1098),A_1098),A_1099)
      | ~ r2_hidden(A_1097,k2_relat_1(A_1098))
      | ~ v4_relat_1(A_1098,A_1099)
      | ~ v1_relat_1(A_1098)
      | ~ v1_relat_1(A_1098) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6521])).

tff(c_5694,plain,(
    ! [A_811,B_812,C_813] :
      ( r2_hidden(k4_tarski('#skF_6'(A_811,B_812,C_813),A_811),C_813)
      | ~ r2_hidden(A_811,k9_relat_1(C_813,B_812))
      | ~ v1_relat_1(C_813) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2772,plain,(
    ! [A_430,B_431,C_432] :
      ( k2_relset_1(A_430,B_431,C_432) = k2_relat_1(C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2786,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_2772])).

tff(c_2789,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2786,c_83])).

tff(c_2878,plain,(
    ! [A_446,B_447,C_448] :
      ( r2_hidden('#skF_6'(A_446,B_447,C_448),k1_relat_1(C_448))
      | ~ r2_hidden(A_446,k9_relat_1(C_448,B_447))
      | ~ v1_relat_1(C_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3549,plain,(
    ! [A_547,B_548,C_549,B_550] :
      ( r2_hidden('#skF_6'(A_547,B_548,C_549),B_550)
      | ~ r1_tarski(k1_relat_1(C_549),B_550)
      | ~ r2_hidden(A_547,k9_relat_1(C_549,B_548))
      | ~ v1_relat_1(C_549) ) ),
    inference(resolution,[status(thm)],[c_2878,c_2])).

tff(c_3582,plain,(
    ! [A_551,B_552,C_553,B_554] :
      ( m1_subset_1('#skF_6'(A_551,B_552,C_553),B_554)
      | ~ r1_tarski(k1_relat_1(C_553),B_554)
      | ~ r2_hidden(A_551,k9_relat_1(C_553,B_552))
      | ~ v1_relat_1(C_553) ) ),
    inference(resolution,[status(thm)],[c_3549,c_8])).

tff(c_3590,plain,(
    ! [A_555,B_556,B_557,A_558] :
      ( m1_subset_1('#skF_6'(A_555,B_556,B_557),A_558)
      | ~ r2_hidden(A_555,k9_relat_1(B_557,B_556))
      | ~ v4_relat_1(B_557,A_558)
      | ~ v1_relat_1(B_557) ) ),
    inference(resolution,[status(thm)],[c_14,c_3582])).

tff(c_5339,plain,(
    ! [A_734,A_735,A_736] :
      ( m1_subset_1('#skF_6'(A_734,k1_relat_1(A_735),A_735),A_736)
      | ~ r2_hidden(A_734,k2_relat_1(A_735))
      | ~ v4_relat_1(A_735,A_736)
      | ~ v1_relat_1(A_735)
      | ~ v1_relat_1(A_735) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3590])).

tff(c_2924,plain,(
    ! [A_476,B_477,C_478] :
      ( r2_hidden(k4_tarski('#skF_6'(A_476,B_477,C_478),A_476),C_478)
      | ~ r2_hidden(A_476,k9_relat_1(C_478,B_477))
      | ~ v1_relat_1(C_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    ! [E_88] :
      ( r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9')
      | ~ r2_hidden(k4_tarski(E_88,'#skF_12'),'#skF_9')
      | ~ m1_subset_1(E_88,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2754,plain,(
    ! [E_88] :
      ( ~ r2_hidden(k4_tarski(E_88,'#skF_12'),'#skF_9')
      | ~ m1_subset_1(E_88,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_2931,plain,(
    ! [B_477] :
      ( ~ m1_subset_1('#skF_6'('#skF_12',B_477,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_12',k9_relat_1('#skF_9',B_477))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2924,c_2754])).

tff(c_2997,plain,(
    ! [B_484] :
      ( ~ m1_subset_1('#skF_6'('#skF_12',B_484,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_12',k9_relat_1('#skF_9',B_484)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_2931])).

tff(c_3001,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_12',k1_relat_1('#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_12',k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2997])).

tff(c_3003,plain,(
    ~ m1_subset_1('#skF_6'('#skF_12',k1_relat_1('#skF_9'),'#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_2789,c_3001])).

tff(c_5346,plain,
    ( ~ r2_hidden('#skF_12',k2_relat_1('#skF_9'))
    | ~ v4_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_5339,c_3003])).

tff(c_5367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_120,c_2789,c_5346])).

tff(c_5368,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_18,plain,(
    ! [C_28,A_13,D_31] :
      ( r2_hidden(C_28,k2_relat_1(A_13))
      | ~ r2_hidden(k4_tarski(D_31,C_28),A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5377,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_5368,c_18])).

tff(c_5395,plain,(
    ! [A_738,B_739,C_740] :
      ( k2_relset_1(A_738,B_739,C_740) = k2_relat_1(C_740)
      | ~ m1_subset_1(C_740,k1_zfmisc_1(k2_zfmisc_1(A_738,B_739))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5404,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_5395])).

tff(c_52,plain,(
    ! [E_88] :
      ( ~ r2_hidden('#skF_10',k2_relset_1('#skF_8','#skF_7','#skF_9'))
      | ~ r2_hidden(k4_tarski(E_88,'#skF_12'),'#skF_9')
      | ~ m1_subset_1(E_88,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5380,plain,(
    ~ r2_hidden('#skF_10',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_5405,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5404,c_5380])).

tff(c_5411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5377,c_5405])).

tff(c_5412,plain,(
    ! [E_88] :
      ( ~ r2_hidden(k4_tarski(E_88,'#skF_12'),'#skF_9')
      | ~ m1_subset_1(E_88,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5701,plain,(
    ! [B_812] :
      ( ~ m1_subset_1('#skF_6'('#skF_12',B_812,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_12',k9_relat_1('#skF_9',B_812))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5694,c_5412])).

tff(c_5751,plain,(
    ! [B_817] :
      ( ~ m1_subset_1('#skF_6'('#skF_12',B_817,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_12',k9_relat_1('#skF_9',B_817)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_5701])).

tff(c_5755,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_12',k1_relat_1('#skF_9'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_12',k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5751])).

tff(c_5757,plain,(
    ~ m1_subset_1('#skF_6'('#skF_12',k1_relat_1('#skF_9'),'#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_5462,c_5755])).

tff(c_8538,plain,
    ( ~ r2_hidden('#skF_12',k2_relat_1('#skF_9'))
    | ~ v4_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_8531,c_5757])).

tff(c_8559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_120,c_5462,c_8538])).

tff(c_8561,plain,(
    ~ r2_hidden('#skF_12',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,
    ( r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9')
    | r2_hidden('#skF_12',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8572,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_8561,c_60])).

tff(c_8627,plain,(
    ! [C_1115,A_1116,D_1117] :
      ( r2_hidden(C_1115,k2_relat_1(A_1116))
      | ~ r2_hidden(k4_tarski(D_1117,C_1115),A_1116) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8635,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_8572,c_8627])).

tff(c_8702,plain,(
    ! [A_1134,B_1135,C_1136] :
      ( k2_relset_1(A_1134,B_1135,C_1136) = k2_relat_1(C_1136)
      | ~ m1_subset_1(C_1136,k1_zfmisc_1(k2_zfmisc_1(A_1134,B_1135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8716,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_8702])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_10',k2_relset_1('#skF_8','#skF_7','#skF_9'))
    | r2_hidden('#skF_12',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8679,plain,(
    ~ r2_hidden('#skF_10',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_8561,c_58])).

tff(c_8717,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8716,c_8679])).

tff(c_8721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8635,c_8717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.31/2.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.31/2.78  
% 8.31/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.31/2.78  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_12 > #skF_4
% 8.31/2.78  
% 8.31/2.78  %Foreground sorts:
% 8.31/2.78  
% 8.31/2.78  
% 8.31/2.78  %Background operators:
% 8.31/2.78  
% 8.31/2.78  
% 8.31/2.78  %Foreground operators:
% 8.31/2.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.31/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.31/2.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.31/2.78  tff('#skF_11', type, '#skF_11': $i).
% 8.31/2.78  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.31/2.78  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.31/2.78  tff('#skF_7', type, '#skF_7': $i).
% 8.31/2.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.31/2.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.31/2.78  tff('#skF_10', type, '#skF_10': $i).
% 8.31/2.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.31/2.78  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.31/2.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.31/2.78  tff('#skF_9', type, '#skF_9': $i).
% 8.31/2.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.31/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.31/2.78  tff('#skF_8', type, '#skF_8': $i).
% 8.31/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.31/2.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.31/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.31/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.31/2.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.31/2.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.31/2.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.31/2.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.31/2.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.31/2.78  tff('#skF_12', type, '#skF_12': $i).
% 8.31/2.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.31/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.31/2.78  
% 8.63/2.81  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.63/2.81  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 8.63/2.81  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.63/2.81  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.63/2.81  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.63/2.81  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 8.63/2.81  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.63/2.81  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 8.63/2.81  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.63/2.81  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 8.63/2.81  tff(f_57, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 8.63/2.81  tff(c_28, plain, (![A_32, B_33]: (v1_relat_1(k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.63/2.81  tff(c_46, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.63/2.81  tff(c_65, plain, (![B_93, A_94]: (v1_relat_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.63/2.81  tff(c_68, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_46, c_65])).
% 8.63/2.81  tff(c_71, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_68])).
% 8.63/2.81  tff(c_111, plain, (![C_106, A_107, B_108]: (v4_relat_1(C_106, A_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.63/2.81  tff(c_120, plain, (v4_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_46, c_111])).
% 8.63/2.81  tff(c_5448, plain, (![A_744, B_745, C_746]: (k2_relset_1(A_744, B_745, C_746)=k2_relat_1(C_746) | ~m1_subset_1(C_746, k1_zfmisc_1(k2_zfmisc_1(A_744, B_745))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.63/2.81  tff(c_5457, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_46, c_5448])).
% 8.63/2.81  tff(c_62, plain, (m1_subset_1('#skF_11', '#skF_8') | r2_hidden('#skF_12', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.63/2.81  tff(c_83, plain, (r2_hidden('#skF_12', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_62])).
% 8.63/2.81  tff(c_5462, plain, (r2_hidden('#skF_12', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_5457, c_83])).
% 8.63/2.81  tff(c_38, plain, (![A_40]: (k9_relat_1(A_40, k1_relat_1(A_40))=k2_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.63/2.81  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.63/2.81  tff(c_5581, plain, (![A_770, B_771, C_772]: (r2_hidden('#skF_6'(A_770, B_771, C_772), k1_relat_1(C_772)) | ~r2_hidden(A_770, k9_relat_1(C_772, B_771)) | ~v1_relat_1(C_772))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.63/2.81  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.63/2.81  tff(c_6402, plain, (![A_894, B_895, C_896, B_897]: (r2_hidden('#skF_6'(A_894, B_895, C_896), B_897) | ~r1_tarski(k1_relat_1(C_896), B_897) | ~r2_hidden(A_894, k9_relat_1(C_896, B_895)) | ~v1_relat_1(C_896))), inference(resolution, [status(thm)], [c_5581, c_2])).
% 8.63/2.81  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.63/2.81  tff(c_6436, plain, (![A_900, B_901, C_902, B_903]: (m1_subset_1('#skF_6'(A_900, B_901, C_902), B_903) | ~r1_tarski(k1_relat_1(C_902), B_903) | ~r2_hidden(A_900, k9_relat_1(C_902, B_901)) | ~v1_relat_1(C_902))), inference(resolution, [status(thm)], [c_6402, c_8])).
% 8.63/2.81  tff(c_6521, plain, (![A_910, B_911, B_912, A_913]: (m1_subset_1('#skF_6'(A_910, B_911, B_912), A_913) | ~r2_hidden(A_910, k9_relat_1(B_912, B_911)) | ~v4_relat_1(B_912, A_913) | ~v1_relat_1(B_912))), inference(resolution, [status(thm)], [c_14, c_6436])).
% 8.63/2.81  tff(c_8531, plain, (![A_1097, A_1098, A_1099]: (m1_subset_1('#skF_6'(A_1097, k1_relat_1(A_1098), A_1098), A_1099) | ~r2_hidden(A_1097, k2_relat_1(A_1098)) | ~v4_relat_1(A_1098, A_1099) | ~v1_relat_1(A_1098) | ~v1_relat_1(A_1098))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6521])).
% 8.63/2.81  tff(c_5694, plain, (![A_811, B_812, C_813]: (r2_hidden(k4_tarski('#skF_6'(A_811, B_812, C_813), A_811), C_813) | ~r2_hidden(A_811, k9_relat_1(C_813, B_812)) | ~v1_relat_1(C_813))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.63/2.81  tff(c_2772, plain, (![A_430, B_431, C_432]: (k2_relset_1(A_430, B_431, C_432)=k2_relat_1(C_432) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.63/2.81  tff(c_2786, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_46, c_2772])).
% 8.63/2.81  tff(c_2789, plain, (r2_hidden('#skF_12', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2786, c_83])).
% 8.63/2.81  tff(c_2878, plain, (![A_446, B_447, C_448]: (r2_hidden('#skF_6'(A_446, B_447, C_448), k1_relat_1(C_448)) | ~r2_hidden(A_446, k9_relat_1(C_448, B_447)) | ~v1_relat_1(C_448))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.63/2.81  tff(c_3549, plain, (![A_547, B_548, C_549, B_550]: (r2_hidden('#skF_6'(A_547, B_548, C_549), B_550) | ~r1_tarski(k1_relat_1(C_549), B_550) | ~r2_hidden(A_547, k9_relat_1(C_549, B_548)) | ~v1_relat_1(C_549))), inference(resolution, [status(thm)], [c_2878, c_2])).
% 8.63/2.81  tff(c_3582, plain, (![A_551, B_552, C_553, B_554]: (m1_subset_1('#skF_6'(A_551, B_552, C_553), B_554) | ~r1_tarski(k1_relat_1(C_553), B_554) | ~r2_hidden(A_551, k9_relat_1(C_553, B_552)) | ~v1_relat_1(C_553))), inference(resolution, [status(thm)], [c_3549, c_8])).
% 8.63/2.81  tff(c_3590, plain, (![A_555, B_556, B_557, A_558]: (m1_subset_1('#skF_6'(A_555, B_556, B_557), A_558) | ~r2_hidden(A_555, k9_relat_1(B_557, B_556)) | ~v4_relat_1(B_557, A_558) | ~v1_relat_1(B_557))), inference(resolution, [status(thm)], [c_14, c_3582])).
% 8.63/2.81  tff(c_5339, plain, (![A_734, A_735, A_736]: (m1_subset_1('#skF_6'(A_734, k1_relat_1(A_735), A_735), A_736) | ~r2_hidden(A_734, k2_relat_1(A_735)) | ~v4_relat_1(A_735, A_736) | ~v1_relat_1(A_735) | ~v1_relat_1(A_735))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3590])).
% 8.63/2.81  tff(c_2924, plain, (![A_476, B_477, C_478]: (r2_hidden(k4_tarski('#skF_6'(A_476, B_477, C_478), A_476), C_478) | ~r2_hidden(A_476, k9_relat_1(C_478, B_477)) | ~v1_relat_1(C_478))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.63/2.81  tff(c_54, plain, (![E_88]: (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9') | ~r2_hidden(k4_tarski(E_88, '#skF_12'), '#skF_9') | ~m1_subset_1(E_88, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.63/2.81  tff(c_2754, plain, (![E_88]: (~r2_hidden(k4_tarski(E_88, '#skF_12'), '#skF_9') | ~m1_subset_1(E_88, '#skF_8'))), inference(splitLeft, [status(thm)], [c_54])).
% 8.63/2.81  tff(c_2931, plain, (![B_477]: (~m1_subset_1('#skF_6'('#skF_12', B_477, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_12', k9_relat_1('#skF_9', B_477)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_2924, c_2754])).
% 8.63/2.81  tff(c_2997, plain, (![B_484]: (~m1_subset_1('#skF_6'('#skF_12', B_484, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_12', k9_relat_1('#skF_9', B_484)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_2931])).
% 8.63/2.81  tff(c_3001, plain, (~m1_subset_1('#skF_6'('#skF_12', k1_relat_1('#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_12', k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2997])).
% 8.63/2.81  tff(c_3003, plain, (~m1_subset_1('#skF_6'('#skF_12', k1_relat_1('#skF_9'), '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_2789, c_3001])).
% 8.63/2.81  tff(c_5346, plain, (~r2_hidden('#skF_12', k2_relat_1('#skF_9')) | ~v4_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_5339, c_3003])).
% 8.63/2.81  tff(c_5367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_120, c_2789, c_5346])).
% 8.63/2.81  tff(c_5368, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_54])).
% 8.63/2.81  tff(c_18, plain, (![C_28, A_13, D_31]: (r2_hidden(C_28, k2_relat_1(A_13)) | ~r2_hidden(k4_tarski(D_31, C_28), A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.63/2.81  tff(c_5377, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_5368, c_18])).
% 8.63/2.81  tff(c_5395, plain, (![A_738, B_739, C_740]: (k2_relset_1(A_738, B_739, C_740)=k2_relat_1(C_740) | ~m1_subset_1(C_740, k1_zfmisc_1(k2_zfmisc_1(A_738, B_739))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.63/2.81  tff(c_5404, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_46, c_5395])).
% 8.63/2.81  tff(c_52, plain, (![E_88]: (~r2_hidden('#skF_10', k2_relset_1('#skF_8', '#skF_7', '#skF_9')) | ~r2_hidden(k4_tarski(E_88, '#skF_12'), '#skF_9') | ~m1_subset_1(E_88, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.63/2.81  tff(c_5380, plain, (~r2_hidden('#skF_10', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_52])).
% 8.63/2.81  tff(c_5405, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_5404, c_5380])).
% 8.63/2.81  tff(c_5411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5377, c_5405])).
% 8.63/2.81  tff(c_5412, plain, (![E_88]: (~r2_hidden(k4_tarski(E_88, '#skF_12'), '#skF_9') | ~m1_subset_1(E_88, '#skF_8'))), inference(splitRight, [status(thm)], [c_52])).
% 8.63/2.81  tff(c_5701, plain, (![B_812]: (~m1_subset_1('#skF_6'('#skF_12', B_812, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_12', k9_relat_1('#skF_9', B_812)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_5694, c_5412])).
% 8.63/2.81  tff(c_5751, plain, (![B_817]: (~m1_subset_1('#skF_6'('#skF_12', B_817, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_12', k9_relat_1('#skF_9', B_817)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_5701])).
% 8.63/2.81  tff(c_5755, plain, (~m1_subset_1('#skF_6'('#skF_12', k1_relat_1('#skF_9'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_12', k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_38, c_5751])).
% 8.63/2.81  tff(c_5757, plain, (~m1_subset_1('#skF_6'('#skF_12', k1_relat_1('#skF_9'), '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_5462, c_5755])).
% 8.63/2.81  tff(c_8538, plain, (~r2_hidden('#skF_12', k2_relat_1('#skF_9')) | ~v4_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_8531, c_5757])).
% 8.63/2.81  tff(c_8559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_120, c_5462, c_8538])).
% 8.63/2.81  tff(c_8561, plain, (~r2_hidden('#skF_12', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_62])).
% 8.63/2.81  tff(c_60, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9') | r2_hidden('#skF_12', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.63/2.81  tff(c_8572, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_8561, c_60])).
% 8.63/2.81  tff(c_8627, plain, (![C_1115, A_1116, D_1117]: (r2_hidden(C_1115, k2_relat_1(A_1116)) | ~r2_hidden(k4_tarski(D_1117, C_1115), A_1116))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.63/2.81  tff(c_8635, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_8572, c_8627])).
% 8.63/2.81  tff(c_8702, plain, (![A_1134, B_1135, C_1136]: (k2_relset_1(A_1134, B_1135, C_1136)=k2_relat_1(C_1136) | ~m1_subset_1(C_1136, k1_zfmisc_1(k2_zfmisc_1(A_1134, B_1135))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.63/2.81  tff(c_8716, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_46, c_8702])).
% 8.63/2.81  tff(c_58, plain, (~r2_hidden('#skF_10', k2_relset_1('#skF_8', '#skF_7', '#skF_9')) | r2_hidden('#skF_12', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.63/2.81  tff(c_8679, plain, (~r2_hidden('#skF_10', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_8561, c_58])).
% 8.63/2.81  tff(c_8717, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_8716, c_8679])).
% 8.63/2.81  tff(c_8721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8635, c_8717])).
% 8.63/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.63/2.81  
% 8.63/2.81  Inference rules
% 8.63/2.81  ----------------------
% 8.63/2.81  #Ref     : 0
% 8.63/2.81  #Sup     : 1968
% 8.63/2.81  #Fact    : 0
% 8.63/2.81  #Define  : 0
% 8.63/2.81  #Split   : 13
% 8.63/2.81  #Chain   : 0
% 8.63/2.81  #Close   : 0
% 8.63/2.81  
% 8.63/2.81  Ordering : KBO
% 8.63/2.81  
% 8.63/2.81  Simplification rules
% 8.63/2.81  ----------------------
% 8.63/2.81  #Subsume      : 133
% 8.63/2.81  #Demod        : 87
% 8.63/2.81  #Tautology    : 122
% 8.63/2.81  #SimpNegUnit  : 2
% 8.63/2.81  #BackRed      : 17
% 8.63/2.81  
% 8.63/2.81  #Partial instantiations: 0
% 8.63/2.81  #Strategies tried      : 1
% 8.63/2.81  
% 8.63/2.81  Timing (in seconds)
% 8.63/2.81  ----------------------
% 8.63/2.81  Preprocessing        : 0.32
% 8.63/2.81  Parsing              : 0.16
% 8.63/2.81  CNF conversion       : 0.03
% 8.63/2.81  Main loop            : 1.72
% 8.63/2.81  Inferencing          : 0.61
% 8.63/2.81  Reduction            : 0.40
% 8.63/2.81  Demodulation         : 0.26
% 8.63/2.81  BG Simplification    : 0.08
% 8.63/2.81  Subsumption          : 0.46
% 8.63/2.81  Abstraction          : 0.09
% 8.63/2.81  MUC search           : 0.00
% 8.63/2.81  Cooper               : 0.00
% 8.63/2.81  Total                : 2.08
% 8.63/2.81  Index Insertion      : 0.00
% 8.63/2.81  Index Deletion       : 0.00
% 8.63/2.81  Index Matching       : 0.00
% 8.63/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
