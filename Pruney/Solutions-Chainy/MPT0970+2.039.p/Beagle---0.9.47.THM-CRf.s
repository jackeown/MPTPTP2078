%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:24 EST 2020

% Result     : Theorem 10.08s
% Output     : CNFRefutation 10.08s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 537 expanded)
%              Number of leaves         :   36 ( 201 expanded)
%              Depth                    :   17
%              Number of atoms          :  218 (1590 expanded)
%              Number of equality atoms :   44 ( 398 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_143,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_147,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_143])).

tff(c_38,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_156,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [D_35] :
      ( r2_hidden('#skF_7'(D_35),'#skF_4')
      | ~ r2_hidden(D_35,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    ! [D_35] :
      ( k1_funct_1('#skF_6','#skF_7'(D_35)) = D_35
      | ~ r2_hidden(D_35,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_75,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_79,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4591,plain,(
    ! [D_488,C_489,A_490,B_491] :
      ( r2_hidden(k1_funct_1(D_488,C_489),k2_relset_1(A_490,B_491,D_488))
      | k1_xboole_0 = B_491
      | ~ r2_hidden(C_489,A_490)
      | ~ m1_subset_1(D_488,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491)))
      | ~ v1_funct_2(D_488,A_490,B_491)
      | ~ v1_funct_1(D_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4601,plain,(
    ! [C_489] :
      ( r2_hidden(k1_funct_1('#skF_6',C_489),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_489,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_4591])).

tff(c_4609,plain,(
    ! [C_489] :
      ( r2_hidden(k1_funct_1('#skF_6',C_489),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_489,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_4601])).

tff(c_4612,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4609])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_107,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_70)
      | r2_hidden('#skF_2'(A_69,B_70),A_69)
      | B_70 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_161,plain,(
    ! [A_79,B_80] :
      ( ~ r1_tarski(A_79,'#skF_2'(A_79,B_80))
      | r2_hidden('#skF_1'(A_79,B_80),B_80)
      | B_80 = A_79 ) ),
    inference(resolution,[status(thm)],[c_107,c_30])).

tff(c_165,plain,(
    ! [B_80] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_80),B_80)
      | k1_xboole_0 = B_80 ) ),
    inference(resolution,[status(thm)],[c_10,c_161])).

tff(c_4631,plain,(
    ! [B_80] :
      ( r2_hidden('#skF_1'('#skF_5',B_80),B_80)
      | B_80 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4612,c_4612,c_165])).

tff(c_260,plain,(
    ! [B_98,A_99] :
      ( ~ r1_tarski(B_98,'#skF_1'(A_99,B_98))
      | r2_hidden('#skF_2'(A_99,B_98),A_99)
      | B_98 = A_99 ) ),
    inference(resolution,[status(thm)],[c_107,c_30])).

tff(c_264,plain,(
    ! [A_99] :
      ( r2_hidden('#skF_2'(A_99,k1_xboole_0),A_99)
      | k1_xboole_0 = A_99 ) ),
    inference(resolution,[status(thm)],[c_10,c_260])).

tff(c_148,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_3'(A_76,B_77,C_78),B_77)
      | ~ r2_hidden(A_76,k9_relat_1(C_78,B_77))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_322,plain,(
    ! [B_109,A_110,C_111] :
      ( ~ r1_tarski(B_109,'#skF_3'(A_110,B_109,C_111))
      | ~ r2_hidden(A_110,k9_relat_1(C_111,B_109))
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_148,c_30])).

tff(c_327,plain,(
    ! [A_112,C_113] :
      ( ~ r2_hidden(A_112,k9_relat_1(C_113,k1_xboole_0))
      | ~ v1_relat_1(C_113) ) ),
    inference(resolution,[status(thm)],[c_10,c_322])).

tff(c_378,plain,(
    ! [C_114] :
      ( ~ v1_relat_1(C_114)
      | k9_relat_1(C_114,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_264,c_327])).

tff(c_382,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79,c_378])).

tff(c_326,plain,(
    ! [A_110,C_111] :
      ( ~ r2_hidden(A_110,k9_relat_1(C_111,k1_xboole_0))
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_10,c_322])).

tff(c_386,plain,(
    ! [A_110] :
      ( ~ r2_hidden(A_110,k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_326])).

tff(c_390,plain,(
    ! [A_110] : ~ r2_hidden(A_110,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_386])).

tff(c_4619,plain,(
    ! [A_110] : ~ r2_hidden(A_110,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4612,c_390])).

tff(c_304,plain,(
    ! [A_106,B_107,C_108] :
      ( r2_hidden(k4_tarski('#skF_3'(A_106,B_107,C_108),A_106),C_108)
      | ~ r2_hidden(A_106,k9_relat_1(C_108,B_107))
      | ~ v1_relat_1(C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [C_12,A_9,B_10] :
      ( r2_hidden(C_12,A_9)
      | ~ r2_hidden(C_12,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6328,plain,(
    ! [A_676,B_677,C_678,A_679] :
      ( r2_hidden(k4_tarski('#skF_3'(A_676,B_677,C_678),A_676),A_679)
      | ~ m1_subset_1(C_678,k1_zfmisc_1(A_679))
      | ~ r2_hidden(A_676,k9_relat_1(C_678,B_677))
      | ~ v1_relat_1(C_678) ) ),
    inference(resolution,[status(thm)],[c_304,c_18])).

tff(c_14,plain,(
    ! [B_6,D_8,A_5,C_7] :
      ( r2_hidden(B_6,D_8)
      | ~ r2_hidden(k4_tarski(A_5,B_6),k2_zfmisc_1(C_7,D_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8221,plain,(
    ! [D_837,C_840,C_839,A_841,B_838] :
      ( r2_hidden(A_841,D_837)
      | ~ m1_subset_1(C_840,k1_zfmisc_1(k2_zfmisc_1(C_839,D_837)))
      | ~ r2_hidden(A_841,k9_relat_1(C_840,B_838))
      | ~ v1_relat_1(C_840) ) ),
    inference(resolution,[status(thm)],[c_6328,c_14])).

tff(c_8223,plain,(
    ! [A_841,B_838] :
      ( r2_hidden(A_841,'#skF_5')
      | ~ r2_hidden(A_841,k9_relat_1('#skF_6',B_838))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_8221])).

tff(c_8226,plain,(
    ! [A_841,B_838] :
      ( r2_hidden(A_841,'#skF_5')
      | ~ r2_hidden(A_841,k9_relat_1('#skF_6',B_838)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_8223])).

tff(c_8309,plain,(
    ! [A_844,B_845] : ~ r2_hidden(A_844,k9_relat_1('#skF_6',B_845)) ),
    inference(negUnitSimplification,[status(thm)],[c_4619,c_8226])).

tff(c_8474,plain,(
    ! [B_846] : k9_relat_1('#skF_6',B_846) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4631,c_8309])).

tff(c_28,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8631,plain,
    ( k2_relat_1('#skF_6') = '#skF_5'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8474,c_28])).

tff(c_8742,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_8631])).

tff(c_8744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_8742])).

tff(c_8747,plain,(
    ! [C_847] :
      ( r2_hidden(k1_funct_1('#skF_6',C_847),k2_relat_1('#skF_6'))
      | ~ r2_hidden(C_847,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_4609])).

tff(c_8766,plain,(
    ! [D_853] :
      ( r2_hidden(D_853,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_853),'#skF_4')
      | ~ r2_hidden(D_853,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_8747])).

tff(c_8775,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_35,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_8766])).

tff(c_9353,plain,(
    ! [A_923,B_924,A_925] :
      ( r2_hidden('#skF_2'(A_923,B_924),A_925)
      | ~ m1_subset_1(A_923,k1_zfmisc_1(A_925))
      | r2_hidden('#skF_1'(A_923,B_924),B_924)
      | B_924 = A_923 ) ),
    inference(resolution,[status(thm)],[c_107,c_18])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9441,plain,(
    ! [A_926,A_927] :
      ( ~ m1_subset_1(A_926,k1_zfmisc_1(A_927))
      | r2_hidden('#skF_1'(A_926,A_927),A_927)
      | A_927 = A_926 ) ),
    inference(resolution,[status(thm)],[c_9353,c_4])).

tff(c_9573,plain,(
    ! [A_937,A_938,A_939] :
      ( r2_hidden('#skF_1'(A_937,A_938),A_939)
      | ~ m1_subset_1(A_938,k1_zfmisc_1(A_939))
      | ~ m1_subset_1(A_937,k1_zfmisc_1(A_938))
      | A_938 = A_937 ) ),
    inference(resolution,[status(thm)],[c_9441,c_18])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9678,plain,(
    ! [A_954,A_955] :
      ( ~ r2_hidden('#skF_2'(A_954,A_955),A_955)
      | ~ m1_subset_1(A_955,k1_zfmisc_1(A_954))
      | ~ m1_subset_1(A_954,k1_zfmisc_1(A_955))
      | A_955 = A_954 ) ),
    inference(resolution,[status(thm)],[c_9573,c_2])).

tff(c_14323,plain,(
    ! [A_1234] :
      ( ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(A_1234))
      | ~ m1_subset_1(A_1234,k1_zfmisc_1(k2_relat_1('#skF_6')))
      | k2_relat_1('#skF_6') = A_1234
      | ~ r2_hidden('#skF_2'(A_1234,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8775,c_9678])).

tff(c_14345,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_relat_1('#skF_6')))
    | ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_14323])).

tff(c_14361,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_relat_1('#skF_6')))
    | ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_156,c_14345])).

tff(c_14918,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_14361])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10560,plain,(
    ! [A_1032,B_1033,C_1034,A_1035] :
      ( r2_hidden(k4_tarski('#skF_3'(A_1032,B_1033,C_1034),A_1032),A_1035)
      | ~ m1_subset_1(C_1034,k1_zfmisc_1(A_1035))
      | ~ r2_hidden(A_1032,k9_relat_1(C_1034,B_1033))
      | ~ v1_relat_1(C_1034) ) ),
    inference(resolution,[status(thm)],[c_304,c_18])).

tff(c_13218,plain,(
    ! [A_1192,C_1191,D_1188,C_1190,B_1189] :
      ( r2_hidden(A_1192,D_1188)
      | ~ m1_subset_1(C_1190,k1_zfmisc_1(k2_zfmisc_1(C_1191,D_1188)))
      | ~ r2_hidden(A_1192,k9_relat_1(C_1190,B_1189))
      | ~ v1_relat_1(C_1190) ) ),
    inference(resolution,[status(thm)],[c_10560,c_14])).

tff(c_13220,plain,(
    ! [A_1192,B_1189] :
      ( r2_hidden(A_1192,'#skF_5')
      | ~ r2_hidden(A_1192,k9_relat_1('#skF_6',B_1189))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_13218])).

tff(c_13224,plain,(
    ! [A_1193,B_1194] :
      ( r2_hidden(A_1193,'#skF_5')
      | ~ r2_hidden(A_1193,k9_relat_1('#skF_6',B_1194)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_13220])).

tff(c_13354,plain,(
    ! [A_1193] :
      ( r2_hidden(A_1193,'#skF_5')
      | ~ r2_hidden(A_1193,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_13224])).

tff(c_13392,plain,(
    ! [A_1195] :
      ( r2_hidden(A_1195,'#skF_5')
      | ~ r2_hidden(A_1195,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_13354])).

tff(c_13537,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_6')),'#skF_5')
      | r2_hidden('#skF_2'(A_1,k2_relat_1('#skF_6')),A_1)
      | k2_relat_1('#skF_6') = A_1 ) ),
    inference(resolution,[status(thm)],[c_8,c_13392])).

tff(c_8776,plain,(
    ! [D_854] :
      ( r2_hidden(D_854,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_854,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_8766])).

tff(c_8798,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_6')),k2_relat_1('#skF_6'))
      | k2_relat_1('#skF_6') = A_1
      | ~ r2_hidden('#skF_2'(A_1,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8776,c_4])).

tff(c_16160,plain,(
    ! [A_1316] :
      ( r2_hidden('#skF_1'(A_1316,k2_relat_1('#skF_6')),'#skF_5')
      | k2_relat_1('#skF_6') = A_1316
      | ~ r2_hidden('#skF_2'(A_1316,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8798,c_13392])).

tff(c_16168,plain,
    ( r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_13537,c_16160])).

tff(c_16203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_14918,c_156,c_14918,c_16168])).

tff(c_16205,plain,(
    r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_14361])).

tff(c_16219,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5',k2_relat_1('#skF_6')),k2_relat_1('#skF_6'))
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16205,c_2])).

tff(c_16234,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k2_relat_1('#skF_6')),k2_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_16219])).

tff(c_16251,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_8775,c_16234])).

tff(c_16267,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5',k2_relat_1('#skF_6')),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_16251])).

tff(c_16282,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16205,c_16267])).

tff(c_16284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_16282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.08/3.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/3.84  
% 10.08/3.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/3.84  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 10.08/3.84  
% 10.08/3.84  %Foreground sorts:
% 10.08/3.84  
% 10.08/3.84  
% 10.08/3.84  %Background operators:
% 10.08/3.84  
% 10.08/3.84  
% 10.08/3.84  %Foreground operators:
% 10.08/3.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.08/3.84  tff('#skF_7', type, '#skF_7': $i > $i).
% 10.08/3.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.08/3.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.08/3.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.08/3.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.08/3.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.08/3.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.08/3.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.08/3.84  tff('#skF_5', type, '#skF_5': $i).
% 10.08/3.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.08/3.84  tff('#skF_6', type, '#skF_6': $i).
% 10.08/3.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.08/3.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.08/3.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.08/3.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.08/3.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.08/3.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.08/3.84  tff('#skF_4', type, '#skF_4': $i).
% 10.08/3.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.08/3.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.08/3.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.08/3.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.08/3.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.08/3.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.08/3.84  
% 10.08/3.86  tff(f_106, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 10.08/3.86  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.08/3.86  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 10.08/3.86  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.08/3.86  tff(f_87, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 10.08/3.86  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.08/3.86  tff(f_67, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 10.08/3.86  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 10.08/3.86  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 10.08/3.86  tff(f_40, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 10.08/3.86  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 10.08/3.86  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.08/3.86  tff(c_143, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.08/3.86  tff(c_147, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_143])).
% 10.08/3.86  tff(c_38, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.08/3.86  tff(c_156, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_38])).
% 10.08/3.86  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.08/3.86  tff(c_48, plain, (![D_35]: (r2_hidden('#skF_7'(D_35), '#skF_4') | ~r2_hidden(D_35, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.08/3.86  tff(c_46, plain, (![D_35]: (k1_funct_1('#skF_6', '#skF_7'(D_35))=D_35 | ~r2_hidden(D_35, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.08/3.86  tff(c_75, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.08/3.86  tff(c_79, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_75])).
% 10.08/3.86  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.08/3.86  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.08/3.86  tff(c_4591, plain, (![D_488, C_489, A_490, B_491]: (r2_hidden(k1_funct_1(D_488, C_489), k2_relset_1(A_490, B_491, D_488)) | k1_xboole_0=B_491 | ~r2_hidden(C_489, A_490) | ~m1_subset_1(D_488, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))) | ~v1_funct_2(D_488, A_490, B_491) | ~v1_funct_1(D_488))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.08/3.86  tff(c_4601, plain, (![C_489]: (r2_hidden(k1_funct_1('#skF_6', C_489), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_489, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_4591])).
% 10.08/3.86  tff(c_4609, plain, (![C_489]: (r2_hidden(k1_funct_1('#skF_6', C_489), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_489, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_4601])).
% 10.08/3.86  tff(c_4612, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_4609])).
% 10.08/3.86  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.08/3.86  tff(c_107, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), B_70) | r2_hidden('#skF_2'(A_69, B_70), A_69) | B_70=A_69)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.08/3.86  tff(c_30, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.08/3.86  tff(c_161, plain, (![A_79, B_80]: (~r1_tarski(A_79, '#skF_2'(A_79, B_80)) | r2_hidden('#skF_1'(A_79, B_80), B_80) | B_80=A_79)), inference(resolution, [status(thm)], [c_107, c_30])).
% 10.08/3.86  tff(c_165, plain, (![B_80]: (r2_hidden('#skF_1'(k1_xboole_0, B_80), B_80) | k1_xboole_0=B_80)), inference(resolution, [status(thm)], [c_10, c_161])).
% 10.08/3.86  tff(c_4631, plain, (![B_80]: (r2_hidden('#skF_1'('#skF_5', B_80), B_80) | B_80='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4612, c_4612, c_165])).
% 10.08/3.86  tff(c_260, plain, (![B_98, A_99]: (~r1_tarski(B_98, '#skF_1'(A_99, B_98)) | r2_hidden('#skF_2'(A_99, B_98), A_99) | B_98=A_99)), inference(resolution, [status(thm)], [c_107, c_30])).
% 10.08/3.86  tff(c_264, plain, (![A_99]: (r2_hidden('#skF_2'(A_99, k1_xboole_0), A_99) | k1_xboole_0=A_99)), inference(resolution, [status(thm)], [c_10, c_260])).
% 10.08/3.86  tff(c_148, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_3'(A_76, B_77, C_78), B_77) | ~r2_hidden(A_76, k9_relat_1(C_78, B_77)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.08/3.86  tff(c_322, plain, (![B_109, A_110, C_111]: (~r1_tarski(B_109, '#skF_3'(A_110, B_109, C_111)) | ~r2_hidden(A_110, k9_relat_1(C_111, B_109)) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_148, c_30])).
% 10.08/3.86  tff(c_327, plain, (![A_112, C_113]: (~r2_hidden(A_112, k9_relat_1(C_113, k1_xboole_0)) | ~v1_relat_1(C_113))), inference(resolution, [status(thm)], [c_10, c_322])).
% 10.08/3.86  tff(c_378, plain, (![C_114]: (~v1_relat_1(C_114) | k9_relat_1(C_114, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_264, c_327])).
% 10.08/3.86  tff(c_382, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_79, c_378])).
% 10.08/3.86  tff(c_326, plain, (![A_110, C_111]: (~r2_hidden(A_110, k9_relat_1(C_111, k1_xboole_0)) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_10, c_322])).
% 10.08/3.86  tff(c_386, plain, (![A_110]: (~r2_hidden(A_110, k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_382, c_326])).
% 10.08/3.86  tff(c_390, plain, (![A_110]: (~r2_hidden(A_110, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_386])).
% 10.08/3.86  tff(c_4619, plain, (![A_110]: (~r2_hidden(A_110, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4612, c_390])).
% 10.08/3.86  tff(c_304, plain, (![A_106, B_107, C_108]: (r2_hidden(k4_tarski('#skF_3'(A_106, B_107, C_108), A_106), C_108) | ~r2_hidden(A_106, k9_relat_1(C_108, B_107)) | ~v1_relat_1(C_108))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.08/3.86  tff(c_18, plain, (![C_12, A_9, B_10]: (r2_hidden(C_12, A_9) | ~r2_hidden(C_12, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.08/3.86  tff(c_6328, plain, (![A_676, B_677, C_678, A_679]: (r2_hidden(k4_tarski('#skF_3'(A_676, B_677, C_678), A_676), A_679) | ~m1_subset_1(C_678, k1_zfmisc_1(A_679)) | ~r2_hidden(A_676, k9_relat_1(C_678, B_677)) | ~v1_relat_1(C_678))), inference(resolution, [status(thm)], [c_304, c_18])).
% 10.08/3.86  tff(c_14, plain, (![B_6, D_8, A_5, C_7]: (r2_hidden(B_6, D_8) | ~r2_hidden(k4_tarski(A_5, B_6), k2_zfmisc_1(C_7, D_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.08/3.86  tff(c_8221, plain, (![D_837, C_840, C_839, A_841, B_838]: (r2_hidden(A_841, D_837) | ~m1_subset_1(C_840, k1_zfmisc_1(k2_zfmisc_1(C_839, D_837))) | ~r2_hidden(A_841, k9_relat_1(C_840, B_838)) | ~v1_relat_1(C_840))), inference(resolution, [status(thm)], [c_6328, c_14])).
% 10.08/3.86  tff(c_8223, plain, (![A_841, B_838]: (r2_hidden(A_841, '#skF_5') | ~r2_hidden(A_841, k9_relat_1('#skF_6', B_838)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_8221])).
% 10.08/3.86  tff(c_8226, plain, (![A_841, B_838]: (r2_hidden(A_841, '#skF_5') | ~r2_hidden(A_841, k9_relat_1('#skF_6', B_838)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_8223])).
% 10.08/3.86  tff(c_8309, plain, (![A_844, B_845]: (~r2_hidden(A_844, k9_relat_1('#skF_6', B_845)))), inference(negUnitSimplification, [status(thm)], [c_4619, c_8226])).
% 10.08/3.86  tff(c_8474, plain, (![B_846]: (k9_relat_1('#skF_6', B_846)='#skF_5')), inference(resolution, [status(thm)], [c_4631, c_8309])).
% 10.08/3.86  tff(c_28, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.08/3.86  tff(c_8631, plain, (k2_relat_1('#skF_6')='#skF_5' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8474, c_28])).
% 10.08/3.86  tff(c_8742, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_8631])).
% 10.08/3.86  tff(c_8744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_8742])).
% 10.08/3.86  tff(c_8747, plain, (![C_847]: (r2_hidden(k1_funct_1('#skF_6', C_847), k2_relat_1('#skF_6')) | ~r2_hidden(C_847, '#skF_4'))), inference(splitRight, [status(thm)], [c_4609])).
% 10.08/3.86  tff(c_8766, plain, (![D_853]: (r2_hidden(D_853, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_853), '#skF_4') | ~r2_hidden(D_853, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_8747])).
% 10.08/3.86  tff(c_8775, plain, (![D_35]: (r2_hidden(D_35, k2_relat_1('#skF_6')) | ~r2_hidden(D_35, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_8766])).
% 10.08/3.86  tff(c_9353, plain, (![A_923, B_924, A_925]: (r2_hidden('#skF_2'(A_923, B_924), A_925) | ~m1_subset_1(A_923, k1_zfmisc_1(A_925)) | r2_hidden('#skF_1'(A_923, B_924), B_924) | B_924=A_923)), inference(resolution, [status(thm)], [c_107, c_18])).
% 10.08/3.86  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.08/3.86  tff(c_9441, plain, (![A_926, A_927]: (~m1_subset_1(A_926, k1_zfmisc_1(A_927)) | r2_hidden('#skF_1'(A_926, A_927), A_927) | A_927=A_926)), inference(resolution, [status(thm)], [c_9353, c_4])).
% 10.08/3.86  tff(c_9573, plain, (![A_937, A_938, A_939]: (r2_hidden('#skF_1'(A_937, A_938), A_939) | ~m1_subset_1(A_938, k1_zfmisc_1(A_939)) | ~m1_subset_1(A_937, k1_zfmisc_1(A_938)) | A_938=A_937)), inference(resolution, [status(thm)], [c_9441, c_18])).
% 10.08/3.86  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.08/3.86  tff(c_9678, plain, (![A_954, A_955]: (~r2_hidden('#skF_2'(A_954, A_955), A_955) | ~m1_subset_1(A_955, k1_zfmisc_1(A_954)) | ~m1_subset_1(A_954, k1_zfmisc_1(A_955)) | A_955=A_954)), inference(resolution, [status(thm)], [c_9573, c_2])).
% 10.08/3.86  tff(c_14323, plain, (![A_1234]: (~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(A_1234)) | ~m1_subset_1(A_1234, k1_zfmisc_1(k2_relat_1('#skF_6'))) | k2_relat_1('#skF_6')=A_1234 | ~r2_hidden('#skF_2'(A_1234, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_8775, c_9678])).
% 10.08/3.86  tff(c_14345, plain, (~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_relat_1('#skF_6'))) | ~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_6, c_14323])).
% 10.08/3.86  tff(c_14361, plain, (~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_relat_1('#skF_6'))) | ~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_156, c_156, c_14345])).
% 10.08/3.86  tff(c_14918, plain, (~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_14361])).
% 10.08/3.86  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.08/3.86  tff(c_10560, plain, (![A_1032, B_1033, C_1034, A_1035]: (r2_hidden(k4_tarski('#skF_3'(A_1032, B_1033, C_1034), A_1032), A_1035) | ~m1_subset_1(C_1034, k1_zfmisc_1(A_1035)) | ~r2_hidden(A_1032, k9_relat_1(C_1034, B_1033)) | ~v1_relat_1(C_1034))), inference(resolution, [status(thm)], [c_304, c_18])).
% 10.08/3.86  tff(c_13218, plain, (![A_1192, C_1191, D_1188, C_1190, B_1189]: (r2_hidden(A_1192, D_1188) | ~m1_subset_1(C_1190, k1_zfmisc_1(k2_zfmisc_1(C_1191, D_1188))) | ~r2_hidden(A_1192, k9_relat_1(C_1190, B_1189)) | ~v1_relat_1(C_1190))), inference(resolution, [status(thm)], [c_10560, c_14])).
% 10.08/3.86  tff(c_13220, plain, (![A_1192, B_1189]: (r2_hidden(A_1192, '#skF_5') | ~r2_hidden(A_1192, k9_relat_1('#skF_6', B_1189)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_13218])).
% 10.08/3.86  tff(c_13224, plain, (![A_1193, B_1194]: (r2_hidden(A_1193, '#skF_5') | ~r2_hidden(A_1193, k9_relat_1('#skF_6', B_1194)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_13220])).
% 10.08/3.86  tff(c_13354, plain, (![A_1193]: (r2_hidden(A_1193, '#skF_5') | ~r2_hidden(A_1193, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_13224])).
% 10.08/3.86  tff(c_13392, plain, (![A_1195]: (r2_hidden(A_1195, '#skF_5') | ~r2_hidden(A_1195, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_13354])).
% 10.08/3.86  tff(c_13537, plain, (![A_1]: (r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_6')), '#skF_5') | r2_hidden('#skF_2'(A_1, k2_relat_1('#skF_6')), A_1) | k2_relat_1('#skF_6')=A_1)), inference(resolution, [status(thm)], [c_8, c_13392])).
% 10.08/3.86  tff(c_8776, plain, (![D_854]: (r2_hidden(D_854, k2_relat_1('#skF_6')) | ~r2_hidden(D_854, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_8766])).
% 10.08/3.86  tff(c_8798, plain, (![A_1]: (r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_6')), k2_relat_1('#skF_6')) | k2_relat_1('#skF_6')=A_1 | ~r2_hidden('#skF_2'(A_1, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_8776, c_4])).
% 10.08/3.86  tff(c_16160, plain, (![A_1316]: (r2_hidden('#skF_1'(A_1316, k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')=A_1316 | ~r2_hidden('#skF_2'(A_1316, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_8798, c_13392])).
% 10.08/3.86  tff(c_16168, plain, (r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_13537, c_16160])).
% 10.08/3.86  tff(c_16203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_14918, c_156, c_14918, c_16168])).
% 10.08/3.86  tff(c_16205, plain, (r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(splitRight, [status(thm)], [c_14361])).
% 10.08/3.86  tff(c_16219, plain, (~r2_hidden('#skF_2'('#skF_5', k2_relat_1('#skF_6')), k2_relat_1('#skF_6')) | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_16205, c_2])).
% 10.08/3.86  tff(c_16234, plain, (~r2_hidden('#skF_2'('#skF_5', k2_relat_1('#skF_6')), k2_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_156, c_16219])).
% 10.08/3.86  tff(c_16251, plain, (~r2_hidden('#skF_2'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_8775, c_16234])).
% 10.08/3.86  tff(c_16267, plain, (~r2_hidden('#skF_1'('#skF_5', k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_6, c_16251])).
% 10.08/3.86  tff(c_16282, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16205, c_16267])).
% 10.08/3.86  tff(c_16284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_16282])).
% 10.08/3.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/3.86  
% 10.08/3.86  Inference rules
% 10.08/3.86  ----------------------
% 10.08/3.86  #Ref     : 0
% 10.08/3.86  #Sup     : 3311
% 10.08/3.86  #Fact    : 0
% 10.08/3.86  #Define  : 0
% 10.08/3.86  #Split   : 27
% 10.08/3.86  #Chain   : 0
% 10.08/3.86  #Close   : 0
% 10.08/3.86  
% 10.08/3.86  Ordering : KBO
% 10.08/3.86  
% 10.08/3.86  Simplification rules
% 10.08/3.86  ----------------------
% 10.08/3.86  #Subsume      : 1197
% 10.08/3.86  #Demod        : 446
% 10.08/3.86  #Tautology    : 175
% 10.08/3.86  #SimpNegUnit  : 126
% 10.08/3.86  #BackRed      : 97
% 10.08/3.86  
% 10.08/3.86  #Partial instantiations: 0
% 10.08/3.86  #Strategies tried      : 1
% 10.08/3.86  
% 10.08/3.86  Timing (in seconds)
% 10.08/3.86  ----------------------
% 10.08/3.86  Preprocessing        : 0.38
% 10.08/3.86  Parsing              : 0.19
% 10.08/3.86  CNF conversion       : 0.03
% 10.08/3.86  Main loop            : 2.70
% 10.08/3.87  Inferencing          : 0.75
% 10.08/3.87  Reduction            : 0.56
% 10.08/3.87  Demodulation         : 0.33
% 10.08/3.87  BG Simplification    : 0.07
% 10.08/3.87  Subsumption          : 1.12
% 10.08/3.87  Abstraction          : 0.11
% 10.08/3.87  MUC search           : 0.00
% 10.08/3.87  Cooper               : 0.00
% 10.08/3.87  Total                : 3.13
% 10.08/3.87  Index Insertion      : 0.00
% 10.08/3.87  Index Deletion       : 0.00
% 10.08/3.87  Index Matching       : 0.00
% 10.08/3.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
