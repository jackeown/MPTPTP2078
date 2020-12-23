%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:20 EST 2020

% Result     : Theorem 9.87s
% Output     : CNFRefutation 9.87s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 240 expanded)
%              Number of leaves         :   54 ( 106 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 534 expanded)
%              Number of equality atoms :   53 ( 144 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_169,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_157,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_139,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_34,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_88,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_54,plain,(
    ! [A_49,B_50] : v1_relat_1(k2_zfmisc_1(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_96,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_171,plain,(
    ! [B_110,A_111] :
      ( v1_relat_1(B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_111))
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_174,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(resolution,[status(thm)],[c_96,c_171])).

tff(c_180,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_174])).

tff(c_5823,plain,(
    ! [C_604,B_605,A_606] :
      ( v5_relat_1(C_604,B_605)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(A_606,B_605))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5831,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_96,c_5823])).

tff(c_52,plain,(
    ! [B_48,A_47] :
      ( r1_tarski(k2_relat_1(B_48),A_47)
      | ~ v5_relat_1(B_48,A_47)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_100,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_94,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_98,plain,(
    v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_6064,plain,(
    ! [A_649,B_650,C_651] :
      ( k1_relset_1(A_649,B_650,C_651) = k1_relat_1(C_651)
      | ~ m1_subset_1(C_651,k1_zfmisc_1(k2_zfmisc_1(A_649,B_650))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6072,plain,(
    k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_96,c_6064])).

tff(c_7665,plain,(
    ! [B_796,A_797,C_798] :
      ( k1_xboole_0 = B_796
      | k1_relset_1(A_797,B_796,C_798) = A_797
      | ~ v1_funct_2(C_798,A_797,B_796)
      | ~ m1_subset_1(C_798,k1_zfmisc_1(k2_zfmisc_1(A_797,B_796))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_7668,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_tarski('#skF_7')
    | ~ v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_96,c_7665])).

tff(c_7675,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_tarski('#skF_7') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_6072,c_7668])).

tff(c_7676,plain,(
    k1_tarski('#skF_7') = k1_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_7675])).

tff(c_44,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_163,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(resolution,[status(thm)],[c_96,c_44])).

tff(c_78,plain,(
    ! [A_65] :
      ( r2_hidden('#skF_6'(A_65),A_65)
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_5813,plain,(
    ! [C_601,B_602,A_603] :
      ( r2_hidden(C_601,B_602)
      | ~ r2_hidden(C_601,A_603)
      | ~ r1_tarski(A_603,B_602) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5895,plain,(
    ! [A_618,B_619] :
      ( r2_hidden('#skF_6'(A_618),B_619)
      | ~ r1_tarski(A_618,B_619)
      | k1_xboole_0 = A_618 ) ),
    inference(resolution,[status(thm)],[c_78,c_5813])).

tff(c_74,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_mcart_1(A_62) = B_63
      | ~ r2_hidden(A_62,k2_zfmisc_1(k1_tarski(B_63),C_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6401,plain,(
    ! [A_693,B_694,C_695] :
      ( k1_mcart_1('#skF_6'(A_693)) = B_694
      | ~ r1_tarski(A_693,k2_zfmisc_1(k1_tarski(B_694),C_695))
      | k1_xboole_0 = A_693 ) ),
    inference(resolution,[status(thm)],[c_5895,c_74])).

tff(c_6415,plain,
    ( k1_mcart_1('#skF_6'('#skF_9')) = '#skF_7'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_163,c_6401])).

tff(c_6416,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_6415])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_129,plain,(
    ! [A_95,B_96] : k2_xboole_0(k1_tarski(A_95),B_96) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_133,plain,(
    ! [A_95] : k1_tarski(A_95) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_129])).

tff(c_6432,plain,(
    ! [A_95] : k1_tarski(A_95) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6416,c_133])).

tff(c_6437,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6416,c_94])).

tff(c_58,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6436,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6416,c_6416,c_58])).

tff(c_6459,plain,(
    k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6436,c_6072])).

tff(c_90,plain,(
    ! [B_88,A_87,C_89] :
      ( k1_xboole_0 = B_88
      | k1_relset_1(A_87,B_88,C_89) = A_87
      | ~ v1_funct_2(C_89,A_87,B_88)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_6878,plain,(
    ! [B_733,A_734,C_735] :
      ( B_733 = '#skF_9'
      | k1_relset_1(A_734,B_733,C_735) = A_734
      | ~ v1_funct_2(C_735,A_734,B_733)
      | ~ m1_subset_1(C_735,k1_zfmisc_1(k2_zfmisc_1(A_734,B_733))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6416,c_90])).

tff(c_6881,plain,
    ( '#skF_9' = '#skF_8'
    | k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_tarski('#skF_7')
    | ~ v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_96,c_6878])).

tff(c_6888,plain,
    ( '#skF_9' = '#skF_8'
    | k1_tarski('#skF_7') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_6459,c_6881])).

tff(c_6890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6432,c_6437,c_6888])).

tff(c_6892,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_6415])).

tff(c_6891,plain,(
    k1_mcart_1('#skF_6'('#skF_9')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6415])).

tff(c_70,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden(k1_mcart_1(A_59),B_60)
      | ~ r2_hidden(A_59,k2_zfmisc_1(B_60,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6943,plain,(
    ! [A_740,B_741,C_742] :
      ( r2_hidden(k1_mcart_1('#skF_6'(A_740)),B_741)
      | ~ r1_tarski(A_740,k2_zfmisc_1(B_741,C_742))
      | k1_xboole_0 = A_740 ) ),
    inference(resolution,[status(thm)],[c_5895,c_70])).

tff(c_6951,plain,
    ( r2_hidden(k1_mcart_1('#skF_6'('#skF_9')),k1_tarski('#skF_7'))
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_163,c_6943])).

tff(c_6955,plain,
    ( r2_hidden('#skF_7',k1_tarski('#skF_7'))
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6891,c_6951])).

tff(c_6956,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_6892,c_6955])).

tff(c_7684,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7676,c_6956])).

tff(c_6957,plain,(
    ! [B_743,A_744] :
      ( r2_hidden(k1_funct_1(B_743,A_744),k2_relat_1(B_743))
      | ~ r2_hidden(A_744,k1_relat_1(B_743))
      | ~ v1_funct_1(B_743)
      | ~ v1_relat_1(B_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_11413,plain,(
    ! [B_1072,A_1073,B_1074] :
      ( r2_hidden(k1_funct_1(B_1072,A_1073),B_1074)
      | ~ r1_tarski(k2_relat_1(B_1072),B_1074)
      | ~ r2_hidden(A_1073,k1_relat_1(B_1072))
      | ~ v1_funct_1(B_1072)
      | ~ v1_relat_1(B_1072) ) ),
    inference(resolution,[status(thm)],[c_6957,c_2])).

tff(c_92,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_11478,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_11413,c_92])).

tff(c_11501,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_100,c_7684,c_11478])).

tff(c_11504,plain,
    ( ~ v5_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_11501])).

tff(c_11508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_5831,c_11504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n013.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 13:00:09 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.87/3.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.87/3.45  
% 9.87/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.87/3.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 9.87/3.46  
% 9.87/3.46  %Foreground sorts:
% 9.87/3.46  
% 9.87/3.46  
% 9.87/3.46  %Background operators:
% 9.87/3.46  
% 9.87/3.46  
% 9.87/3.46  %Foreground operators:
% 9.87/3.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.87/3.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.87/3.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.87/3.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.87/3.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.87/3.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.87/3.46  tff('#skF_7', type, '#skF_7': $i).
% 9.87/3.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.87/3.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.87/3.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.87/3.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.87/3.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.87/3.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.87/3.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.87/3.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.87/3.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.87/3.46  tff('#skF_9', type, '#skF_9': $i).
% 9.87/3.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.87/3.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.87/3.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.87/3.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.87/3.46  tff('#skF_8', type, '#skF_8': $i).
% 9.87/3.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.87/3.46  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 9.87/3.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.87/3.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.87/3.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.87/3.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.87/3.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.87/3.46  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 9.87/3.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.87/3.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.87/3.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.87/3.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.87/3.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.87/3.46  tff('#skF_6', type, '#skF_6': $i > $i).
% 9.87/3.46  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.87/3.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.87/3.46  
% 9.87/3.47  tff(f_85, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.87/3.47  tff(f_169, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 9.87/3.47  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.87/3.47  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.87/3.47  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.87/3.47  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.87/3.47  tff(f_157, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.87/3.47  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.87/3.47  tff(f_139, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 9.87/3.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.87/3.47  tff(f_118, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 9.87/3.47  tff(f_34, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 9.87/3.47  tff(f_55, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 9.87/3.47  tff(f_88, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 9.87/3.47  tff(f_112, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 9.87/3.47  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 9.87/3.47  tff(c_54, plain, (![A_49, B_50]: (v1_relat_1(k2_zfmisc_1(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.87/3.47  tff(c_96, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 9.87/3.47  tff(c_171, plain, (![B_110, A_111]: (v1_relat_1(B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_111)) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.87/3.47  tff(c_174, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_96, c_171])).
% 9.87/3.47  tff(c_180, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_174])).
% 9.87/3.47  tff(c_5823, plain, (![C_604, B_605, A_606]: (v5_relat_1(C_604, B_605) | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(A_606, B_605))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.87/3.47  tff(c_5831, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_96, c_5823])).
% 9.87/3.47  tff(c_52, plain, (![B_48, A_47]: (r1_tarski(k2_relat_1(B_48), A_47) | ~v5_relat_1(B_48, A_47) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.87/3.47  tff(c_100, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_169])).
% 9.87/3.47  tff(c_94, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_169])).
% 9.87/3.47  tff(c_98, plain, (v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_169])).
% 9.87/3.47  tff(c_6064, plain, (![A_649, B_650, C_651]: (k1_relset_1(A_649, B_650, C_651)=k1_relat_1(C_651) | ~m1_subset_1(C_651, k1_zfmisc_1(k2_zfmisc_1(A_649, B_650))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.87/3.47  tff(c_6072, plain, (k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_96, c_6064])).
% 9.87/3.47  tff(c_7665, plain, (![B_796, A_797, C_798]: (k1_xboole_0=B_796 | k1_relset_1(A_797, B_796, C_798)=A_797 | ~v1_funct_2(C_798, A_797, B_796) | ~m1_subset_1(C_798, k1_zfmisc_1(k2_zfmisc_1(A_797, B_796))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.87/3.47  tff(c_7668, plain, (k1_xboole_0='#skF_8' | k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_tarski('#skF_7') | ~v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_96, c_7665])).
% 9.87/3.47  tff(c_7675, plain, (k1_xboole_0='#skF_8' | k1_tarski('#skF_7')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_6072, c_7668])).
% 9.87/3.47  tff(c_7676, plain, (k1_tarski('#skF_7')=k1_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_94, c_7675])).
% 9.87/3.47  tff(c_44, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.87/3.47  tff(c_163, plain, (r1_tarski('#skF_9', k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_96, c_44])).
% 9.87/3.47  tff(c_78, plain, (![A_65]: (r2_hidden('#skF_6'(A_65), A_65) | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.87/3.47  tff(c_5813, plain, (![C_601, B_602, A_603]: (r2_hidden(C_601, B_602) | ~r2_hidden(C_601, A_603) | ~r1_tarski(A_603, B_602))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.87/3.47  tff(c_5895, plain, (![A_618, B_619]: (r2_hidden('#skF_6'(A_618), B_619) | ~r1_tarski(A_618, B_619) | k1_xboole_0=A_618)), inference(resolution, [status(thm)], [c_78, c_5813])).
% 9.87/3.47  tff(c_74, plain, (![A_62, B_63, C_64]: (k1_mcart_1(A_62)=B_63 | ~r2_hidden(A_62, k2_zfmisc_1(k1_tarski(B_63), C_64)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.87/3.47  tff(c_6401, plain, (![A_693, B_694, C_695]: (k1_mcart_1('#skF_6'(A_693))=B_694 | ~r1_tarski(A_693, k2_zfmisc_1(k1_tarski(B_694), C_695)) | k1_xboole_0=A_693)), inference(resolution, [status(thm)], [c_5895, c_74])).
% 9.87/3.47  tff(c_6415, plain, (k1_mcart_1('#skF_6'('#skF_9'))='#skF_7' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_163, c_6401])).
% 9.87/3.47  tff(c_6416, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_6415])).
% 9.87/3.47  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.87/3.47  tff(c_129, plain, (![A_95, B_96]: (k2_xboole_0(k1_tarski(A_95), B_96)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.87/3.47  tff(c_133, plain, (![A_95]: (k1_tarski(A_95)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_129])).
% 9.87/3.47  tff(c_6432, plain, (![A_95]: (k1_tarski(A_95)!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6416, c_133])).
% 9.87/3.47  tff(c_6437, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6416, c_94])).
% 9.87/3.47  tff(c_58, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.87/3.47  tff(c_6436, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6416, c_6416, c_58])).
% 9.87/3.47  tff(c_6459, plain, (k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6436, c_6072])).
% 9.87/3.47  tff(c_90, plain, (![B_88, A_87, C_89]: (k1_xboole_0=B_88 | k1_relset_1(A_87, B_88, C_89)=A_87 | ~v1_funct_2(C_89, A_87, B_88) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.87/3.47  tff(c_6878, plain, (![B_733, A_734, C_735]: (B_733='#skF_9' | k1_relset_1(A_734, B_733, C_735)=A_734 | ~v1_funct_2(C_735, A_734, B_733) | ~m1_subset_1(C_735, k1_zfmisc_1(k2_zfmisc_1(A_734, B_733))))), inference(demodulation, [status(thm), theory('equality')], [c_6416, c_90])).
% 9.87/3.47  tff(c_6881, plain, ('#skF_9'='#skF_8' | k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_tarski('#skF_7') | ~v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_96, c_6878])).
% 9.87/3.47  tff(c_6888, plain, ('#skF_9'='#skF_8' | k1_tarski('#skF_7')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_6459, c_6881])).
% 9.87/3.47  tff(c_6890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6432, c_6437, c_6888])).
% 9.87/3.47  tff(c_6892, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_6415])).
% 9.87/3.47  tff(c_6891, plain, (k1_mcart_1('#skF_6'('#skF_9'))='#skF_7'), inference(splitRight, [status(thm)], [c_6415])).
% 9.87/3.47  tff(c_70, plain, (![A_59, B_60, C_61]: (r2_hidden(k1_mcart_1(A_59), B_60) | ~r2_hidden(A_59, k2_zfmisc_1(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.87/3.47  tff(c_6943, plain, (![A_740, B_741, C_742]: (r2_hidden(k1_mcart_1('#skF_6'(A_740)), B_741) | ~r1_tarski(A_740, k2_zfmisc_1(B_741, C_742)) | k1_xboole_0=A_740)), inference(resolution, [status(thm)], [c_5895, c_70])).
% 9.87/3.47  tff(c_6951, plain, (r2_hidden(k1_mcart_1('#skF_6'('#skF_9')), k1_tarski('#skF_7')) | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_163, c_6943])).
% 9.87/3.47  tff(c_6955, plain, (r2_hidden('#skF_7', k1_tarski('#skF_7')) | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6891, c_6951])).
% 9.87/3.47  tff(c_6956, plain, (r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_6892, c_6955])).
% 9.87/3.47  tff(c_7684, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_7676, c_6956])).
% 9.87/3.47  tff(c_6957, plain, (![B_743, A_744]: (r2_hidden(k1_funct_1(B_743, A_744), k2_relat_1(B_743)) | ~r2_hidden(A_744, k1_relat_1(B_743)) | ~v1_funct_1(B_743) | ~v1_relat_1(B_743))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.87/3.47  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.87/3.47  tff(c_11413, plain, (![B_1072, A_1073, B_1074]: (r2_hidden(k1_funct_1(B_1072, A_1073), B_1074) | ~r1_tarski(k2_relat_1(B_1072), B_1074) | ~r2_hidden(A_1073, k1_relat_1(B_1072)) | ~v1_funct_1(B_1072) | ~v1_relat_1(B_1072))), inference(resolution, [status(thm)], [c_6957, c_2])).
% 9.87/3.47  tff(c_92, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_169])).
% 9.87/3.47  tff(c_11478, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_11413, c_92])).
% 9.87/3.47  tff(c_11501, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_100, c_7684, c_11478])).
% 9.87/3.47  tff(c_11504, plain, (~v5_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_11501])).
% 9.87/3.47  tff(c_11508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_5831, c_11504])).
% 9.87/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.87/3.47  
% 9.87/3.47  Inference rules
% 9.87/3.47  ----------------------
% 9.87/3.47  #Ref     : 0
% 9.87/3.47  #Sup     : 2654
% 9.87/3.47  #Fact    : 0
% 9.87/3.47  #Define  : 0
% 9.87/3.47  #Split   : 76
% 9.87/3.47  #Chain   : 0
% 9.87/3.47  #Close   : 0
% 9.87/3.47  
% 9.87/3.47  Ordering : KBO
% 9.87/3.47  
% 9.87/3.47  Simplification rules
% 9.87/3.47  ----------------------
% 9.87/3.47  #Subsume      : 278
% 9.87/3.47  #Demod        : 439
% 9.87/3.47  #Tautology    : 265
% 9.87/3.47  #SimpNegUnit  : 69
% 9.87/3.47  #BackRed      : 83
% 9.87/3.47  
% 9.87/3.47  #Partial instantiations: 0
% 9.87/3.47  #Strategies tried      : 1
% 9.87/3.47  
% 9.87/3.47  Timing (in seconds)
% 9.87/3.47  ----------------------
% 9.87/3.47  Preprocessing        : 0.38
% 9.87/3.48  Parsing              : 0.20
% 9.87/3.48  CNF conversion       : 0.03
% 9.87/3.48  Main loop            : 2.36
% 9.87/3.48  Inferencing          : 0.68
% 9.87/3.48  Reduction            : 0.69
% 9.87/3.48  Demodulation         : 0.44
% 9.87/3.48  BG Simplification    : 0.08
% 9.87/3.48  Subsumption          : 0.69
% 9.87/3.48  Abstraction          : 0.09
% 9.87/3.48  MUC search           : 0.00
% 9.87/3.48  Cooper               : 0.00
% 9.87/3.48  Total                : 2.77
% 9.87/3.48  Index Insertion      : 0.00
% 9.87/3.48  Index Deletion       : 0.00
% 9.87/3.48  Index Matching       : 0.00
% 9.87/3.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
