%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:09 EST 2020

% Result     : Theorem 13.80s
% Output     : CNFRefutation 13.98s
% Verified   : 
% Statistics : Number of formulae       :  265 (3187 expanded)
%              Number of leaves         :   48 (1032 expanded)
%              Depth                    :   15
%              Number of atoms          :  477 (8483 expanded)
%              Number of equality atoms :  187 (2990 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_91,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_183,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_163,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

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

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_44,plain,(
    ! [A_28,B_29] : v1_relat_1(k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_92,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_27436,plain,(
    ! [B_1526,A_1527] :
      ( v1_relat_1(B_1526)
      | ~ m1_subset_1(B_1526,k1_zfmisc_1(A_1527))
      | ~ v1_relat_1(A_1527) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_27442,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_92,c_27436])).

tff(c_27446,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_27442])).

tff(c_28050,plain,(
    ! [C_1572,A_1573,B_1574] :
      ( v4_relat_1(C_1572,A_1573)
      | ~ m1_subset_1(C_1572,k1_zfmisc_1(k2_zfmisc_1(A_1573,B_1574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28065,plain,(
    v4_relat_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_28050])).

tff(c_40,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k1_relat_1(B_26),A_25)
      | ~ v4_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28273,plain,(
    ! [A_1597,B_1598,C_1599] :
      ( k2_relset_1(A_1597,B_1598,C_1599) = k2_relat_1(C_1599)
      | ~ m1_subset_1(C_1599,k1_zfmisc_1(k2_zfmisc_1(A_1597,B_1598))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_28288,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_28273])).

tff(c_90,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_28311,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28288,c_90])).

tff(c_28801,plain,(
    ! [C_1646,A_1647,B_1648] :
      ( m1_subset_1(C_1646,k1_zfmisc_1(k2_zfmisc_1(A_1647,B_1648)))
      | ~ r1_tarski(k2_relat_1(C_1646),B_1648)
      | ~ r1_tarski(k1_relat_1(C_1646),A_1647)
      | ~ v1_relat_1(C_1646) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_20,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_154,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_94,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1531,plain,(
    ! [A_178,B_179,C_180] :
      ( k1_relset_1(A_178,B_179,C_180) = k1_relat_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1546,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_1531])).

tff(c_2066,plain,(
    ! [B_221,A_222,C_223] :
      ( k1_xboole_0 = B_221
      | k1_relset_1(A_222,B_221,C_223) = A_222
      | ~ v1_funct_2(C_223,A_222,B_221)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_222,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2076,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_2066])).

tff(c_2087,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1546,c_2076])).

tff(c_2088,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_2087])).

tff(c_704,plain,(
    ! [B_100,A_101] :
      ( v1_relat_1(B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_101))
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_710,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_92,c_704])).

tff(c_714,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_710])).

tff(c_1283,plain,(
    ! [A_160,B_161,C_162] :
      ( k2_relset_1(A_160,B_161,C_162) = k2_relat_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1298,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_1283])).

tff(c_1300,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1298,c_90])).

tff(c_1906,plain,(
    ! [C_202,A_203,B_204] :
      ( m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204)))
      | ~ r1_tarski(k2_relat_1(C_202),B_204)
      | ~ r1_tarski(k1_relat_1(C_202),A_203)
      | ~ v1_relat_1(C_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8175,plain,(
    ! [C_510,A_511,B_512] :
      ( r1_tarski(C_510,k2_zfmisc_1(A_511,B_512))
      | ~ r1_tarski(k2_relat_1(C_510),B_512)
      | ~ r1_tarski(k1_relat_1(C_510),A_511)
      | ~ v1_relat_1(C_510) ) ),
    inference(resolution,[status(thm)],[c_1906,c_30])).

tff(c_8189,plain,(
    ! [A_511] :
      ( r1_tarski('#skF_7',k2_zfmisc_1(A_511,'#skF_6'))
      | ~ r1_tarski(k1_relat_1('#skF_7'),A_511)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1300,c_8175])).

tff(c_8213,plain,(
    ! [A_513] :
      ( r1_tarski('#skF_7',k2_zfmisc_1(A_513,'#skF_6'))
      | ~ r1_tarski('#skF_4',A_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_2088,c_8189])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1545,plain,(
    ! [A_178,B_179,A_17] :
      ( k1_relset_1(A_178,B_179,A_17) = k1_relat_1(A_17)
      | ~ r1_tarski(A_17,k2_zfmisc_1(A_178,B_179)) ) ),
    inference(resolution,[status(thm)],[c_32,c_1531])).

tff(c_8225,plain,(
    ! [A_513] :
      ( k1_relset_1(A_513,'#skF_6','#skF_7') = k1_relat_1('#skF_7')
      | ~ r1_tarski('#skF_4',A_513) ) ),
    inference(resolution,[status(thm)],[c_8213,c_1545])).

tff(c_8359,plain,(
    ! [A_516] :
      ( k1_relset_1(A_516,'#skF_6','#skF_7') = '#skF_4'
      | ~ r1_tarski('#skF_4',A_516) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2088,c_8225])).

tff(c_8379,plain,(
    k1_relset_1('#skF_4','#skF_6','#skF_7') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_8359])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [A_32] : k1_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_56,plain,(
    ! [A_33] : v1_relat_1(k6_relat_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_235,plain,(
    ! [A_74] :
      ( k1_relat_1(A_74) != k1_xboole_0
      | k1_xboole_0 = A_74
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_244,plain,(
    ! [A_33] :
      ( k1_relat_1(k6_relat_1(A_33)) != k1_xboole_0
      | k6_relat_1(A_33) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_235])).

tff(c_253,plain,(
    ! [A_75] :
      ( k1_xboole_0 != A_75
      | k6_relat_1(A_75) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_244])).

tff(c_155,plain,(
    ! [A_62] :
      ( v1_xboole_0(k1_relat_1(A_62))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_158,plain,(
    ! [A_32] :
      ( v1_xboole_0(A_32)
      | ~ v1_xboole_0(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_155])).

tff(c_262,plain,(
    ! [A_75] :
      ( v1_xboole_0(A_75)
      | ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 != A_75 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_158])).

tff(c_280,plain,(
    ! [A_75] :
      ( v1_xboole_0(A_75)
      | k1_xboole_0 != A_75 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_262])).

tff(c_762,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_2'(A_106,B_107),A_106)
      | r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_773,plain,(
    ! [A_108,B_109] :
      ( ~ v1_xboole_0(A_108)
      | r1_tarski(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_762,c_2])).

tff(c_620,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_630,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_relset_1('#skF_4','#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_90,c_620])).

tff(c_702,plain,(
    ~ r1_tarski('#skF_6',k2_relset_1('#skF_4','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_630])).

tff(c_791,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_773,c_702])).

tff(c_805,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_280,c_791])).

tff(c_68,plain,(
    ! [C_45,A_43,B_44] :
      ( m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ r1_tarski(k2_relat_1(C_45),B_44)
      | ~ r1_tarski(k1_relat_1(C_45),A_43)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2154,plain,(
    ! [B_224,C_225,A_226] :
      ( k1_xboole_0 = B_224
      | v1_funct_2(C_225,A_226,B_224)
      | k1_relset_1(A_226,B_224,C_225) != A_226
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_226,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_11283,plain,(
    ! [B_617,C_618,A_619] :
      ( k1_xboole_0 = B_617
      | v1_funct_2(C_618,A_619,B_617)
      | k1_relset_1(A_619,B_617,C_618) != A_619
      | ~ r1_tarski(k2_relat_1(C_618),B_617)
      | ~ r1_tarski(k1_relat_1(C_618),A_619)
      | ~ v1_relat_1(C_618) ) ),
    inference(resolution,[status(thm)],[c_68,c_2154])).

tff(c_11297,plain,(
    ! [A_619] :
      ( k1_xboole_0 = '#skF_6'
      | v1_funct_2('#skF_7',A_619,'#skF_6')
      | k1_relset_1(A_619,'#skF_6','#skF_7') != A_619
      | ~ r1_tarski(k1_relat_1('#skF_7'),A_619)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1300,c_11283])).

tff(c_11316,plain,(
    ! [A_619] :
      ( k1_xboole_0 = '#skF_6'
      | v1_funct_2('#skF_7',A_619,'#skF_6')
      | k1_relset_1(A_619,'#skF_6','#skF_7') != A_619
      | ~ r1_tarski('#skF_4',A_619) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_2088,c_11297])).

tff(c_11322,plain,(
    ! [A_620] :
      ( v1_funct_2('#skF_7',A_620,'#skF_6')
      | k1_relset_1(A_620,'#skF_6','#skF_7') != A_620
      | ~ r1_tarski('#skF_4',A_620) ) ),
    inference(negUnitSimplification,[status(thm)],[c_805,c_11316])).

tff(c_96,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_86,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_98,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_86])).

tff(c_234,plain,(
    ~ v1_funct_2('#skF_7','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_11325,plain,
    ( k1_relset_1('#skF_4','#skF_6','#skF_7') != '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_11322,c_234])).

tff(c_11329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8379,c_11325])).

tff(c_11330,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_630])).

tff(c_11911,plain,(
    ! [A_682,B_683,C_684] :
      ( k2_relset_1(A_682,B_683,C_684) = k2_relat_1(C_684)
      | ~ m1_subset_1(C_684,k1_zfmisc_1(k2_zfmisc_1(A_682,B_683))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_11918,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_11911])).

tff(c_11927,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11330,c_11918])).

tff(c_11339,plain,(
    ! [B_621,A_622] :
      ( v1_relat_1(B_621)
      | ~ m1_subset_1(B_621,k1_zfmisc_1(A_622))
      | ~ v1_relat_1(A_622) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_11345,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_92,c_11339])).

tff(c_11349,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_11345])).

tff(c_48,plain,(
    ! [A_31] :
      ( k2_relat_1(A_31) != k1_xboole_0
      | k1_xboole_0 = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_11356,plain,
    ( k2_relat_1('#skF_7') != k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_11349,c_48])).

tff(c_11358,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_11356])).

tff(c_11928,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11927,c_11358])).

tff(c_12012,plain,(
    ! [A_696,B_697,C_698] :
      ( k1_relset_1(A_696,B_697,C_698) = k1_relat_1(C_698)
      | ~ m1_subset_1(C_698,k1_zfmisc_1(k2_zfmisc_1(A_696,B_697))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12027,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_12012])).

tff(c_12563,plain,(
    ! [B_748,A_749,C_750] :
      ( k1_xboole_0 = B_748
      | k1_relset_1(A_749,B_748,C_750) = A_749
      | ~ v1_funct_2(C_750,A_749,B_748)
      | ~ m1_subset_1(C_750,k1_zfmisc_1(k2_zfmisc_1(A_749,B_748))) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_12573,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_12563])).

tff(c_12584,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_12027,c_12573])).

tff(c_12585,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_12584])).

tff(c_12414,plain,(
    ! [C_734,A_735,B_736] :
      ( m1_subset_1(C_734,k1_zfmisc_1(k2_zfmisc_1(A_735,B_736)))
      | ~ r1_tarski(k2_relat_1(C_734),B_736)
      | ~ r1_tarski(k1_relat_1(C_734),A_735)
      | ~ v1_relat_1(C_734) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_64,plain,(
    ! [A_37,B_38,C_39] :
      ( k1_relset_1(A_37,B_38,C_39) = k1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_20825,plain,(
    ! [A_1108,B_1109,C_1110] :
      ( k1_relset_1(A_1108,B_1109,C_1110) = k1_relat_1(C_1110)
      | ~ r1_tarski(k2_relat_1(C_1110),B_1109)
      | ~ r1_tarski(k1_relat_1(C_1110),A_1108)
      | ~ v1_relat_1(C_1110) ) ),
    inference(resolution,[status(thm)],[c_12414,c_64])).

tff(c_20839,plain,(
    ! [A_1108,B_1109] :
      ( k1_relset_1(A_1108,B_1109,'#skF_7') = k1_relat_1('#skF_7')
      | ~ r1_tarski('#skF_6',B_1109)
      | ~ r1_tarski(k1_relat_1('#skF_7'),A_1108)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11927,c_20825])).

tff(c_21154,plain,(
    ! [A_1117,B_1118] :
      ( k1_relset_1(A_1117,B_1118,'#skF_7') = '#skF_4'
      | ~ r1_tarski('#skF_6',B_1118)
      | ~ r1_tarski('#skF_4',A_1117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11349,c_12585,c_12585,c_20839])).

tff(c_21171,plain,(
    ! [A_1119] :
      ( k1_relset_1(A_1119,'#skF_6','#skF_7') = '#skF_4'
      | ~ r1_tarski('#skF_4',A_1119) ) ),
    inference(resolution,[status(thm)],[c_20,c_21154])).

tff(c_21191,plain,(
    k1_relset_1('#skF_4','#skF_6','#skF_7') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_21171])).

tff(c_12520,plain,(
    ! [B_743,C_744,A_745] :
      ( k1_xboole_0 = B_743
      | v1_funct_2(C_744,A_745,B_743)
      | k1_relset_1(A_745,B_743,C_744) != A_745
      | ~ m1_subset_1(C_744,k1_zfmisc_1(k2_zfmisc_1(A_745,B_743))) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_22269,plain,(
    ! [B_1164,C_1165,A_1166] :
      ( k1_xboole_0 = B_1164
      | v1_funct_2(C_1165,A_1166,B_1164)
      | k1_relset_1(A_1166,B_1164,C_1165) != A_1166
      | ~ r1_tarski(k2_relat_1(C_1165),B_1164)
      | ~ r1_tarski(k1_relat_1(C_1165),A_1166)
      | ~ v1_relat_1(C_1165) ) ),
    inference(resolution,[status(thm)],[c_68,c_12520])).

tff(c_22283,plain,(
    ! [B_1164,A_1166] :
      ( k1_xboole_0 = B_1164
      | v1_funct_2('#skF_7',A_1166,B_1164)
      | k1_relset_1(A_1166,B_1164,'#skF_7') != A_1166
      | ~ r1_tarski('#skF_6',B_1164)
      | ~ r1_tarski(k1_relat_1('#skF_7'),A_1166)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11927,c_22269])).

tff(c_22944,plain,(
    ! [B_1169,A_1170] :
      ( k1_xboole_0 = B_1169
      | v1_funct_2('#skF_7',A_1170,B_1169)
      | k1_relset_1(A_1170,B_1169,'#skF_7') != A_1170
      | ~ r1_tarski('#skF_6',B_1169)
      | ~ r1_tarski('#skF_4',A_1170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11349,c_12585,c_22283])).

tff(c_22950,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_4','#skF_6','#skF_7') != '#skF_4'
    | ~ r1_tarski('#skF_6','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_22944,c_234])).

tff(c_22955,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_21191,c_22950])).

tff(c_22957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11928,c_22955])).

tff(c_22958,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_11356])).

tff(c_22982,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22958,c_154])).

tff(c_22959,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_11356])).

tff(c_22993,plain,(
    k2_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22958,c_22959])).

tff(c_23576,plain,(
    ! [A_1217,B_1218,C_1219] :
      ( k2_relset_1(A_1217,B_1218,C_1219) = k2_relat_1(C_1219)
      | ~ m1_subset_1(C_1219,k1_zfmisc_1(k2_zfmisc_1(A_1217,B_1218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_23589,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_23576])).

tff(c_23592,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22993,c_11330,c_23589])).

tff(c_23621,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23592,c_22958])).

tff(c_26,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ! [A_49] :
      ( v1_funct_2(k1_xboole_0,A_49,k1_xboole_0)
      | k1_xboole_0 = A_49
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_49,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_102,plain,(
    ! [A_49] :
      ( v1_funct_2(k1_xboole_0,A_49,k1_xboole_0)
      | k1_xboole_0 = A_49
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_74])).

tff(c_23636,plain,(
    ! [A_49] :
      ( v1_funct_2('#skF_6',A_49,'#skF_6')
      | A_49 = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23621,c_23621,c_23621,c_23621,c_23621,c_102])).

tff(c_23637,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_23636])).

tff(c_23653,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_23637])).

tff(c_23657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_23653])).

tff(c_24019,plain,(
    ! [A_1248] :
      ( v1_funct_2('#skF_6',A_1248,'#skF_6')
      | A_1248 = '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_23636])).

tff(c_23624,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23592,c_234])).

tff(c_24032,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24019,c_23624])).

tff(c_22974,plain,(
    ! [A_75] :
      ( v1_xboole_0(A_75)
      | A_75 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22958,c_280])).

tff(c_23617,plain,(
    ! [A_75] :
      ( v1_xboole_0(A_75)
      | A_75 != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23592,c_22974])).

tff(c_24183,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24032,c_23617])).

tff(c_28,plain,(
    ! [B_16] : k2_zfmisc_1(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22983,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_7',B_16) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22958,c_22958,c_28])).

tff(c_23615,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_6',B_16) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23592,c_23592,c_22983])).

tff(c_24060,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_4',B_16) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24032,c_24032,c_23615])).

tff(c_23108,plain,(
    ! [A_1180,B_1181] :
      ( r2_hidden('#skF_2'(A_1180,B_1181),A_1180)
      | r1_tarski(A_1180,B_1181) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_23119,plain,(
    ! [A_1182,B_1183] :
      ( ~ v1_xboole_0(A_1182)
      | r1_tarski(A_1182,B_1183) ) ),
    inference(resolution,[status(thm)],[c_23108,c_2])).

tff(c_199,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_203,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_92,c_199])).

tff(c_629,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_203,c_620])).

tff(c_23060,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_629])).

tff(c_23125,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_23119,c_23060])).

tff(c_24145,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24060,c_23125])).

tff(c_24186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24183,c_24145])).

tff(c_24187,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_629])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k1_xboole_0 = B_16
      | k1_xboole_0 = A_15
      | k2_zfmisc_1(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24302,plain,(
    ! [B_1263,A_1264] :
      ( B_1263 = '#skF_7'
      | A_1264 = '#skF_7'
      | k2_zfmisc_1(A_1264,B_1263) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22958,c_22958,c_22958,c_24])).

tff(c_24305,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_24187,c_24302])).

tff(c_24314,plain,(
    '#skF_7' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_22982,c_24305])).

tff(c_24329,plain,(
    ! [A_75] :
      ( v1_xboole_0(A_75)
      | A_75 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24314,c_22974])).

tff(c_42,plain,(
    ! [A_27] :
      ( v1_xboole_0(k1_relat_1(A_27))
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24189,plain,(
    ! [A_1255,B_1256] :
      ( r2_hidden('#skF_2'(A_1255,B_1256),A_1255)
      | r1_tarski(A_1255,B_1256) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24199,plain,(
    ! [A_1255,B_1256] :
      ( ~ v1_xboole_0(A_1255)
      | r1_tarski(A_1255,B_1256) ) ),
    inference(resolution,[status(thm)],[c_24189,c_2])).

tff(c_24219,plain,(
    ! [A_1257,B_1258] :
      ( ~ v1_xboole_0(A_1257)
      | r1_tarski(A_1257,B_1258) ) ),
    inference(resolution,[status(thm)],[c_24189,c_2])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_25286,plain,(
    ! [B_1347,A_1348] :
      ( B_1347 = A_1348
      | ~ r1_tarski(B_1347,A_1348)
      | ~ v1_xboole_0(A_1348) ) ),
    inference(resolution,[status(thm)],[c_24219,c_16])).

tff(c_25304,plain,(
    ! [B_1349,A_1350] :
      ( B_1349 = A_1350
      | ~ v1_xboole_0(B_1349)
      | ~ v1_xboole_0(A_1350) ) ),
    inference(resolution,[status(thm)],[c_24199,c_25286])).

tff(c_25469,plain,(
    ! [A_1363,A_1364] :
      ( k1_relat_1(A_1363) = A_1364
      | ~ v1_xboole_0(A_1364)
      | ~ v1_xboole_0(A_1363) ) ),
    inference(resolution,[status(thm)],[c_42,c_25304])).

tff(c_26088,plain,(
    ! [A_1438,A_1439] :
      ( k1_relat_1(A_1438) = A_1439
      | ~ v1_xboole_0(A_1438)
      | A_1439 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_24329,c_25469])).

tff(c_26252,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24329,c_26088])).

tff(c_24744,plain,(
    ! [A_1303,B_1304,C_1305] :
      ( k1_relset_1(A_1303,B_1304,C_1305) = k1_relat_1(C_1305)
      | ~ m1_subset_1(C_1305,k1_zfmisc_1(k2_zfmisc_1(A_1303,B_1304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_26803,plain,(
    ! [A_1482,B_1483,A_1484] :
      ( k1_relset_1(A_1482,B_1483,A_1484) = k1_relat_1(A_1484)
      | ~ r1_tarski(A_1484,k2_zfmisc_1(A_1482,B_1483)) ) ),
    inference(resolution,[status(thm)],[c_32,c_24744])).

tff(c_26933,plain,(
    ! [A_1488,B_1489,A_1490] :
      ( k1_relset_1(A_1488,B_1489,A_1490) = k1_relat_1(A_1490)
      | ~ v1_xboole_0(A_1490) ) ),
    inference(resolution,[status(thm)],[c_24199,c_26803])).

tff(c_27209,plain,(
    ! [A_1488,B_1489] : k1_relset_1(A_1488,B_1489,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24329,c_26933])).

tff(c_24331,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24314,c_24314,c_22993])).

tff(c_24648,plain,(
    ! [A_1294,B_1295,C_1296] :
      ( k2_relset_1(A_1294,B_1295,C_1296) = k2_relat_1(C_1296)
      | ~ m1_subset_1(C_1296,k1_zfmisc_1(k2_zfmisc_1(A_1294,B_1295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_26634,plain,(
    ! [A_1472,B_1473,A_1474] :
      ( k2_relset_1(A_1472,B_1473,A_1474) = k2_relat_1(A_1474)
      | ~ r1_tarski(A_1474,k2_zfmisc_1(A_1472,B_1473)) ) ),
    inference(resolution,[status(thm)],[c_32,c_24648])).

tff(c_26954,plain,(
    ! [A_1491,B_1492,A_1493] :
      ( k2_relset_1(A_1491,B_1492,A_1493) = k2_relat_1(A_1493)
      | ~ v1_xboole_0(A_1493) ) ),
    inference(resolution,[status(thm)],[c_24199,c_26634])).

tff(c_27090,plain,(
    ! [A_1503,B_1504,A_1505] :
      ( k2_relset_1(A_1503,B_1504,A_1505) = k2_relat_1(A_1505)
      | A_1505 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_24329,c_26954])).

tff(c_24335,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24314,c_11330])).

tff(c_27100,plain,(
    k2_relat_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_27090,c_24335])).

tff(c_27113,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24331,c_27100])).

tff(c_24200,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24187,c_92])).

tff(c_24324,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24314,c_24314,c_24200])).

tff(c_24333,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24314,c_22958])).

tff(c_78,plain,(
    ! [C_51,B_50] :
      ( v1_funct_2(C_51,k1_xboole_0,B_50)
      | k1_relset_1(k1_xboole_0,B_50,C_51) != k1_xboole_0
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_99,plain,(
    ! [C_51,B_50] :
      ( v1_funct_2(C_51,k1_xboole_0,B_50)
      | k1_relset_1(k1_xboole_0,B_50,C_51) != k1_xboole_0
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_78])).

tff(c_24992,plain,(
    ! [C_1318,B_1319] :
      ( v1_funct_2(C_1318,'#skF_4',B_1319)
      | k1_relset_1('#skF_4',B_1319,C_1318) != '#skF_4'
      | ~ m1_subset_1(C_1318,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24333,c_24333,c_24333,c_24333,c_99])).

tff(c_25001,plain,(
    ! [B_1320] :
      ( v1_funct_2('#skF_4','#skF_4',B_1320)
      | k1_relset_1('#skF_4',B_1320,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_24324,c_24992])).

tff(c_24336,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24314,c_234])).

tff(c_25012,plain,(
    k1_relset_1('#skF_4','#skF_6','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_25001,c_24336])).

tff(c_27118,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27113,c_25012])).

tff(c_27210,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27209,c_27118])).

tff(c_27214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26252,c_27210])).

tff(c_27215,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_28826,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28801,c_27215])).

tff(c_28848,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27446,c_28311,c_28826])).

tff(c_28861,plain,
    ( ~ v4_relat_1('#skF_7','#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_28848])).

tff(c_28874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27446,c_28065,c_28861])).

tff(c_28875,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_28881,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28875,c_12])).

tff(c_50,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) != k1_xboole_0
      | k1_xboole_0 = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_29007,plain,(
    ! [A_1664] :
      ( k1_relat_1(A_1664) != '#skF_4'
      | A_1664 = '#skF_4'
      | ~ v1_relat_1(A_1664) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28875,c_28875,c_50])).

tff(c_29016,plain,(
    ! [A_33] :
      ( k1_relat_1(k6_relat_1(A_33)) != '#skF_4'
      | k6_relat_1(A_33) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_56,c_29007])).

tff(c_29025,plain,(
    ! [A_1665] :
      ( A_1665 != '#skF_4'
      | k6_relat_1(A_1665) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_29016])).

tff(c_28923,plain,(
    ! [A_1652] :
      ( v1_xboole_0(k1_relat_1(A_1652))
      | ~ v1_xboole_0(A_1652) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28926,plain,(
    ! [A_32] :
      ( v1_xboole_0(A_32)
      | ~ v1_xboole_0(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_28923])).

tff(c_29034,plain,(
    ! [A_1665] :
      ( v1_xboole_0(A_1665)
      | ~ v1_xboole_0('#skF_4')
      | A_1665 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29025,c_28926])).

tff(c_29058,plain,(
    ! [A_1666] :
      ( v1_xboole_0(A_1666)
      | A_1666 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28881,c_29034])).

tff(c_14,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28936,plain,(
    ! [A_1657] :
      ( r2_hidden('#skF_3'(A_1657),A_1657)
      | A_1657 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28875,c_14])).

tff(c_28941,plain,(
    ! [A_1658] :
      ( ~ v1_xboole_0(A_1658)
      | A_1658 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_28936,c_2])).

tff(c_28948,plain,(
    ! [A_27] :
      ( k1_relat_1(A_27) = '#skF_4'
      | ~ v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_42,c_28941])).

tff(c_29148,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_29058,c_28948])).

tff(c_22,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28880,plain,(
    ! [A_14] : r1_tarski('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28875,c_22])).

tff(c_28877,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_4',B_16) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28875,c_28875,c_28])).

tff(c_28876,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_28886,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28875,c_28876])).

tff(c_28892,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28886,c_92])).

tff(c_28894,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28877,c_28892])).

tff(c_28960,plain,(
    ! [A_1660,B_1661] :
      ( r1_tarski(A_1660,B_1661)
      | ~ m1_subset_1(A_1660,k1_zfmisc_1(B_1661)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28964,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_28894,c_28960])).

tff(c_29461,plain,(
    ! [B_1686,A_1687] :
      ( B_1686 = A_1687
      | ~ r1_tarski(B_1686,A_1687)
      | ~ r1_tarski(A_1687,B_1686) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_29463,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_28964,c_29461])).

tff(c_29472,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28880,c_29463])).

tff(c_29483,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29472,c_28894])).

tff(c_30335,plain,(
    ! [A_1779,B_1780,C_1781] :
      ( k1_relset_1(A_1779,B_1780,C_1781) = k1_relat_1(C_1781)
      | ~ m1_subset_1(C_1781,k1_zfmisc_1(k2_zfmisc_1(A_1779,B_1780))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32172,plain,(
    ! [B_1910,C_1911] :
      ( k1_relset_1('#skF_4',B_1910,C_1911) = k1_relat_1(C_1911)
      | ~ m1_subset_1(C_1911,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28877,c_30335])).

tff(c_32174,plain,(
    ! [B_1910] : k1_relset_1('#skF_4',B_1910,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_29483,c_32172])).

tff(c_32179,plain,(
    ! [B_1910] : k1_relset_1('#skF_4',B_1910,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29148,c_32174])).

tff(c_30415,plain,(
    ! [C_1795,B_1796] :
      ( v1_funct_2(C_1795,'#skF_4',B_1796)
      | k1_relset_1('#skF_4',B_1796,C_1795) != '#skF_4'
      | ~ m1_subset_1(C_1795,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28875,c_28875,c_28875,c_28875,c_99])).

tff(c_30443,plain,(
    ! [B_1799] :
      ( v1_funct_2('#skF_4','#skF_4',B_1799)
      | k1_relset_1('#skF_4',B_1799,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_29483,c_30415])).

tff(c_29004,plain,(
    ~ v1_funct_2('#skF_7','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28894,c_28877,c_98])).

tff(c_29480,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29472,c_29004])).

tff(c_30459,plain,(
    k1_relset_1('#skF_4','#skF_6','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_30443,c_29480])).

tff(c_32186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32179,c_30459])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:31:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.80/5.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.80/5.38  
% 13.80/5.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.98/5.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 13.98/5.39  
% 13.98/5.39  %Foreground sorts:
% 13.98/5.39  
% 13.98/5.39  
% 13.98/5.39  %Background operators:
% 13.98/5.39  
% 13.98/5.39  
% 13.98/5.39  %Foreground operators:
% 13.98/5.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.98/5.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.98/5.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.98/5.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.98/5.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.98/5.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.98/5.39  tff('#skF_7', type, '#skF_7': $i).
% 13.98/5.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.98/5.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.98/5.39  tff('#skF_5', type, '#skF_5': $i).
% 13.98/5.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.98/5.39  tff('#skF_6', type, '#skF_6': $i).
% 13.98/5.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.98/5.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.98/5.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.98/5.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.98/5.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.98/5.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.98/5.39  tff('#skF_4', type, '#skF_4': $i).
% 13.98/5.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 13.98/5.39  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.98/5.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.98/5.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.98/5.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.98/5.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.98/5.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.98/5.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.98/5.39  
% 13.98/5.42  tff(f_91, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.98/5.42  tff(f_183, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 13.98/5.42  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.98/5.42  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.98/5.42  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 13.98/5.42  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.98/5.42  tff(f_137, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 13.98/5.42  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.98/5.42  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.98/5.42  tff(f_163, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.98/5.42  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.98/5.42  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.98/5.42  tff(f_111, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 13.98/5.42  tff(f_115, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 13.98/5.42  tff(f_107, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 13.98/5.42  tff(f_89, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 13.98/5.42  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.98/5.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.98/5.42  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.98/5.42  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 13.98/5.42  tff(f_55, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.98/5.42  tff(c_44, plain, (![A_28, B_29]: (v1_relat_1(k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.98/5.42  tff(c_92, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 13.98/5.42  tff(c_27436, plain, (![B_1526, A_1527]: (v1_relat_1(B_1526) | ~m1_subset_1(B_1526, k1_zfmisc_1(A_1527)) | ~v1_relat_1(A_1527))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.98/5.42  tff(c_27442, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_92, c_27436])).
% 13.98/5.42  tff(c_27446, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_27442])).
% 13.98/5.42  tff(c_28050, plain, (![C_1572, A_1573, B_1574]: (v4_relat_1(C_1572, A_1573) | ~m1_subset_1(C_1572, k1_zfmisc_1(k2_zfmisc_1(A_1573, B_1574))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 13.98/5.42  tff(c_28065, plain, (v4_relat_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_92, c_28050])).
% 13.98/5.42  tff(c_40, plain, (![B_26, A_25]: (r1_tarski(k1_relat_1(B_26), A_25) | ~v4_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.98/5.42  tff(c_28273, plain, (![A_1597, B_1598, C_1599]: (k2_relset_1(A_1597, B_1598, C_1599)=k2_relat_1(C_1599) | ~m1_subset_1(C_1599, k1_zfmisc_1(k2_zfmisc_1(A_1597, B_1598))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.98/5.42  tff(c_28288, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_92, c_28273])).
% 13.98/5.42  tff(c_90, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_183])).
% 13.98/5.42  tff(c_28311, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28288, c_90])).
% 13.98/5.42  tff(c_28801, plain, (![C_1646, A_1647, B_1648]: (m1_subset_1(C_1646, k1_zfmisc_1(k2_zfmisc_1(A_1647, B_1648))) | ~r1_tarski(k2_relat_1(C_1646), B_1648) | ~r1_tarski(k1_relat_1(C_1646), A_1647) | ~v1_relat_1(C_1646))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.98/5.42  tff(c_20, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.98/5.42  tff(c_88, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_183])).
% 13.98/5.42  tff(c_154, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_88])).
% 13.98/5.42  tff(c_94, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_183])).
% 13.98/5.42  tff(c_1531, plain, (![A_178, B_179, C_180]: (k1_relset_1(A_178, B_179, C_180)=k1_relat_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.98/5.42  tff(c_1546, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_92, c_1531])).
% 13.98/5.42  tff(c_2066, plain, (![B_221, A_222, C_223]: (k1_xboole_0=B_221 | k1_relset_1(A_222, B_221, C_223)=A_222 | ~v1_funct_2(C_223, A_222, B_221) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_222, B_221))))), inference(cnfTransformation, [status(thm)], [f_163])).
% 13.98/5.42  tff(c_2076, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_92, c_2066])).
% 13.98/5.42  tff(c_2087, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1546, c_2076])).
% 13.98/5.42  tff(c_2088, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_154, c_2087])).
% 13.98/5.42  tff(c_704, plain, (![B_100, A_101]: (v1_relat_1(B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_101)) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.98/5.42  tff(c_710, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_92, c_704])).
% 13.98/5.42  tff(c_714, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_710])).
% 13.98/5.42  tff(c_1283, plain, (![A_160, B_161, C_162]: (k2_relset_1(A_160, B_161, C_162)=k2_relat_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.98/5.42  tff(c_1298, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_92, c_1283])).
% 13.98/5.42  tff(c_1300, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1298, c_90])).
% 13.98/5.42  tff(c_1906, plain, (![C_202, A_203, B_204]: (m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))) | ~r1_tarski(k2_relat_1(C_202), B_204) | ~r1_tarski(k1_relat_1(C_202), A_203) | ~v1_relat_1(C_202))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.98/5.42  tff(c_30, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.98/5.42  tff(c_8175, plain, (![C_510, A_511, B_512]: (r1_tarski(C_510, k2_zfmisc_1(A_511, B_512)) | ~r1_tarski(k2_relat_1(C_510), B_512) | ~r1_tarski(k1_relat_1(C_510), A_511) | ~v1_relat_1(C_510))), inference(resolution, [status(thm)], [c_1906, c_30])).
% 13.98/5.42  tff(c_8189, plain, (![A_511]: (r1_tarski('#skF_7', k2_zfmisc_1(A_511, '#skF_6')) | ~r1_tarski(k1_relat_1('#skF_7'), A_511) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1300, c_8175])).
% 13.98/5.42  tff(c_8213, plain, (![A_513]: (r1_tarski('#skF_7', k2_zfmisc_1(A_513, '#skF_6')) | ~r1_tarski('#skF_4', A_513))), inference(demodulation, [status(thm), theory('equality')], [c_714, c_2088, c_8189])).
% 13.98/5.42  tff(c_32, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.98/5.42  tff(c_1545, plain, (![A_178, B_179, A_17]: (k1_relset_1(A_178, B_179, A_17)=k1_relat_1(A_17) | ~r1_tarski(A_17, k2_zfmisc_1(A_178, B_179)))), inference(resolution, [status(thm)], [c_32, c_1531])).
% 13.98/5.42  tff(c_8225, plain, (![A_513]: (k1_relset_1(A_513, '#skF_6', '#skF_7')=k1_relat_1('#skF_7') | ~r1_tarski('#skF_4', A_513))), inference(resolution, [status(thm)], [c_8213, c_1545])).
% 13.98/5.42  tff(c_8359, plain, (![A_516]: (k1_relset_1(A_516, '#skF_6', '#skF_7')='#skF_4' | ~r1_tarski('#skF_4', A_516))), inference(demodulation, [status(thm), theory('equality')], [c_2088, c_8225])).
% 13.98/5.42  tff(c_8379, plain, (k1_relset_1('#skF_4', '#skF_6', '#skF_7')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_8359])).
% 13.98/5.42  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.98/5.42  tff(c_52, plain, (![A_32]: (k1_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.98/5.42  tff(c_56, plain, (![A_33]: (v1_relat_1(k6_relat_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 13.98/5.42  tff(c_235, plain, (![A_74]: (k1_relat_1(A_74)!=k1_xboole_0 | k1_xboole_0=A_74 | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.98/5.42  tff(c_244, plain, (![A_33]: (k1_relat_1(k6_relat_1(A_33))!=k1_xboole_0 | k6_relat_1(A_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_235])).
% 13.98/5.42  tff(c_253, plain, (![A_75]: (k1_xboole_0!=A_75 | k6_relat_1(A_75)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_244])).
% 13.98/5.42  tff(c_155, plain, (![A_62]: (v1_xboole_0(k1_relat_1(A_62)) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.98/5.42  tff(c_158, plain, (![A_32]: (v1_xboole_0(A_32) | ~v1_xboole_0(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_155])).
% 13.98/5.42  tff(c_262, plain, (![A_75]: (v1_xboole_0(A_75) | ~v1_xboole_0(k1_xboole_0) | k1_xboole_0!=A_75)), inference(superposition, [status(thm), theory('equality')], [c_253, c_158])).
% 13.98/5.42  tff(c_280, plain, (![A_75]: (v1_xboole_0(A_75) | k1_xboole_0!=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_262])).
% 13.98/5.42  tff(c_762, plain, (![A_106, B_107]: (r2_hidden('#skF_2'(A_106, B_107), A_106) | r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.98/5.42  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.98/5.42  tff(c_773, plain, (![A_108, B_109]: (~v1_xboole_0(A_108) | r1_tarski(A_108, B_109))), inference(resolution, [status(thm)], [c_762, c_2])).
% 13.98/5.42  tff(c_620, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.98/5.42  tff(c_630, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_6' | ~r1_tarski('#skF_6', k2_relset_1('#skF_4', '#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_90, c_620])).
% 13.98/5.42  tff(c_702, plain, (~r1_tarski('#skF_6', k2_relset_1('#skF_4', '#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_630])).
% 13.98/5.42  tff(c_791, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_773, c_702])).
% 13.98/5.42  tff(c_805, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_280, c_791])).
% 13.98/5.42  tff(c_68, plain, (![C_45, A_43, B_44]: (m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~r1_tarski(k2_relat_1(C_45), B_44) | ~r1_tarski(k1_relat_1(C_45), A_43) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.98/5.42  tff(c_2154, plain, (![B_224, C_225, A_226]: (k1_xboole_0=B_224 | v1_funct_2(C_225, A_226, B_224) | k1_relset_1(A_226, B_224, C_225)!=A_226 | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_226, B_224))))), inference(cnfTransformation, [status(thm)], [f_163])).
% 13.98/5.42  tff(c_11283, plain, (![B_617, C_618, A_619]: (k1_xboole_0=B_617 | v1_funct_2(C_618, A_619, B_617) | k1_relset_1(A_619, B_617, C_618)!=A_619 | ~r1_tarski(k2_relat_1(C_618), B_617) | ~r1_tarski(k1_relat_1(C_618), A_619) | ~v1_relat_1(C_618))), inference(resolution, [status(thm)], [c_68, c_2154])).
% 13.98/5.42  tff(c_11297, plain, (![A_619]: (k1_xboole_0='#skF_6' | v1_funct_2('#skF_7', A_619, '#skF_6') | k1_relset_1(A_619, '#skF_6', '#skF_7')!=A_619 | ~r1_tarski(k1_relat_1('#skF_7'), A_619) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1300, c_11283])).
% 13.98/5.42  tff(c_11316, plain, (![A_619]: (k1_xboole_0='#skF_6' | v1_funct_2('#skF_7', A_619, '#skF_6') | k1_relset_1(A_619, '#skF_6', '#skF_7')!=A_619 | ~r1_tarski('#skF_4', A_619))), inference(demodulation, [status(thm), theory('equality')], [c_714, c_2088, c_11297])).
% 13.98/5.42  tff(c_11322, plain, (![A_620]: (v1_funct_2('#skF_7', A_620, '#skF_6') | k1_relset_1(A_620, '#skF_6', '#skF_7')!=A_620 | ~r1_tarski('#skF_4', A_620))), inference(negUnitSimplification, [status(thm)], [c_805, c_11316])).
% 13.98/5.42  tff(c_96, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_183])).
% 13.98/5.42  tff(c_86, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_4', '#skF_6') | ~v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_183])).
% 13.98/5.42  tff(c_98, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_86])).
% 13.98/5.42  tff(c_234, plain, (~v1_funct_2('#skF_7', '#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_98])).
% 13.98/5.42  tff(c_11325, plain, (k1_relset_1('#skF_4', '#skF_6', '#skF_7')!='#skF_4' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_11322, c_234])).
% 13.98/5.42  tff(c_11329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_8379, c_11325])).
% 13.98/5.42  tff(c_11330, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_630])).
% 13.98/5.42  tff(c_11911, plain, (![A_682, B_683, C_684]: (k2_relset_1(A_682, B_683, C_684)=k2_relat_1(C_684) | ~m1_subset_1(C_684, k1_zfmisc_1(k2_zfmisc_1(A_682, B_683))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.98/5.42  tff(c_11918, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_92, c_11911])).
% 13.98/5.42  tff(c_11927, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11330, c_11918])).
% 13.98/5.42  tff(c_11339, plain, (![B_621, A_622]: (v1_relat_1(B_621) | ~m1_subset_1(B_621, k1_zfmisc_1(A_622)) | ~v1_relat_1(A_622))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.98/5.42  tff(c_11345, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_92, c_11339])).
% 13.98/5.42  tff(c_11349, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_11345])).
% 13.98/5.42  tff(c_48, plain, (![A_31]: (k2_relat_1(A_31)!=k1_xboole_0 | k1_xboole_0=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.98/5.42  tff(c_11356, plain, (k2_relat_1('#skF_7')!=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_11349, c_48])).
% 13.98/5.42  tff(c_11358, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_11356])).
% 13.98/5.42  tff(c_11928, plain, (k1_xboole_0!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11927, c_11358])).
% 13.98/5.42  tff(c_12012, plain, (![A_696, B_697, C_698]: (k1_relset_1(A_696, B_697, C_698)=k1_relat_1(C_698) | ~m1_subset_1(C_698, k1_zfmisc_1(k2_zfmisc_1(A_696, B_697))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.98/5.42  tff(c_12027, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_92, c_12012])).
% 13.98/5.42  tff(c_12563, plain, (![B_748, A_749, C_750]: (k1_xboole_0=B_748 | k1_relset_1(A_749, B_748, C_750)=A_749 | ~v1_funct_2(C_750, A_749, B_748) | ~m1_subset_1(C_750, k1_zfmisc_1(k2_zfmisc_1(A_749, B_748))))), inference(cnfTransformation, [status(thm)], [f_163])).
% 13.98/5.42  tff(c_12573, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_92, c_12563])).
% 13.98/5.42  tff(c_12584, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_12027, c_12573])).
% 13.98/5.42  tff(c_12585, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_154, c_12584])).
% 13.98/5.42  tff(c_12414, plain, (![C_734, A_735, B_736]: (m1_subset_1(C_734, k1_zfmisc_1(k2_zfmisc_1(A_735, B_736))) | ~r1_tarski(k2_relat_1(C_734), B_736) | ~r1_tarski(k1_relat_1(C_734), A_735) | ~v1_relat_1(C_734))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.98/5.42  tff(c_64, plain, (![A_37, B_38, C_39]: (k1_relset_1(A_37, B_38, C_39)=k1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.98/5.42  tff(c_20825, plain, (![A_1108, B_1109, C_1110]: (k1_relset_1(A_1108, B_1109, C_1110)=k1_relat_1(C_1110) | ~r1_tarski(k2_relat_1(C_1110), B_1109) | ~r1_tarski(k1_relat_1(C_1110), A_1108) | ~v1_relat_1(C_1110))), inference(resolution, [status(thm)], [c_12414, c_64])).
% 13.98/5.42  tff(c_20839, plain, (![A_1108, B_1109]: (k1_relset_1(A_1108, B_1109, '#skF_7')=k1_relat_1('#skF_7') | ~r1_tarski('#skF_6', B_1109) | ~r1_tarski(k1_relat_1('#skF_7'), A_1108) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_11927, c_20825])).
% 13.98/5.42  tff(c_21154, plain, (![A_1117, B_1118]: (k1_relset_1(A_1117, B_1118, '#skF_7')='#skF_4' | ~r1_tarski('#skF_6', B_1118) | ~r1_tarski('#skF_4', A_1117))), inference(demodulation, [status(thm), theory('equality')], [c_11349, c_12585, c_12585, c_20839])).
% 13.98/5.42  tff(c_21171, plain, (![A_1119]: (k1_relset_1(A_1119, '#skF_6', '#skF_7')='#skF_4' | ~r1_tarski('#skF_4', A_1119))), inference(resolution, [status(thm)], [c_20, c_21154])).
% 13.98/5.42  tff(c_21191, plain, (k1_relset_1('#skF_4', '#skF_6', '#skF_7')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_21171])).
% 13.98/5.42  tff(c_12520, plain, (![B_743, C_744, A_745]: (k1_xboole_0=B_743 | v1_funct_2(C_744, A_745, B_743) | k1_relset_1(A_745, B_743, C_744)!=A_745 | ~m1_subset_1(C_744, k1_zfmisc_1(k2_zfmisc_1(A_745, B_743))))), inference(cnfTransformation, [status(thm)], [f_163])).
% 13.98/5.42  tff(c_22269, plain, (![B_1164, C_1165, A_1166]: (k1_xboole_0=B_1164 | v1_funct_2(C_1165, A_1166, B_1164) | k1_relset_1(A_1166, B_1164, C_1165)!=A_1166 | ~r1_tarski(k2_relat_1(C_1165), B_1164) | ~r1_tarski(k1_relat_1(C_1165), A_1166) | ~v1_relat_1(C_1165))), inference(resolution, [status(thm)], [c_68, c_12520])).
% 13.98/5.42  tff(c_22283, plain, (![B_1164, A_1166]: (k1_xboole_0=B_1164 | v1_funct_2('#skF_7', A_1166, B_1164) | k1_relset_1(A_1166, B_1164, '#skF_7')!=A_1166 | ~r1_tarski('#skF_6', B_1164) | ~r1_tarski(k1_relat_1('#skF_7'), A_1166) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_11927, c_22269])).
% 13.98/5.42  tff(c_22944, plain, (![B_1169, A_1170]: (k1_xboole_0=B_1169 | v1_funct_2('#skF_7', A_1170, B_1169) | k1_relset_1(A_1170, B_1169, '#skF_7')!=A_1170 | ~r1_tarski('#skF_6', B_1169) | ~r1_tarski('#skF_4', A_1170))), inference(demodulation, [status(thm), theory('equality')], [c_11349, c_12585, c_22283])).
% 13.98/5.42  tff(c_22950, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_4', '#skF_6', '#skF_7')!='#skF_4' | ~r1_tarski('#skF_6', '#skF_6') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_22944, c_234])).
% 13.98/5.42  tff(c_22955, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_21191, c_22950])).
% 13.98/5.42  tff(c_22957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11928, c_22955])).
% 13.98/5.42  tff(c_22958, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_11356])).
% 13.98/5.42  tff(c_22982, plain, ('#skF_7'!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22958, c_154])).
% 13.98/5.42  tff(c_22959, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_11356])).
% 13.98/5.42  tff(c_22993, plain, (k2_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_22958, c_22959])).
% 13.98/5.42  tff(c_23576, plain, (![A_1217, B_1218, C_1219]: (k2_relset_1(A_1217, B_1218, C_1219)=k2_relat_1(C_1219) | ~m1_subset_1(C_1219, k1_zfmisc_1(k2_zfmisc_1(A_1217, B_1218))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.98/5.42  tff(c_23589, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_92, c_23576])).
% 13.98/5.42  tff(c_23592, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22993, c_11330, c_23589])).
% 13.98/5.42  tff(c_23621, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_23592, c_22958])).
% 13.98/5.42  tff(c_26, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.98/5.42  tff(c_74, plain, (![A_49]: (v1_funct_2(k1_xboole_0, A_49, k1_xboole_0) | k1_xboole_0=A_49 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_49, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_163])).
% 13.98/5.42  tff(c_102, plain, (![A_49]: (v1_funct_2(k1_xboole_0, A_49, k1_xboole_0) | k1_xboole_0=A_49 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_74])).
% 13.98/5.42  tff(c_23636, plain, (![A_49]: (v1_funct_2('#skF_6', A_49, '#skF_6') | A_49='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_23621, c_23621, c_23621, c_23621, c_23621, c_102])).
% 13.98/5.42  tff(c_23637, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_23636])).
% 13.98/5.42  tff(c_23653, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_32, c_23637])).
% 13.98/5.42  tff(c_23657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_23653])).
% 13.98/5.42  tff(c_24019, plain, (![A_1248]: (v1_funct_2('#skF_6', A_1248, '#skF_6') | A_1248='#skF_6')), inference(splitRight, [status(thm)], [c_23636])).
% 13.98/5.42  tff(c_23624, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_23592, c_234])).
% 13.98/5.42  tff(c_24032, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_24019, c_23624])).
% 13.98/5.42  tff(c_22974, plain, (![A_75]: (v1_xboole_0(A_75) | A_75!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_22958, c_280])).
% 13.98/5.42  tff(c_23617, plain, (![A_75]: (v1_xboole_0(A_75) | A_75!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_23592, c_22974])).
% 13.98/5.42  tff(c_24183, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24032, c_23617])).
% 13.98/5.42  tff(c_28, plain, (![B_16]: (k2_zfmisc_1(k1_xboole_0, B_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.98/5.42  tff(c_22983, plain, (![B_16]: (k2_zfmisc_1('#skF_7', B_16)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_22958, c_22958, c_28])).
% 13.98/5.42  tff(c_23615, plain, (![B_16]: (k2_zfmisc_1('#skF_6', B_16)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_23592, c_23592, c_22983])).
% 13.98/5.42  tff(c_24060, plain, (![B_16]: (k2_zfmisc_1('#skF_4', B_16)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24032, c_24032, c_23615])).
% 13.98/5.42  tff(c_23108, plain, (![A_1180, B_1181]: (r2_hidden('#skF_2'(A_1180, B_1181), A_1180) | r1_tarski(A_1180, B_1181))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.98/5.42  tff(c_23119, plain, (![A_1182, B_1183]: (~v1_xboole_0(A_1182) | r1_tarski(A_1182, B_1183))), inference(resolution, [status(thm)], [c_23108, c_2])).
% 13.98/5.42  tff(c_199, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | ~m1_subset_1(A_70, k1_zfmisc_1(B_71)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.98/5.42  tff(c_203, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_92, c_199])).
% 13.98/5.42  tff(c_629, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_203, c_620])).
% 13.98/5.42  tff(c_23060, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_629])).
% 13.98/5.42  tff(c_23125, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_23119, c_23060])).
% 13.98/5.42  tff(c_24145, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24060, c_23125])).
% 13.98/5.42  tff(c_24186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24183, c_24145])).
% 13.98/5.42  tff(c_24187, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_629])).
% 13.98/5.42  tff(c_24, plain, (![B_16, A_15]: (k1_xboole_0=B_16 | k1_xboole_0=A_15 | k2_zfmisc_1(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.98/5.42  tff(c_24302, plain, (![B_1263, A_1264]: (B_1263='#skF_7' | A_1264='#skF_7' | k2_zfmisc_1(A_1264, B_1263)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_22958, c_22958, c_22958, c_24])).
% 13.98/5.42  tff(c_24305, plain, ('#skF_7'='#skF_5' | '#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_24187, c_24302])).
% 13.98/5.42  tff(c_24314, plain, ('#skF_7'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_22982, c_24305])).
% 13.98/5.42  tff(c_24329, plain, (![A_75]: (v1_xboole_0(A_75) | A_75!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24314, c_22974])).
% 13.98/5.42  tff(c_42, plain, (![A_27]: (v1_xboole_0(k1_relat_1(A_27)) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.98/5.42  tff(c_24189, plain, (![A_1255, B_1256]: (r2_hidden('#skF_2'(A_1255, B_1256), A_1255) | r1_tarski(A_1255, B_1256))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.98/5.42  tff(c_24199, plain, (![A_1255, B_1256]: (~v1_xboole_0(A_1255) | r1_tarski(A_1255, B_1256))), inference(resolution, [status(thm)], [c_24189, c_2])).
% 13.98/5.42  tff(c_24219, plain, (![A_1257, B_1258]: (~v1_xboole_0(A_1257) | r1_tarski(A_1257, B_1258))), inference(resolution, [status(thm)], [c_24189, c_2])).
% 13.98/5.42  tff(c_16, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.98/5.42  tff(c_25286, plain, (![B_1347, A_1348]: (B_1347=A_1348 | ~r1_tarski(B_1347, A_1348) | ~v1_xboole_0(A_1348))), inference(resolution, [status(thm)], [c_24219, c_16])).
% 13.98/5.42  tff(c_25304, plain, (![B_1349, A_1350]: (B_1349=A_1350 | ~v1_xboole_0(B_1349) | ~v1_xboole_0(A_1350))), inference(resolution, [status(thm)], [c_24199, c_25286])).
% 13.98/5.42  tff(c_25469, plain, (![A_1363, A_1364]: (k1_relat_1(A_1363)=A_1364 | ~v1_xboole_0(A_1364) | ~v1_xboole_0(A_1363))), inference(resolution, [status(thm)], [c_42, c_25304])).
% 13.98/5.42  tff(c_26088, plain, (![A_1438, A_1439]: (k1_relat_1(A_1438)=A_1439 | ~v1_xboole_0(A_1438) | A_1439!='#skF_4')), inference(resolution, [status(thm)], [c_24329, c_25469])).
% 13.98/5.42  tff(c_26252, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_24329, c_26088])).
% 13.98/5.42  tff(c_24744, plain, (![A_1303, B_1304, C_1305]: (k1_relset_1(A_1303, B_1304, C_1305)=k1_relat_1(C_1305) | ~m1_subset_1(C_1305, k1_zfmisc_1(k2_zfmisc_1(A_1303, B_1304))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.98/5.42  tff(c_26803, plain, (![A_1482, B_1483, A_1484]: (k1_relset_1(A_1482, B_1483, A_1484)=k1_relat_1(A_1484) | ~r1_tarski(A_1484, k2_zfmisc_1(A_1482, B_1483)))), inference(resolution, [status(thm)], [c_32, c_24744])).
% 13.98/5.42  tff(c_26933, plain, (![A_1488, B_1489, A_1490]: (k1_relset_1(A_1488, B_1489, A_1490)=k1_relat_1(A_1490) | ~v1_xboole_0(A_1490))), inference(resolution, [status(thm)], [c_24199, c_26803])).
% 13.98/5.42  tff(c_27209, plain, (![A_1488, B_1489]: (k1_relset_1(A_1488, B_1489, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24329, c_26933])).
% 13.98/5.42  tff(c_24331, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24314, c_24314, c_22993])).
% 13.98/5.42  tff(c_24648, plain, (![A_1294, B_1295, C_1296]: (k2_relset_1(A_1294, B_1295, C_1296)=k2_relat_1(C_1296) | ~m1_subset_1(C_1296, k1_zfmisc_1(k2_zfmisc_1(A_1294, B_1295))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.98/5.42  tff(c_26634, plain, (![A_1472, B_1473, A_1474]: (k2_relset_1(A_1472, B_1473, A_1474)=k2_relat_1(A_1474) | ~r1_tarski(A_1474, k2_zfmisc_1(A_1472, B_1473)))), inference(resolution, [status(thm)], [c_32, c_24648])).
% 13.98/5.42  tff(c_26954, plain, (![A_1491, B_1492, A_1493]: (k2_relset_1(A_1491, B_1492, A_1493)=k2_relat_1(A_1493) | ~v1_xboole_0(A_1493))), inference(resolution, [status(thm)], [c_24199, c_26634])).
% 13.98/5.42  tff(c_27090, plain, (![A_1503, B_1504, A_1505]: (k2_relset_1(A_1503, B_1504, A_1505)=k2_relat_1(A_1505) | A_1505!='#skF_4')), inference(resolution, [status(thm)], [c_24329, c_26954])).
% 13.98/5.42  tff(c_24335, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24314, c_11330])).
% 13.98/5.42  tff(c_27100, plain, (k2_relat_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_27090, c_24335])).
% 13.98/5.42  tff(c_27113, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24331, c_27100])).
% 13.98/5.42  tff(c_24200, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_24187, c_92])).
% 13.98/5.42  tff(c_24324, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24314, c_24314, c_24200])).
% 13.98/5.42  tff(c_24333, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24314, c_22958])).
% 13.98/5.42  tff(c_78, plain, (![C_51, B_50]: (v1_funct_2(C_51, k1_xboole_0, B_50) | k1_relset_1(k1_xboole_0, B_50, C_51)!=k1_xboole_0 | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_50))))), inference(cnfTransformation, [status(thm)], [f_163])).
% 13.98/5.42  tff(c_99, plain, (![C_51, B_50]: (v1_funct_2(C_51, k1_xboole_0, B_50) | k1_relset_1(k1_xboole_0, B_50, C_51)!=k1_xboole_0 | ~m1_subset_1(C_51, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_78])).
% 13.98/5.42  tff(c_24992, plain, (![C_1318, B_1319]: (v1_funct_2(C_1318, '#skF_4', B_1319) | k1_relset_1('#skF_4', B_1319, C_1318)!='#skF_4' | ~m1_subset_1(C_1318, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_24333, c_24333, c_24333, c_24333, c_99])).
% 13.98/5.42  tff(c_25001, plain, (![B_1320]: (v1_funct_2('#skF_4', '#skF_4', B_1320) | k1_relset_1('#skF_4', B_1320, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_24324, c_24992])).
% 13.98/5.42  tff(c_24336, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24314, c_234])).
% 13.98/5.42  tff(c_25012, plain, (k1_relset_1('#skF_4', '#skF_6', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_25001, c_24336])).
% 13.98/5.42  tff(c_27118, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27113, c_25012])).
% 13.98/5.42  tff(c_27210, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27209, c_27118])).
% 13.98/5.42  tff(c_27214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26252, c_27210])).
% 13.98/5.42  tff(c_27215, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_98])).
% 13.98/5.42  tff(c_28826, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r1_tarski(k1_relat_1('#skF_7'), '#skF_4') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28801, c_27215])).
% 13.98/5.42  tff(c_28848, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27446, c_28311, c_28826])).
% 13.98/5.42  tff(c_28861, plain, (~v4_relat_1('#skF_7', '#skF_4') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_28848])).
% 13.98/5.42  tff(c_28874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27446, c_28065, c_28861])).
% 13.98/5.42  tff(c_28875, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_88])).
% 13.98/5.42  tff(c_28881, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28875, c_12])).
% 13.98/5.42  tff(c_50, plain, (![A_31]: (k1_relat_1(A_31)!=k1_xboole_0 | k1_xboole_0=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.98/5.42  tff(c_29007, plain, (![A_1664]: (k1_relat_1(A_1664)!='#skF_4' | A_1664='#skF_4' | ~v1_relat_1(A_1664))), inference(demodulation, [status(thm), theory('equality')], [c_28875, c_28875, c_50])).
% 13.98/5.42  tff(c_29016, plain, (![A_33]: (k1_relat_1(k6_relat_1(A_33))!='#skF_4' | k6_relat_1(A_33)='#skF_4')), inference(resolution, [status(thm)], [c_56, c_29007])).
% 13.98/5.42  tff(c_29025, plain, (![A_1665]: (A_1665!='#skF_4' | k6_relat_1(A_1665)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_29016])).
% 13.98/5.42  tff(c_28923, plain, (![A_1652]: (v1_xboole_0(k1_relat_1(A_1652)) | ~v1_xboole_0(A_1652))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.98/5.42  tff(c_28926, plain, (![A_32]: (v1_xboole_0(A_32) | ~v1_xboole_0(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_28923])).
% 13.98/5.42  tff(c_29034, plain, (![A_1665]: (v1_xboole_0(A_1665) | ~v1_xboole_0('#skF_4') | A_1665!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_29025, c_28926])).
% 13.98/5.42  tff(c_29058, plain, (![A_1666]: (v1_xboole_0(A_1666) | A_1666!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28881, c_29034])).
% 13.98/5.42  tff(c_14, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.98/5.42  tff(c_28936, plain, (![A_1657]: (r2_hidden('#skF_3'(A_1657), A_1657) | A_1657='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28875, c_14])).
% 13.98/5.42  tff(c_28941, plain, (![A_1658]: (~v1_xboole_0(A_1658) | A_1658='#skF_4')), inference(resolution, [status(thm)], [c_28936, c_2])).
% 13.98/5.42  tff(c_28948, plain, (![A_27]: (k1_relat_1(A_27)='#skF_4' | ~v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_42, c_28941])).
% 13.98/5.42  tff(c_29148, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_29058, c_28948])).
% 13.98/5.42  tff(c_22, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.98/5.42  tff(c_28880, plain, (![A_14]: (r1_tarski('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_28875, c_22])).
% 13.98/5.42  tff(c_28877, plain, (![B_16]: (k2_zfmisc_1('#skF_4', B_16)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28875, c_28875, c_28])).
% 13.98/5.42  tff(c_28876, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_88])).
% 13.98/5.42  tff(c_28886, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28875, c_28876])).
% 13.98/5.42  tff(c_28892, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_28886, c_92])).
% 13.98/5.42  tff(c_28894, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28877, c_28892])).
% 13.98/5.42  tff(c_28960, plain, (![A_1660, B_1661]: (r1_tarski(A_1660, B_1661) | ~m1_subset_1(A_1660, k1_zfmisc_1(B_1661)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.98/5.42  tff(c_28964, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_28894, c_28960])).
% 13.98/5.42  tff(c_29461, plain, (![B_1686, A_1687]: (B_1686=A_1687 | ~r1_tarski(B_1686, A_1687) | ~r1_tarski(A_1687, B_1686))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.98/5.42  tff(c_29463, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_28964, c_29461])).
% 13.98/5.42  tff(c_29472, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28880, c_29463])).
% 13.98/5.42  tff(c_29483, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_29472, c_28894])).
% 13.98/5.42  tff(c_30335, plain, (![A_1779, B_1780, C_1781]: (k1_relset_1(A_1779, B_1780, C_1781)=k1_relat_1(C_1781) | ~m1_subset_1(C_1781, k1_zfmisc_1(k2_zfmisc_1(A_1779, B_1780))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.98/5.42  tff(c_32172, plain, (![B_1910, C_1911]: (k1_relset_1('#skF_4', B_1910, C_1911)=k1_relat_1(C_1911) | ~m1_subset_1(C_1911, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_28877, c_30335])).
% 13.98/5.42  tff(c_32174, plain, (![B_1910]: (k1_relset_1('#skF_4', B_1910, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_29483, c_32172])).
% 13.98/5.42  tff(c_32179, plain, (![B_1910]: (k1_relset_1('#skF_4', B_1910, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29148, c_32174])).
% 13.98/5.42  tff(c_30415, plain, (![C_1795, B_1796]: (v1_funct_2(C_1795, '#skF_4', B_1796) | k1_relset_1('#skF_4', B_1796, C_1795)!='#skF_4' | ~m1_subset_1(C_1795, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_28875, c_28875, c_28875, c_28875, c_99])).
% 13.98/5.42  tff(c_30443, plain, (![B_1799]: (v1_funct_2('#skF_4', '#skF_4', B_1799) | k1_relset_1('#skF_4', B_1799, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_29483, c_30415])).
% 13.98/5.42  tff(c_29004, plain, (~v1_funct_2('#skF_7', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28894, c_28877, c_98])).
% 13.98/5.42  tff(c_29480, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_29472, c_29004])).
% 13.98/5.42  tff(c_30459, plain, (k1_relset_1('#skF_4', '#skF_6', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_30443, c_29480])).
% 13.98/5.42  tff(c_32186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32179, c_30459])).
% 13.98/5.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.98/5.42  
% 13.98/5.42  Inference rules
% 13.98/5.42  ----------------------
% 13.98/5.42  #Ref     : 39
% 13.98/5.42  #Sup     : 7775
% 13.98/5.42  #Fact    : 0
% 13.98/5.42  #Define  : 0
% 13.98/5.42  #Split   : 59
% 13.98/5.42  #Chain   : 0
% 13.98/5.42  #Close   : 0
% 13.98/5.42  
% 13.98/5.42  Ordering : KBO
% 13.98/5.42  
% 13.98/5.42  Simplification rules
% 13.98/5.42  ----------------------
% 13.98/5.42  #Subsume      : 4120
% 13.98/5.42  #Demod        : 3300
% 13.98/5.42  #Tautology    : 1761
% 13.98/5.42  #SimpNegUnit  : 272
% 13.98/5.42  #BackRed      : 296
% 13.98/5.42  
% 13.98/5.42  #Partial instantiations: 0
% 13.98/5.42  #Strategies tried      : 1
% 13.98/5.42  
% 13.98/5.42  Timing (in seconds)
% 13.98/5.42  ----------------------
% 13.98/5.42  Preprocessing        : 0.37
% 13.98/5.42  Parsing              : 0.18
% 13.98/5.42  CNF conversion       : 0.03
% 13.98/5.42  Main loop            : 4.25
% 13.98/5.42  Inferencing          : 1.03
% 13.98/5.42  Reduction            : 1.42
% 13.98/5.43  Demodulation         : 0.99
% 13.98/5.43  BG Simplification    : 0.09
% 13.98/5.43  Subsumption          : 1.43
% 13.98/5.43  Abstraction          : 0.13
% 13.98/5.43  MUC search           : 0.00
% 13.98/5.43  Cooper               : 0.00
% 13.98/5.43  Total                : 4.69
% 13.98/5.43  Index Insertion      : 0.00
% 13.98/5.43  Index Deletion       : 0.00
% 13.98/5.43  Index Matching       : 0.00
% 13.98/5.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
