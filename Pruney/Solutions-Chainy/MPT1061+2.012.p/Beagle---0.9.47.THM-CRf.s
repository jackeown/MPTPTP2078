%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:38 EST 2020

% Result     : Theorem 12.16s
% Output     : CNFRefutation 12.55s
% Verified   : 
% Statistics : Number of formulae       :  458 (2981 expanded)
%              Number of leaves         :   54 ( 971 expanded)
%              Depth                    :   19
%              Number of atoms          :  772 (7838 expanded)
%              Number of equality atoms :  204 ( 880 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_219,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_172,axiom,(
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

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_186,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_180,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_198,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_92,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_94,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_122,plain,(
    ! [B_84,A_85] :
      ( v1_relat_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_128,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_6')) ),
    inference(resolution,[status(thm)],[c_94,c_122])).

tff(c_135,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_128])).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_96,plain,(
    v1_funct_2('#skF_7','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_37666,plain,(
    ! [A_2319,B_2320,C_2321] :
      ( k1_relset_1(A_2319,B_2320,C_2321) = k1_relat_1(C_2321)
      | ~ m1_subset_1(C_2321,k1_zfmisc_1(k2_zfmisc_1(A_2319,B_2320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_37675,plain,(
    k1_relset_1('#skF_3','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_37666])).

tff(c_90,plain,(
    r1_tarski(k7_relset_1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1293,plain,(
    ! [B_210,A_211] :
      ( v1_xboole_0(B_210)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(A_211))
      | ~ v1_xboole_0(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1313,plain,(
    ! [A_214,B_215] :
      ( v1_xboole_0(A_214)
      | ~ v1_xboole_0(B_215)
      | ~ r1_tarski(A_214,B_215) ) ),
    inference(resolution,[status(thm)],[c_24,c_1293])).

tff(c_1339,plain,
    ( v1_xboole_0(k7_relset_1('#skF_3','#skF_6','#skF_7','#skF_4'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_1313])).

tff(c_17010,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1339])).

tff(c_27755,plain,(
    ! [A_1819,B_1820,C_1821] :
      ( k1_relset_1(A_1819,B_1820,C_1821) = k1_relat_1(C_1821)
      | ~ m1_subset_1(C_1821,k1_zfmisc_1(k2_zfmisc_1(A_1819,B_1820))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_27774,plain,(
    k1_relset_1('#skF_3','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_27755])).

tff(c_31835,plain,(
    ! [B_1974,A_1975,C_1976] :
      ( k1_xboole_0 = B_1974
      | k1_relset_1(A_1975,B_1974,C_1976) = A_1975
      | ~ v1_funct_2(C_1976,A_1975,B_1974)
      | ~ m1_subset_1(C_1976,k1_zfmisc_1(k2_zfmisc_1(A_1975,B_1974))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_31879,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_3','#skF_6','#skF_7') = '#skF_3'
    | ~ v1_funct_2('#skF_7','#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_31835])).

tff(c_31890,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_27774,c_31879])).

tff(c_31891,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_31890])).

tff(c_26957,plain,(
    ! [C_1743,A_1744,B_1745] :
      ( v4_relat_1(C_1743,A_1744)
      | ~ m1_subset_1(C_1743,k1_zfmisc_1(k2_zfmisc_1(A_1744,B_1745))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26975,plain,(
    v4_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_26957])).

tff(c_38,plain,(
    ! [B_29,A_28] :
      ( k7_relat_1(B_29,A_28) = B_29
      | ~ v4_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26978,plain,
    ( k7_relat_1('#skF_7','#skF_3') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_26975,c_38])).

tff(c_26981,plain,(
    k7_relat_1('#skF_7','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_26978])).

tff(c_40,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_31,A_30)),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_27031,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_3')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_26981,c_40])).

tff(c_27037,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_27031])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_27054,plain,
    ( k1_relat_1('#skF_7') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_27037,c_8])).

tff(c_27134,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_27054])).

tff(c_31893,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31891,c_27134])).

tff(c_31897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_31893])).

tff(c_31898,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_31890])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1341,plain,(
    ! [A_8] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_1313])).

tff(c_1344,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitLeft,[status(thm)],[c_1341])).

tff(c_16,plain,(
    ! [A_9] : v1_xboole_0('#skF_2'(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1344,c_16])).

tff(c_1349,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1341])).

tff(c_31955,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31898,c_1349])).

tff(c_31959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_31955])).

tff(c_31960,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_27054])).

tff(c_32349,plain,(
    ! [B_2016,A_2017] :
      ( k1_relat_1(k7_relat_1(B_2016,A_2017)) = A_2017
      | ~ r1_tarski(A_2017,k1_relat_1(B_2016))
      | ~ v1_relat_1(B_2016) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32365,plain,(
    ! [A_2017] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_2017)) = A_2017
      | ~ r1_tarski(A_2017,'#skF_3')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31960,c_32349])).

tff(c_32400,plain,(
    ! [A_2017] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_2017)) = A_2017
      | ~ r1_tarski(A_2017,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_32365])).

tff(c_98,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_35693,plain,(
    ! [A_2169,B_2170,C_2171,D_2172] :
      ( k2_partfun1(A_2169,B_2170,C_2171,D_2172) = k7_relat_1(C_2171,D_2172)
      | ~ m1_subset_1(C_2171,k1_zfmisc_1(k2_zfmisc_1(A_2169,B_2170)))
      | ~ v1_funct_1(C_2171) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_35719,plain,(
    ! [D_2172] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_2172) = k7_relat_1('#skF_7',D_2172)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_94,c_35693])).

tff(c_35729,plain,(
    ! [D_2172] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_2172) = k7_relat_1('#skF_7',D_2172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_35719])).

tff(c_17902,plain,(
    ! [A_1272,B_1273,C_1274] :
      ( k1_relset_1(A_1272,B_1273,C_1274) = k1_relat_1(C_1274)
      | ~ m1_subset_1(C_1274,k1_zfmisc_1(k2_zfmisc_1(A_1272,B_1273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_17917,plain,(
    k1_relset_1('#skF_3','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_17902])).

tff(c_20033,plain,(
    ! [B_1402,A_1403,C_1404] :
      ( k1_xboole_0 = B_1402
      | k1_relset_1(A_1403,B_1402,C_1404) = A_1403
      | ~ v1_funct_2(C_1404,A_1403,B_1402)
      | ~ m1_subset_1(C_1404,k1_zfmisc_1(k2_zfmisc_1(A_1403,B_1402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_20065,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_3','#skF_6','#skF_7') = '#skF_3'
    | ~ v1_funct_2('#skF_7','#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_20033])).

tff(c_20074,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_17917,c_20065])).

tff(c_20075,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20074])).

tff(c_17219,plain,(
    ! [C_1205,A_1206,B_1207] :
      ( v4_relat_1(C_1205,A_1206)
      | ~ m1_subset_1(C_1205,k1_zfmisc_1(k2_zfmisc_1(A_1206,B_1207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_17232,plain,(
    v4_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_17219])).

tff(c_17236,plain,
    ( k7_relat_1('#skF_7','#skF_3') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_17232,c_38])).

tff(c_17239,plain,(
    k7_relat_1('#skF_7','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_17236])).

tff(c_17246,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_3')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_17239,c_40])).

tff(c_17252,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_17246])).

tff(c_17262,plain,
    ( k1_relat_1('#skF_7') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_17252,c_8])).

tff(c_17275,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_17262])).

tff(c_20077,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20075,c_17275])).

tff(c_20081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20077])).

tff(c_20082,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_20074])).

tff(c_20129,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20082,c_1349])).

tff(c_20133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_20129])).

tff(c_20134,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17262])).

tff(c_20680,plain,(
    ! [B_1461,A_1462] :
      ( k1_relat_1(k7_relat_1(B_1461,A_1462)) = A_1462
      | ~ r1_tarski(A_1462,k1_relat_1(B_1461))
      | ~ v1_relat_1(B_1461) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20690,plain,(
    ! [A_1462] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_1462)) = A_1462
      | ~ r1_tarski(A_1462,'#skF_3')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20134,c_20680])).

tff(c_20714,plain,(
    ! [A_1462] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_1462)) = A_1462
      | ~ r1_tarski(A_1462,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_20690])).

tff(c_26538,plain,(
    ! [A_1711,B_1712,C_1713,D_1714] :
      ( k2_partfun1(A_1711,B_1712,C_1713,D_1714) = k7_relat_1(C_1713,D_1714)
      | ~ m1_subset_1(C_1713,k1_zfmisc_1(k2_zfmisc_1(A_1711,B_1712)))
      | ~ v1_funct_1(C_1713) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_26564,plain,(
    ! [D_1714] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_1714) = k7_relat_1('#skF_7',D_1714)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_94,c_26538])).

tff(c_26575,plain,(
    ! [D_1714] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_1714) = k7_relat_1('#skF_7',D_1714) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_26564])).

tff(c_21719,plain,(
    ! [A_1541,B_1542,C_1543,D_1544] :
      ( k7_relset_1(A_1541,B_1542,C_1543,D_1544) = k9_relat_1(C_1543,D_1544)
      | ~ m1_subset_1(C_1543,k1_zfmisc_1(k2_zfmisc_1(A_1541,B_1542))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_21733,plain,(
    ! [D_1544] : k7_relset_1('#skF_3','#skF_6','#skF_7',D_1544) = k9_relat_1('#skF_7',D_1544) ),
    inference(resolution,[status(thm)],[c_94,c_21719])).

tff(c_21743,plain,(
    r1_tarski(k9_relat_1('#skF_7','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21733,c_90])).

tff(c_36,plain,(
    ! [B_27,A_26] :
      ( k2_relat_1(k7_relat_1(B_27,A_26)) = k9_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26303,plain,(
    ! [A_1700,B_1701,C_1702,D_1703] :
      ( k2_partfun1(A_1700,B_1701,C_1702,D_1703) = k7_relat_1(C_1702,D_1703)
      | ~ m1_subset_1(C_1702,k1_zfmisc_1(k2_zfmisc_1(A_1700,B_1701)))
      | ~ v1_funct_1(C_1702) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_26329,plain,(
    ! [D_1703] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_1703) = k7_relat_1('#skF_7',D_1703)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_94,c_26303])).

tff(c_26340,plain,(
    ! [D_1703] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_1703) = k7_relat_1('#skF_7',D_1703) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_26329])).

tff(c_23768,plain,(
    ! [A_1624,B_1625,C_1626,D_1627] :
      ( k2_partfun1(A_1624,B_1625,C_1626,D_1627) = k7_relat_1(C_1626,D_1627)
      | ~ m1_subset_1(C_1626,k1_zfmisc_1(k2_zfmisc_1(A_1624,B_1625)))
      | ~ v1_funct_1(C_1626) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_23794,plain,(
    ! [D_1627] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_1627) = k7_relat_1('#skF_7',D_1627)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_94,c_23768])).

tff(c_23805,plain,(
    ! [D_1627] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_1627) = k7_relat_1('#skF_7',D_1627) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_23794])).

tff(c_26077,plain,(
    ! [A_1693,B_1694,C_1695,D_1696] :
      ( m1_subset_1(k2_partfun1(A_1693,B_1694,C_1695,D_1696),k1_zfmisc_1(k2_zfmisc_1(A_1693,B_1694)))
      | ~ m1_subset_1(C_1695,k1_zfmisc_1(k2_zfmisc_1(A_1693,B_1694)))
      | ~ v1_funct_1(C_1695) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_26127,plain,(
    ! [D_1627] :
      ( m1_subset_1(k7_relat_1('#skF_7',D_1627),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_6')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_6')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23805,c_26077])).

tff(c_26167,plain,(
    ! [D_1697] : m1_subset_1(k7_relat_1('#skF_7',D_1697),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94,c_26127])).

tff(c_28,plain,(
    ! [B_21,A_19] :
      ( v1_relat_1(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_19))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26205,plain,(
    ! [D_1697] :
      ( v1_relat_1(k7_relat_1('#skF_7',D_1697))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_26167,c_28])).

tff(c_26233,plain,(
    ! [D_1697] : v1_relat_1(k7_relat_1('#skF_7',D_1697)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26205])).

tff(c_23593,plain,(
    ! [C_1616,A_1617,B_1618] :
      ( m1_subset_1(C_1616,k1_zfmisc_1(k2_zfmisc_1(A_1617,B_1618)))
      | ~ r1_tarski(k2_relat_1(C_1616),B_1618)
      | ~ r1_tarski(k1_relat_1(C_1616),A_1617)
      | ~ v1_relat_1(C_1616) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1264,plain,(
    ! [A_204,B_205,C_206,D_207] :
      ( v1_funct_1(k2_partfun1(A_204,B_205,C_206,D_207))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_1(C_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1272,plain,(
    ! [D_207] :
      ( v1_funct_1(k2_partfun1('#skF_3','#skF_6','#skF_7',D_207))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_94,c_1264])).

tff(c_1277,plain,(
    ! [D_207] : v1_funct_1(k2_partfun1('#skF_3','#skF_6','#skF_7',D_207)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1272])).

tff(c_88,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_4','#skF_5')
    | ~ v1_funct_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_165,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_1280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1277,c_165])).

tff(c_1281,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_4','#skF_5')
    | ~ m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_17191,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_23650,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_5')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(resolution,[status(thm)],[c_23593,c_17191])).

tff(c_23725,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_23650])).

tff(c_23806,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23805,c_23725])).

tff(c_26242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26233,c_23806])).

tff(c_26243,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_4')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_23650])).

tff(c_26245,plain,(
    ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_26243])).

tff(c_26353,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26340,c_26245])).

tff(c_26473,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_7','#skF_4'),'#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_26353])).

tff(c_26480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_21743,c_26473])).

tff(c_26481,plain,(
    ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_26243])).

tff(c_26702,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26575,c_26481])).

tff(c_26705,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20714,c_26702])).

tff(c_26714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_12,c_26705])).

tff(c_26715,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_35740,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_7','#skF_4'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35729,c_26715])).

tff(c_26716,plain,(
    m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_32912,plain,(
    ! [A_2051,B_2052,C_2053] :
      ( k1_relset_1(A_2051,B_2052,C_2053) = k1_relat_1(C_2053)
      | ~ m1_subset_1(C_2053,k1_zfmisc_1(k2_zfmisc_1(A_2051,B_2052))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_32930,plain,(
    k1_relset_1('#skF_4','#skF_5',k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) = k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(resolution,[status(thm)],[c_26716,c_32912])).

tff(c_35734,plain,(
    k1_relset_1('#skF_4','#skF_5',k7_relat_1('#skF_7','#skF_4')) = k1_relat_1(k7_relat_1('#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35729,c_35729,c_32930])).

tff(c_35739,plain,(
    m1_subset_1(k7_relat_1('#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35729,c_26716])).

tff(c_36005,plain,(
    ! [B_2179,C_2180,A_2181] :
      ( k1_xboole_0 = B_2179
      | v1_funct_2(C_2180,A_2181,B_2179)
      | k1_relset_1(A_2181,B_2179,C_2180) != A_2181
      | ~ m1_subset_1(C_2180,k1_zfmisc_1(k2_zfmisc_1(A_2181,B_2179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_36008,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2(k7_relat_1('#skF_7','#skF_4'),'#skF_4','#skF_5')
    | k1_relset_1('#skF_4','#skF_5',k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_35739,c_36005])).

tff(c_36048,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2(k7_relat_1('#skF_7','#skF_4'),'#skF_4','#skF_5')
    | k1_relat_1(k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35734,c_36008])).

tff(c_36049,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1(k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_35740,c_36048])).

tff(c_36059,plain,(
    k1_relat_1(k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36049])).

tff(c_36068,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32400,c_36059])).

tff(c_36077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_36068])).

tff(c_36078,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36049])).

tff(c_36130,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36078,c_1349])).

tff(c_36134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17010,c_36130])).

tff(c_36136,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1339])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37094,plain,(
    ! [C_2276,B_2277,A_2278] :
      ( ~ v1_xboole_0(C_2276)
      | ~ m1_subset_1(B_2277,k1_zfmisc_1(C_2276))
      | ~ r2_hidden(A_2278,B_2277) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_37492,plain,(
    ! [B_2307,A_2308,A_2309] :
      ( ~ v1_xboole_0(B_2307)
      | ~ r2_hidden(A_2308,A_2309)
      | ~ r1_tarski(A_2309,B_2307) ) ),
    inference(resolution,[status(thm)],[c_24,c_37094])).

tff(c_37496,plain,(
    ! [B_2310,A_2311,B_2312] :
      ( ~ v1_xboole_0(B_2310)
      | ~ r1_tarski(A_2311,B_2310)
      | r1_tarski(A_2311,B_2312) ) ),
    inference(resolution,[status(thm)],[c_6,c_37492])).

tff(c_37532,plain,(
    ! [B_2314,B_2315] :
      ( ~ v1_xboole_0(B_2314)
      | r1_tarski(B_2314,B_2315) ) ),
    inference(resolution,[status(thm)],[c_12,c_37496])).

tff(c_1357,plain,(
    ! [B_218,A_219] :
      ( B_218 = A_219
      | ~ r1_tarski(B_218,A_219)
      | ~ r1_tarski(A_219,B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1380,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_1357])).

tff(c_37593,plain,(
    ! [B_2316] :
      ( k1_xboole_0 = B_2316
      | ~ v1_xboole_0(B_2316) ) ),
    inference(resolution,[status(thm)],[c_37532,c_1380])).

tff(c_37603,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36136,c_37593])).

tff(c_74,plain,(
    ! [B_60,A_59,C_61] :
      ( k1_xboole_0 = B_60
      | k1_relset_1(A_59,B_60,C_61) = A_59
      | ~ v1_funct_2(C_61,A_59,B_60)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_38447,plain,(
    ! [B_2390,A_2391,C_2392] :
      ( B_2390 = '#skF_5'
      | k1_relset_1(A_2391,B_2390,C_2392) = A_2391
      | ~ v1_funct_2(C_2392,A_2391,B_2390)
      | ~ m1_subset_1(C_2392,k1_zfmisc_1(k2_zfmisc_1(A_2391,B_2390))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37603,c_74])).

tff(c_38464,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1('#skF_3','#skF_6','#skF_7') = '#skF_3'
    | ~ v1_funct_2('#skF_7','#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_38447])).

tff(c_38472,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_37675,c_38464])).

tff(c_38473,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_38472])).

tff(c_36895,plain,(
    ! [C_2260,A_2261,B_2262] :
      ( v4_relat_1(C_2260,A_2261)
      | ~ m1_subset_1(C_2260,k1_zfmisc_1(k2_zfmisc_1(A_2261,B_2262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36908,plain,(
    v4_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_36895])).

tff(c_36912,plain,
    ( k7_relat_1('#skF_7','#skF_3') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36908,c_38])).

tff(c_36915,plain,(
    k7_relat_1('#skF_7','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_36912])).

tff(c_36919,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_3')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36915,c_40])).

tff(c_36923,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_36919])).

tff(c_36933,plain,
    ( k1_relat_1('#skF_7') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_36923,c_8])).

tff(c_36945,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_36933])).

tff(c_38475,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38473,c_36945])).

tff(c_38479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38475])).

tff(c_38480,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38472])).

tff(c_38511,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38480,c_36136])).

tff(c_38514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_38511])).

tff(c_38515,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36933])).

tff(c_39035,plain,(
    ! [B_2436,A_2437] :
      ( k1_relat_1(k7_relat_1(B_2436,A_2437)) = A_2437
      | ~ r1_tarski(A_2437,k1_relat_1(B_2436))
      | ~ v1_relat_1(B_2436) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_39045,plain,(
    ! [A_2437] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_2437)) = A_2437
      | ~ r1_tarski(A_2437,'#skF_3')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38515,c_39035])).

tff(c_39073,plain,(
    ! [A_2437] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_2437)) = A_2437
      | ~ r1_tarski(A_2437,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_39045])).

tff(c_38701,plain,(
    ! [C_2406,B_2407,A_2408] :
      ( ~ v1_xboole_0(C_2406)
      | ~ m1_subset_1(B_2407,k1_zfmisc_1(C_2406))
      | ~ r2_hidden(A_2408,B_2407) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_39031,plain,(
    ! [B_2433,A_2434,A_2435] :
      ( ~ v1_xboole_0(B_2433)
      | ~ r2_hidden(A_2434,A_2435)
      | ~ r1_tarski(A_2435,B_2433) ) ),
    inference(resolution,[status(thm)],[c_24,c_38701])).

tff(c_39079,plain,(
    ! [B_2438,A_2439,B_2440] :
      ( ~ v1_xboole_0(B_2438)
      | ~ r1_tarski(A_2439,B_2438)
      | r1_tarski(A_2439,B_2440) ) ),
    inference(resolution,[status(thm)],[c_6,c_39031])).

tff(c_39105,plain,(
    ! [B_2441,B_2442] :
      ( ~ v1_xboole_0(B_2441)
      | r1_tarski(B_2441,B_2442) ) ),
    inference(resolution,[status(thm)],[c_12,c_39079])).

tff(c_39162,plain,(
    ! [B_2443] :
      ( k1_xboole_0 = B_2443
      | ~ v1_xboole_0(B_2443) ) ),
    inference(resolution,[status(thm)],[c_39105,c_1380])).

tff(c_39172,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36136,c_39162])).

tff(c_39175,plain,(
    ! [A_9] : '#skF_2'(A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_39162])).

tff(c_39205,plain,(
    ! [A_9] : '#skF_2'(A_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39172,c_39175])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1('#skF_2'(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(A_81,B_82)
      | ~ m1_subset_1(A_81,k1_zfmisc_1(B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_120,plain,(
    ! [A_9] : r1_tarski('#skF_2'(A_9),A_9) ),
    inference(resolution,[status(thm)],[c_18,c_108])).

tff(c_39215,plain,(
    ! [A_9] : r1_tarski('#skF_5',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39205,c_120])).

tff(c_39551,plain,(
    ! [A_2471,B_2472,C_2473,D_2474] :
      ( k7_relset_1(A_2471,B_2472,C_2473,D_2474) = k9_relat_1(C_2473,D_2474)
      | ~ m1_subset_1(C_2473,k1_zfmisc_1(k2_zfmisc_1(A_2471,B_2472))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_39627,plain,(
    ! [D_2488] : k7_relset_1('#skF_3','#skF_6','#skF_7',D_2488) = k9_relat_1('#skF_7',D_2488) ),
    inference(resolution,[status(thm)],[c_94,c_39551])).

tff(c_36261,plain,(
    ! [C_2199,B_2200,A_2201] :
      ( ~ v1_xboole_0(C_2199)
      | ~ m1_subset_1(B_2200,k1_zfmisc_1(C_2199))
      | ~ r2_hidden(A_2201,B_2200) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36631,plain,(
    ! [B_2224,A_2225,A_2226] :
      ( ~ v1_xboole_0(B_2224)
      | ~ r2_hidden(A_2225,A_2226)
      | ~ r1_tarski(A_2226,B_2224) ) ),
    inference(resolution,[status(thm)],[c_24,c_36261])).

tff(c_36713,plain,(
    ! [B_2237,A_2238,B_2239] :
      ( ~ v1_xboole_0(B_2237)
      | ~ r1_tarski(A_2238,B_2237)
      | r1_tarski(A_2238,B_2239) ) ),
    inference(resolution,[status(thm)],[c_6,c_36631])).

tff(c_36744,plain,(
    ! [B_2240,B_2241] :
      ( ~ v1_xboole_0(B_2240)
      | r1_tarski(B_2240,B_2241) ) ),
    inference(resolution,[status(thm)],[c_12,c_36713])).

tff(c_1375,plain,
    ( k7_relset_1('#skF_3','#skF_6','#skF_7','#skF_4') = '#skF_5'
    | ~ r1_tarski('#skF_5',k7_relset_1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_1357])).

tff(c_36137,plain,(
    ~ r1_tarski('#skF_5',k7_relset_1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1375])).

tff(c_36767,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36744,c_36137])).

tff(c_36796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36136,c_36767])).

tff(c_36797,plain,(
    k7_relset_1('#skF_3','#skF_6','#skF_7','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1375])).

tff(c_39633,plain,(
    k9_relat_1('#skF_7','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_39627,c_36797])).

tff(c_41377,plain,(
    ! [A_2599,B_2600,C_2601,D_2602] :
      ( k2_partfun1(A_2599,B_2600,C_2601,D_2602) = k7_relat_1(C_2601,D_2602)
      | ~ m1_subset_1(C_2601,k1_zfmisc_1(k2_zfmisc_1(A_2599,B_2600)))
      | ~ v1_funct_1(C_2601) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_41391,plain,(
    ! [D_2602] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_2602) = k7_relat_1('#skF_7',D_2602)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_94,c_41377])).

tff(c_41402,plain,(
    ! [D_2602] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_2602) = k7_relat_1('#skF_7',D_2602) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_41391])).

tff(c_40411,plain,(
    ! [A_2540,B_2541,C_2542,D_2543] :
      ( k2_partfun1(A_2540,B_2541,C_2542,D_2543) = k7_relat_1(C_2542,D_2543)
      | ~ m1_subset_1(C_2542,k1_zfmisc_1(k2_zfmisc_1(A_2540,B_2541)))
      | ~ v1_funct_1(C_2542) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_40425,plain,(
    ! [D_2543] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_2543) = k7_relat_1('#skF_7',D_2543)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_94,c_40411])).

tff(c_40436,plain,(
    ! [D_2543] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_2543) = k7_relat_1('#skF_7',D_2543) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_40425])).

tff(c_41024,plain,(
    ! [A_2575,B_2576,C_2577,D_2578] :
      ( m1_subset_1(k2_partfun1(A_2575,B_2576,C_2577,D_2578),k1_zfmisc_1(k2_zfmisc_1(A_2575,B_2576)))
      | ~ m1_subset_1(C_2577,k1_zfmisc_1(k2_zfmisc_1(A_2575,B_2576)))
      | ~ v1_funct_1(C_2577) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_41076,plain,(
    ! [D_2543] :
      ( m1_subset_1(k7_relat_1('#skF_7',D_2543),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_6')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_6')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40436,c_41024])).

tff(c_41251,plain,(
    ! [D_2594] : m1_subset_1(k7_relat_1('#skF_7',D_2594),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94,c_41076])).

tff(c_41289,plain,(
    ! [D_2594] :
      ( v1_relat_1(k7_relat_1('#skF_7',D_2594))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_41251,c_28])).

tff(c_41317,plain,(
    ! [D_2594] : v1_relat_1(k7_relat_1('#skF_7',D_2594)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_41289])).

tff(c_40207,plain,(
    ! [C_2522,A_2523,B_2524] :
      ( m1_subset_1(C_2522,k1_zfmisc_1(k2_zfmisc_1(A_2523,B_2524)))
      | ~ r1_tarski(k2_relat_1(C_2522),B_2524)
      | ~ r1_tarski(k1_relat_1(C_2522),A_2523)
      | ~ v1_relat_1(C_2522) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_36799,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_40262,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_5')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(resolution,[status(thm)],[c_40207,c_36799])).

tff(c_40343,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40262])).

tff(c_40437,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40436,c_40343])).

tff(c_41322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41317,c_40437])).

tff(c_41323,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_4')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_40262])).

tff(c_41517,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_4')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41402,c_41402,c_41323])).

tff(c_41518,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_41517])).

tff(c_41524,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_7','#skF_4'),'#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_41518])).

tff(c_41531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_39215,c_39633,c_41524])).

tff(c_41533,plain,(
    r1_tarski(k2_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_41517])).

tff(c_41546,plain,
    ( k2_relat_1(k7_relat_1('#skF_7','#skF_4')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_relat_1(k7_relat_1('#skF_7','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_41533,c_8])).

tff(c_41568,plain,(
    k2_relat_1(k7_relat_1('#skF_7','#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39215,c_41546])).

tff(c_41324,plain,(
    v1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40262])).

tff(c_41403,plain,(
    v1_relat_1(k7_relat_1('#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41402,c_41324])).

tff(c_56,plain,(
    ! [C_54,A_52,B_53] :
      ( m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ r1_tarski(k2_relat_1(C_54),B_53)
      | ~ r1_tarski(k1_relat_1(C_54),A_52)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_41407,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41402,c_36799])).

tff(c_41423,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_5')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_41407])).

tff(c_41429,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_5')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41403,c_41423])).

tff(c_41697,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39215,c_41568,c_41429])).

tff(c_41700,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_39073,c_41697])).

tff(c_41709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_12,c_41700])).

tff(c_41711,plain,(
    m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_42509,plain,(
    ! [C_2683,A_2684,B_2685] :
      ( v1_xboole_0(C_2683)
      | ~ m1_subset_1(C_2683,k1_zfmisc_1(k2_zfmisc_1(A_2684,B_2685)))
      | ~ v1_xboole_0(A_2684) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42526,plain,
    ( v1_xboole_0(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_41711,c_42509])).

tff(c_42538,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42526])).

tff(c_41794,plain,(
    ! [C_2640,B_2641,A_2642] :
      ( ~ v1_xboole_0(C_2640)
      | ~ m1_subset_1(B_2641,k1_zfmisc_1(C_2640))
      | ~ r2_hidden(A_2642,B_2641) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42106,plain,(
    ! [B_2656,A_2657,A_2658] :
      ( ~ v1_xboole_0(B_2656)
      | ~ r2_hidden(A_2657,A_2658)
      | ~ r1_tarski(A_2658,B_2656) ) ),
    inference(resolution,[status(thm)],[c_24,c_41794])).

tff(c_42203,plain,(
    ! [B_2665,A_2666,B_2667] :
      ( ~ v1_xboole_0(B_2665)
      | ~ r1_tarski(A_2666,B_2665)
      | r1_tarski(A_2666,B_2667) ) ),
    inference(resolution,[status(thm)],[c_6,c_42106])).

tff(c_42232,plain,(
    ! [B_2668,B_2669] :
      ( ~ v1_xboole_0(B_2668)
      | r1_tarski(B_2668,B_2669) ) ),
    inference(resolution,[status(thm)],[c_12,c_42203])).

tff(c_42275,plain,(
    ! [B_2670] :
      ( k1_xboole_0 = B_2670
      | ~ v1_xboole_0(B_2670) ) ),
    inference(resolution,[status(thm)],[c_42232,c_1380])).

tff(c_42285,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36136,c_42275])).

tff(c_42288,plain,(
    ! [A_9] : '#skF_2'(A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_42275])).

tff(c_42339,plain,(
    ! [A_9] : '#skF_2'(A_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42285,c_42288])).

tff(c_42348,plain,(
    ! [A_9] : m1_subset_1('#skF_5',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42339,c_18])).

tff(c_64,plain,(
    ! [A_59] :
      ( v1_funct_2(k1_xboole_0,A_59,k1_xboole_0)
      | k1_xboole_0 = A_59
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_59,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_42671,plain,(
    ! [A_59] :
      ( v1_funct_2('#skF_5',A_59,'#skF_5')
      | A_59 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42348,c_42285,c_42285,c_42285,c_42285,c_42285,c_64])).

tff(c_42426,plain,(
    ! [C_2678,B_2679,A_2680] :
      ( v1_xboole_0(C_2678)
      | ~ m1_subset_1(C_2678,k1_zfmisc_1(k2_zfmisc_1(B_2679,A_2680)))
      | ~ v1_xboole_0(A_2680) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42429,plain,
    ( v1_xboole_0(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_41711,c_42426])).

tff(c_42439,plain,(
    v1_xboole_0(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36136,c_42429])).

tff(c_42271,plain,(
    ! [B_2668] :
      ( k1_xboole_0 = B_2668
      | ~ v1_xboole_0(B_2668) ) ),
    inference(resolution,[status(thm)],[c_42232,c_1380])).

tff(c_42289,plain,(
    ! [B_2668] :
      ( B_2668 = '#skF_5'
      | ~ v1_xboole_0(B_2668) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42285,c_42271])).

tff(c_42738,plain,(
    k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42439,c_42289])).

tff(c_41710,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_42771,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42738,c_41710])).

tff(c_42786,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42671,c_42771])).

tff(c_42809,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42786,c_36136])).

tff(c_42812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42538,c_42809])).

tff(c_42813,plain,(
    v1_xboole_0(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_42526])).

tff(c_42814,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_42526])).

tff(c_42818,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42814,c_42289])).

tff(c_42821,plain,(
    ! [B_2668] :
      ( B_2668 = '#skF_4'
      | ~ v1_xboole_0(B_2668) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42818,c_42289])).

tff(c_43253,plain,(
    k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42813,c_42821])).

tff(c_1282,plain,(
    v1_funct_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_43300,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43253,c_1282])).

tff(c_138,plain,(
    ! [A_87,B_88] :
      ( v1_relat_1(A_87)
      | ~ v1_relat_1(B_88)
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_24,c_122])).

tff(c_161,plain,
    ( v1_relat_1(k7_relset_1('#skF_3','#skF_6','#skF_7','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_138])).

tff(c_1467,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_1490,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1339])).

tff(c_9412,plain,(
    ! [A_747,B_748,C_749] :
      ( k1_relset_1(A_747,B_748,C_749) = k1_relat_1(C_749)
      | ~ m1_subset_1(C_749,k1_zfmisc_1(k2_zfmisc_1(A_747,B_748))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_9431,plain,(
    k1_relset_1('#skF_3','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_9412])).

tff(c_12304,plain,(
    ! [B_892,A_893,C_894] :
      ( k1_xboole_0 = B_892
      | k1_relset_1(A_893,B_892,C_894) = A_893
      | ~ v1_funct_2(C_894,A_893,B_892)
      | ~ m1_subset_1(C_894,k1_zfmisc_1(k2_zfmisc_1(A_893,B_892))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_12339,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_3','#skF_6','#skF_7') = '#skF_3'
    | ~ v1_funct_2('#skF_7','#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_12304])).

tff(c_12348,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_9431,c_12339])).

tff(c_12349,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12348])).

tff(c_8587,plain,(
    ! [C_677,A_678,B_679] :
      ( v4_relat_1(C_677,A_678)
      | ~ m1_subset_1(C_677,k1_zfmisc_1(k2_zfmisc_1(A_678,B_679))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8600,plain,(
    v4_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_8587])).

tff(c_8604,plain,
    ( k7_relat_1('#skF_7','#skF_3') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_8600,c_38])).

tff(c_8607,plain,(
    k7_relat_1('#skF_7','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_8604])).

tff(c_8614,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_3')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_8607,c_40])).

tff(c_8620,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_8614])).

tff(c_8630,plain,
    ( k1_relat_1('#skF_7') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_8620,c_8])).

tff(c_8669,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_8630])).

tff(c_12351,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12349,c_8669])).

tff(c_12355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12351])).

tff(c_12356,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12348])).

tff(c_12404,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12356,c_1349])).

tff(c_12408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_12404])).

tff(c_12409,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8630])).

tff(c_12910,plain,(
    ! [B_939,A_940] :
      ( k1_relat_1(k7_relat_1(B_939,A_940)) = A_940
      | ~ r1_tarski(A_940,k1_relat_1(B_939))
      | ~ v1_relat_1(B_939) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12920,plain,(
    ! [A_940] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_940)) = A_940
      | ~ r1_tarski(A_940,'#skF_3')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12409,c_12910])).

tff(c_12944,plain,(
    ! [A_940] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_940)) = A_940
      | ~ r1_tarski(A_940,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_12920])).

tff(c_15501,plain,(
    ! [A_1084,B_1085,C_1086,D_1087] :
      ( k2_partfun1(A_1084,B_1085,C_1086,D_1087) = k7_relat_1(C_1086,D_1087)
      | ~ m1_subset_1(C_1086,k1_zfmisc_1(k2_zfmisc_1(A_1084,B_1085)))
      | ~ v1_funct_1(C_1086) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_15525,plain,(
    ! [D_1087] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_1087) = k7_relat_1('#skF_7',D_1087)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_94,c_15501])).

tff(c_15535,plain,(
    ! [D_1087] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_1087) = k7_relat_1('#skF_7',D_1087) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_15525])).

tff(c_2331,plain,(
    ! [A_309,B_310,C_311] :
      ( k1_relset_1(A_309,B_310,C_311) = k1_relat_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2346,plain,(
    k1_relset_1('#skF_3','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_2331])).

tff(c_3728,plain,(
    ! [B_419,A_420,C_421] :
      ( k1_xboole_0 = B_419
      | k1_relset_1(A_420,B_419,C_421) = A_420
      | ~ v1_funct_2(C_421,A_420,B_419)
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(A_420,B_419))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_3751,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_3','#skF_6','#skF_7') = '#skF_3'
    | ~ v1_funct_2('#skF_7','#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_3728])).

tff(c_3760,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2346,c_3751])).

tff(c_3761,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3760])).

tff(c_1763,plain,(
    ! [C_260,A_261,B_262] :
      ( v4_relat_1(C_260,A_261)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1776,plain,(
    v4_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_1763])).

tff(c_1780,plain,
    ( k7_relat_1('#skF_7','#skF_3') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1776,c_38])).

tff(c_1783,plain,(
    k7_relat_1('#skF_7','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_1780])).

tff(c_1809,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_3')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1783,c_40])).

tff(c_1815,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_1809])).

tff(c_1826,plain,
    ( k1_relat_1('#skF_7') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1815,c_8])).

tff(c_1912,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1826])).

tff(c_3763,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3761,c_1912])).

tff(c_3767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3763])).

tff(c_3768,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3760])).

tff(c_3811,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3768,c_1349])).

tff(c_3815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_3811])).

tff(c_3816,plain,(
    k1_relat_1('#skF_7') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1826])).

tff(c_3942,plain,(
    ! [B_435,A_436] :
      ( k1_relat_1(k7_relat_1(B_435,A_436)) = A_436
      | ~ r1_tarski(A_436,k1_relat_1(B_435))
      | ~ v1_relat_1(B_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3948,plain,(
    ! [A_436] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_436)) = A_436
      | ~ r1_tarski(A_436,'#skF_3')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3816,c_3942])).

tff(c_3979,plain,(
    ! [A_436] :
      ( k1_relat_1(k7_relat_1('#skF_7',A_436)) = A_436
      | ~ r1_tarski(A_436,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_3948])).

tff(c_8011,plain,(
    ! [A_650,B_651,C_652,D_653] :
      ( k2_partfun1(A_650,B_651,C_652,D_653) = k7_relat_1(C_652,D_653)
      | ~ m1_subset_1(C_652,k1_zfmisc_1(k2_zfmisc_1(A_650,B_651)))
      | ~ v1_funct_1(C_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_8029,plain,(
    ! [D_653] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_653) = k7_relat_1('#skF_7',D_653)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_94,c_8011])).

tff(c_8040,plain,(
    ! [D_653] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_653) = k7_relat_1('#skF_7',D_653) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_8029])).

tff(c_4843,plain,(
    ! [A_513,B_514,C_515,D_516] :
      ( k7_relset_1(A_513,B_514,C_515,D_516) = k9_relat_1(C_515,D_516)
      | ~ m1_subset_1(C_515,k1_zfmisc_1(k2_zfmisc_1(A_513,B_514))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4855,plain,(
    ! [D_516] : k7_relset_1('#skF_3','#skF_6','#skF_7',D_516) = k9_relat_1('#skF_7',D_516) ),
    inference(resolution,[status(thm)],[c_94,c_4843])).

tff(c_5027,plain,(
    r1_tarski(k9_relat_1('#skF_7','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4855,c_90])).

tff(c_7912,plain,(
    ! [A_641,B_642,C_643,D_644] :
      ( k2_partfun1(A_641,B_642,C_643,D_644) = k7_relat_1(C_643,D_644)
      | ~ m1_subset_1(C_643,k1_zfmisc_1(k2_zfmisc_1(A_641,B_642)))
      | ~ v1_funct_1(C_643) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_7932,plain,(
    ! [D_644] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_644) = k7_relat_1('#skF_7',D_644)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_94,c_7912])).

tff(c_7943,plain,(
    ! [D_644] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_644) = k7_relat_1('#skF_7',D_644) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_7932])).

tff(c_6431,plain,(
    ! [A_584,B_585,C_586,D_587] :
      ( k2_partfun1(A_584,B_585,C_586,D_587) = k7_relat_1(C_586,D_587)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_zfmisc_1(A_584,B_585)))
      | ~ v1_funct_1(C_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_6451,plain,(
    ! [D_587] :
      ( k2_partfun1('#skF_3','#skF_6','#skF_7',D_587) = k7_relat_1('#skF_7',D_587)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_94,c_6431])).

tff(c_6462,plain,(
    ! [D_587] : k2_partfun1('#skF_3','#skF_6','#skF_7',D_587) = k7_relat_1('#skF_7',D_587) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_6451])).

tff(c_7496,plain,(
    ! [A_627,B_628,C_629,D_630] :
      ( m1_subset_1(k2_partfun1(A_627,B_628,C_629,D_630),k1_zfmisc_1(k2_zfmisc_1(A_627,B_628)))
      | ~ m1_subset_1(C_629,k1_zfmisc_1(k2_zfmisc_1(A_627,B_628)))
      | ~ v1_funct_1(C_629) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_7546,plain,(
    ! [D_587] :
      ( m1_subset_1(k7_relat_1('#skF_7',D_587),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_6')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_6')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6462,c_7496])).

tff(c_7576,plain,(
    ! [D_631] : m1_subset_1(k7_relat_1('#skF_7',D_631),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94,c_7546])).

tff(c_7611,plain,(
    ! [D_631] :
      ( v1_relat_1(k7_relat_1('#skF_7',D_631))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_7576,c_28])).

tff(c_7635,plain,(
    ! [D_631] : v1_relat_1(k7_relat_1('#skF_7',D_631)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7611])).

tff(c_5921,plain,(
    ! [C_568,A_569,B_570] :
      ( m1_subset_1(C_568,k1_zfmisc_1(k2_zfmisc_1(A_569,B_570)))
      | ~ r1_tarski(k2_relat_1(C_568),B_570)
      | ~ r1_tarski(k1_relat_1(C_568),A_569)
      | ~ v1_relat_1(C_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1560,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_5970,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_5')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(resolution,[status(thm)],[c_5921,c_1560])).

tff(c_6174,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5970])).

tff(c_6500,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6462,c_6174])).

tff(c_7642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7635,c_6500])).

tff(c_7643,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_4')
    | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5970])).

tff(c_7645,plain,(
    ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7643])).

tff(c_7995,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7943,c_7645])).

tff(c_8001,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_7','#skF_4'),'#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_7995])).

tff(c_8008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_5027,c_8001])).

tff(c_8009,plain,(
    ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_7643])).

tff(c_8440,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_7','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8040,c_8009])).

tff(c_8443,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3979,c_8440])).

tff(c_8452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_12,c_8443])).

tff(c_8453,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_15548,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_7','#skF_4'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15535,c_8453])).

tff(c_8454,plain,(
    m1_subset_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_13181,plain,(
    ! [A_965,B_966,C_967] :
      ( k1_relset_1(A_965,B_966,C_967) = k1_relat_1(C_967)
      | ~ m1_subset_1(C_967,k1_zfmisc_1(k2_zfmisc_1(A_965,B_966))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_13198,plain,(
    k1_relset_1('#skF_4','#skF_5',k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) = k1_relat_1(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8454,c_13181])).

tff(c_15542,plain,(
    k1_relset_1('#skF_4','#skF_5',k7_relat_1('#skF_7','#skF_4')) = k1_relat_1(k7_relat_1('#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15535,c_15535,c_13198])).

tff(c_15547,plain,(
    m1_subset_1(k7_relat_1('#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15535,c_8454])).

tff(c_15838,plain,(
    ! [B_1096,C_1097,A_1098] :
      ( k1_xboole_0 = B_1096
      | v1_funct_2(C_1097,A_1098,B_1096)
      | k1_relset_1(A_1098,B_1096,C_1097) != A_1098
      | ~ m1_subset_1(C_1097,k1_zfmisc_1(k2_zfmisc_1(A_1098,B_1096))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_15841,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2(k7_relat_1('#skF_7','#skF_4'),'#skF_4','#skF_5')
    | k1_relset_1('#skF_4','#skF_5',k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_15547,c_15838])).

tff(c_15878,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2(k7_relat_1('#skF_7','#skF_4'),'#skF_4','#skF_5')
    | k1_relat_1(k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15542,c_15841])).

tff(c_15879,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1(k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_15548,c_15878])).

tff(c_15889,plain,(
    k1_relat_1(k7_relat_1('#skF_7','#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_15879])).

tff(c_15892,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12944,c_15889])).

tff(c_15896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_15892])).

tff(c_15897,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_15879])).

tff(c_15946,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15897,c_1349])).

tff(c_15950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1490,c_15946])).

tff(c_15952,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1339])).

tff(c_16658,plain,(
    ! [C_1156,B_1157,A_1158] :
      ( ~ v1_xboole_0(C_1156)
      | ~ m1_subset_1(B_1157,k1_zfmisc_1(C_1156))
      | ~ r2_hidden(A_1158,B_1157) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16911,plain,(
    ! [B_1170,A_1171,A_1172] :
      ( ~ v1_xboole_0(B_1170)
      | ~ r2_hidden(A_1171,A_1172)
      | ~ r1_tarski(A_1172,B_1170) ) ),
    inference(resolution,[status(thm)],[c_24,c_16658])).

tff(c_16920,plain,(
    ! [B_1177,A_1178,B_1179] :
      ( ~ v1_xboole_0(B_1177)
      | ~ r1_tarski(A_1178,B_1177)
      | r1_tarski(A_1178,B_1179) ) ),
    inference(resolution,[status(thm)],[c_6,c_16911])).

tff(c_16946,plain,(
    ! [B_1180,B_1181] :
      ( ~ v1_xboole_0(B_1180)
      | r1_tarski(B_1180,B_1181) ) ),
    inference(resolution,[status(thm)],[c_12,c_16920])).

tff(c_16976,plain,(
    ! [B_1182] :
      ( k1_xboole_0 = B_1182
      | ~ v1_xboole_0(B_1182) ) ),
    inference(resolution,[status(thm)],[c_16946,c_1380])).

tff(c_16986,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_15952,c_16976])).

tff(c_163,plain,(
    ! [A_8] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_1284,plain,(
    ! [A_8] : ~ v1_relat_1(A_8) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_1290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1284,c_135])).

tff(c_1291,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_17003,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16986,c_1291])).

tff(c_17007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1467,c_17003])).

tff(c_17009,plain,(
    v1_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_42834,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42818,c_17009])).

tff(c_42307,plain,(
    ! [A_8] : r1_tarski('#skF_5',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42285,c_14])).

tff(c_42825,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42818,c_42307])).

tff(c_41722,plain,(
    ! [C_2621,B_2622,A_2623] :
      ( v5_relat_1(C_2621,B_2622)
      | ~ m1_subset_1(C_2621,k1_zfmisc_1(k2_zfmisc_1(A_2623,B_2622))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_41746,plain,(
    ! [A_2629,B_2630,A_2631] :
      ( v5_relat_1(A_2629,B_2630)
      | ~ r1_tarski(A_2629,k2_zfmisc_1(A_2631,B_2630)) ) ),
    inference(resolution,[status(thm)],[c_24,c_41722])).

tff(c_41772,plain,(
    ! [B_2630] : v5_relat_1(k1_xboole_0,B_2630) ),
    inference(resolution,[status(thm)],[c_14,c_41746])).

tff(c_41975,plain,(
    ! [B_2650,A_2651] :
      ( r1_tarski(k2_relat_1(B_2650),A_2651)
      | ~ v5_relat_1(B_2650,A_2651)
      | ~ v1_relat_1(B_2650) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42111,plain,(
    ! [B_2661] :
      ( k2_relat_1(B_2661) = k1_xboole_0
      | ~ v5_relat_1(B_2661,k1_xboole_0)
      | ~ v1_relat_1(B_2661) ) ),
    inference(resolution,[status(thm)],[c_41975,c_1380])).

tff(c_42123,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_41772,c_42111])).

tff(c_42134,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_42123])).

tff(c_42292,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42285,c_42285,c_42134])).

tff(c_42824,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42818,c_42818,c_42292])).

tff(c_42473,plain,(
    ! [A_2682] : m1_subset_1('#skF_5',k1_zfmisc_1(A_2682)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42339,c_18])).

tff(c_46,plain,(
    ! [C_36,A_34,B_35] :
      ( v4_relat_1(C_36,A_34)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42499,plain,(
    ! [A_34] : v4_relat_1('#skF_5',A_34) ),
    inference(resolution,[status(thm)],[c_42473,c_46])).

tff(c_42871,plain,(
    ! [A_2711] : v4_relat_1('#skF_4',A_2711) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42818,c_42499])).

tff(c_42874,plain,(
    ! [A_2711] :
      ( k7_relat_1('#skF_4',A_2711) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42871,c_38])).

tff(c_43024,plain,(
    ! [A_2718] : k7_relat_1('#skF_4',A_2718) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42834,c_42874])).

tff(c_43032,plain,(
    ! [A_2718] :
      ( r1_tarski(k1_relat_1('#skF_4'),A_2718)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43024,c_40])).

tff(c_43039,plain,(
    ! [A_2718] : r1_tarski(k1_relat_1('#skF_4'),A_2718) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42834,c_43032])).

tff(c_1374,plain,(
    ! [A_9] :
      ( '#skF_2'(A_9) = A_9
      | ~ r1_tarski(A_9,'#skF_2'(A_9)) ) ),
    inference(resolution,[status(thm)],[c_120,c_1357])).

tff(c_42345,plain,(
    ! [A_9] :
      ( A_9 = '#skF_5'
      | ~ r1_tarski(A_9,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42339,c_42339,c_1374])).

tff(c_43105,plain,(
    ! [A_2727] :
      ( A_2727 = '#skF_4'
      | ~ r1_tarski(A_2727,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42818,c_42818,c_42345])).

tff(c_43130,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_43039,c_43105])).

tff(c_84,plain,(
    ! [B_71,A_70] :
      ( v1_funct_2(B_71,k1_relat_1(B_71),A_70)
      | ~ r1_tarski(k2_relat_1(B_71),A_70)
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_43146,plain,(
    ! [A_70] :
      ( v1_funct_2('#skF_4','#skF_4',A_70)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_70)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43130,c_84])).

tff(c_43153,plain,(
    ! [A_70] :
      ( v1_funct_2('#skF_4','#skF_4',A_70)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42834,c_42825,c_42824,c_43146])).

tff(c_43350,plain,(
    ! [A_70] : v1_funct_2('#skF_4','#skF_4',A_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43300,c_43153])).

tff(c_42831,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42818,c_41710])).

tff(c_43297,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43253,c_42831])).

tff(c_43353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43350,c_43297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.16/5.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.55/5.24  
% 12.55/5.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.55/5.24  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 12.55/5.24  
% 12.55/5.24  %Foreground sorts:
% 12.55/5.24  
% 12.55/5.24  
% 12.55/5.24  %Background operators:
% 12.55/5.24  
% 12.55/5.24  
% 12.55/5.24  %Foreground operators:
% 12.55/5.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.55/5.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 12.55/5.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.55/5.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.55/5.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.55/5.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.55/5.24  tff('#skF_7', type, '#skF_7': $i).
% 12.55/5.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.55/5.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.55/5.24  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 12.55/5.24  tff('#skF_5', type, '#skF_5': $i).
% 12.55/5.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.55/5.24  tff('#skF_6', type, '#skF_6': $i).
% 12.55/5.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.55/5.24  tff('#skF_3', type, '#skF_3': $i).
% 12.55/5.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.55/5.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.55/5.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.55/5.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.55/5.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.55/5.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.55/5.24  tff('#skF_4', type, '#skF_4': $i).
% 12.55/5.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.55/5.24  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 12.55/5.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.55/5.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.55/5.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.55/5.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.55/5.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.55/5.24  
% 12.55/5.28  tff(f_219, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 12.55/5.28  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.55/5.28  tff(f_78, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.55/5.28  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.55/5.28  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.55/5.28  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.55/5.28  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 12.55/5.28  tff(f_172, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 12.55/5.28  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.55/5.28  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 12.55/5.29  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 12.55/5.29  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.55/5.29  tff(f_45, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 12.55/5.29  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 12.55/5.29  tff(f_186, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 12.55/5.29  tff(f_126, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 12.55/5.29  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 12.55/5.29  tff(f_180, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 12.55/5.29  tff(f_134, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 12.55/5.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.55/5.29  tff(f_63, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 12.55/5.29  tff(f_111, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 12.55/5.29  tff(f_118, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 12.55/5.29  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 12.55/5.29  tff(f_198, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 12.55/5.29  tff(c_92, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.55/5.29  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.55/5.29  tff(c_34, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.55/5.29  tff(c_94, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.55/5.29  tff(c_122, plain, (![B_84, A_85]: (v1_relat_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.55/5.29  tff(c_128, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_6'))), inference(resolution, [status(thm)], [c_94, c_122])).
% 12.55/5.29  tff(c_135, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_128])).
% 12.55/5.29  tff(c_100, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.55/5.29  tff(c_96, plain, (v1_funct_2('#skF_7', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.55/5.29  tff(c_37666, plain, (![A_2319, B_2320, C_2321]: (k1_relset_1(A_2319, B_2320, C_2321)=k1_relat_1(C_2321) | ~m1_subset_1(C_2321, k1_zfmisc_1(k2_zfmisc_1(A_2319, B_2320))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.55/5.29  tff(c_37675, plain, (k1_relset_1('#skF_3', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_94, c_37666])).
% 12.55/5.29  tff(c_90, plain, (r1_tarski(k7_relset_1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.55/5.29  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.55/5.29  tff(c_1293, plain, (![B_210, A_211]: (v1_xboole_0(B_210) | ~m1_subset_1(B_210, k1_zfmisc_1(A_211)) | ~v1_xboole_0(A_211))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.55/5.29  tff(c_1313, plain, (![A_214, B_215]: (v1_xboole_0(A_214) | ~v1_xboole_0(B_215) | ~r1_tarski(A_214, B_215))), inference(resolution, [status(thm)], [c_24, c_1293])).
% 12.55/5.29  tff(c_1339, plain, (v1_xboole_0(k7_relset_1('#skF_3', '#skF_6', '#skF_7', '#skF_4')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_90, c_1313])).
% 12.55/5.29  tff(c_17010, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1339])).
% 12.55/5.29  tff(c_27755, plain, (![A_1819, B_1820, C_1821]: (k1_relset_1(A_1819, B_1820, C_1821)=k1_relat_1(C_1821) | ~m1_subset_1(C_1821, k1_zfmisc_1(k2_zfmisc_1(A_1819, B_1820))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.55/5.29  tff(c_27774, plain, (k1_relset_1('#skF_3', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_94, c_27755])).
% 12.55/5.29  tff(c_31835, plain, (![B_1974, A_1975, C_1976]: (k1_xboole_0=B_1974 | k1_relset_1(A_1975, B_1974, C_1976)=A_1975 | ~v1_funct_2(C_1976, A_1975, B_1974) | ~m1_subset_1(C_1976, k1_zfmisc_1(k2_zfmisc_1(A_1975, B_1974))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 12.55/5.29  tff(c_31879, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_3', '#skF_6', '#skF_7')='#skF_3' | ~v1_funct_2('#skF_7', '#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_94, c_31835])).
% 12.55/5.29  tff(c_31890, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_27774, c_31879])).
% 12.55/5.29  tff(c_31891, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_31890])).
% 12.55/5.29  tff(c_26957, plain, (![C_1743, A_1744, B_1745]: (v4_relat_1(C_1743, A_1744) | ~m1_subset_1(C_1743, k1_zfmisc_1(k2_zfmisc_1(A_1744, B_1745))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.55/5.29  tff(c_26975, plain, (v4_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_94, c_26957])).
% 12.55/5.29  tff(c_38, plain, (![B_29, A_28]: (k7_relat_1(B_29, A_28)=B_29 | ~v4_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.55/5.29  tff(c_26978, plain, (k7_relat_1('#skF_7', '#skF_3')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_26975, c_38])).
% 12.55/5.29  tff(c_26981, plain, (k7_relat_1('#skF_7', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_26978])).
% 12.55/5.29  tff(c_40, plain, (![B_31, A_30]: (r1_tarski(k1_relat_1(k7_relat_1(B_31, A_30)), A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.55/5.29  tff(c_27031, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_3') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_26981, c_40])).
% 12.55/5.29  tff(c_27037, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_27031])).
% 12.55/5.29  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.55/5.29  tff(c_27054, plain, (k1_relat_1('#skF_7')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_27037, c_8])).
% 12.55/5.29  tff(c_27134, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_27054])).
% 12.55/5.29  tff(c_31893, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31891, c_27134])).
% 12.55/5.29  tff(c_31897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_31893])).
% 12.55/5.29  tff(c_31898, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_31890])).
% 12.55/5.29  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.55/5.29  tff(c_1341, plain, (![A_8]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_8))), inference(resolution, [status(thm)], [c_14, c_1313])).
% 12.55/5.29  tff(c_1344, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitLeft, [status(thm)], [c_1341])).
% 12.55/5.29  tff(c_16, plain, (![A_9]: (v1_xboole_0('#skF_2'(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.55/5.29  tff(c_1348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1344, c_16])).
% 12.55/5.29  tff(c_1349, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_1341])).
% 12.55/5.29  tff(c_31955, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_31898, c_1349])).
% 12.55/5.29  tff(c_31959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_31955])).
% 12.55/5.29  tff(c_31960, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(splitRight, [status(thm)], [c_27054])).
% 12.55/5.29  tff(c_32349, plain, (![B_2016, A_2017]: (k1_relat_1(k7_relat_1(B_2016, A_2017))=A_2017 | ~r1_tarski(A_2017, k1_relat_1(B_2016)) | ~v1_relat_1(B_2016))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.55/5.29  tff(c_32365, plain, (![A_2017]: (k1_relat_1(k7_relat_1('#skF_7', A_2017))=A_2017 | ~r1_tarski(A_2017, '#skF_3') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_31960, c_32349])).
% 12.55/5.29  tff(c_32400, plain, (![A_2017]: (k1_relat_1(k7_relat_1('#skF_7', A_2017))=A_2017 | ~r1_tarski(A_2017, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_32365])).
% 12.55/5.29  tff(c_98, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.55/5.29  tff(c_35693, plain, (![A_2169, B_2170, C_2171, D_2172]: (k2_partfun1(A_2169, B_2170, C_2171, D_2172)=k7_relat_1(C_2171, D_2172) | ~m1_subset_1(C_2171, k1_zfmisc_1(k2_zfmisc_1(A_2169, B_2170))) | ~v1_funct_1(C_2171))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.55/5.29  tff(c_35719, plain, (![D_2172]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_2172)=k7_relat_1('#skF_7', D_2172) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_94, c_35693])).
% 12.55/5.29  tff(c_35729, plain, (![D_2172]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_2172)=k7_relat_1('#skF_7', D_2172))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_35719])).
% 12.55/5.29  tff(c_17902, plain, (![A_1272, B_1273, C_1274]: (k1_relset_1(A_1272, B_1273, C_1274)=k1_relat_1(C_1274) | ~m1_subset_1(C_1274, k1_zfmisc_1(k2_zfmisc_1(A_1272, B_1273))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.55/5.29  tff(c_17917, plain, (k1_relset_1('#skF_3', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_94, c_17902])).
% 12.55/5.29  tff(c_20033, plain, (![B_1402, A_1403, C_1404]: (k1_xboole_0=B_1402 | k1_relset_1(A_1403, B_1402, C_1404)=A_1403 | ~v1_funct_2(C_1404, A_1403, B_1402) | ~m1_subset_1(C_1404, k1_zfmisc_1(k2_zfmisc_1(A_1403, B_1402))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 12.55/5.29  tff(c_20065, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_3', '#skF_6', '#skF_7')='#skF_3' | ~v1_funct_2('#skF_7', '#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_94, c_20033])).
% 12.55/5.29  tff(c_20074, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_17917, c_20065])).
% 12.55/5.29  tff(c_20075, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_20074])).
% 12.55/5.29  tff(c_17219, plain, (![C_1205, A_1206, B_1207]: (v4_relat_1(C_1205, A_1206) | ~m1_subset_1(C_1205, k1_zfmisc_1(k2_zfmisc_1(A_1206, B_1207))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.55/5.29  tff(c_17232, plain, (v4_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_94, c_17219])).
% 12.55/5.29  tff(c_17236, plain, (k7_relat_1('#skF_7', '#skF_3')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_17232, c_38])).
% 12.55/5.29  tff(c_17239, plain, (k7_relat_1('#skF_7', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_17236])).
% 12.55/5.29  tff(c_17246, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_3') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_17239, c_40])).
% 12.55/5.29  tff(c_17252, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_17246])).
% 12.55/5.29  tff(c_17262, plain, (k1_relat_1('#skF_7')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_17252, c_8])).
% 12.55/5.29  tff(c_17275, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_17262])).
% 12.55/5.29  tff(c_20077, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20075, c_17275])).
% 12.55/5.29  tff(c_20081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_20077])).
% 12.55/5.29  tff(c_20082, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_20074])).
% 12.55/5.29  tff(c_20129, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20082, c_1349])).
% 12.55/5.29  tff(c_20133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_20129])).
% 12.55/5.29  tff(c_20134, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(splitRight, [status(thm)], [c_17262])).
% 12.55/5.29  tff(c_20680, plain, (![B_1461, A_1462]: (k1_relat_1(k7_relat_1(B_1461, A_1462))=A_1462 | ~r1_tarski(A_1462, k1_relat_1(B_1461)) | ~v1_relat_1(B_1461))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.55/5.29  tff(c_20690, plain, (![A_1462]: (k1_relat_1(k7_relat_1('#skF_7', A_1462))=A_1462 | ~r1_tarski(A_1462, '#skF_3') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_20134, c_20680])).
% 12.55/5.29  tff(c_20714, plain, (![A_1462]: (k1_relat_1(k7_relat_1('#skF_7', A_1462))=A_1462 | ~r1_tarski(A_1462, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_20690])).
% 12.55/5.29  tff(c_26538, plain, (![A_1711, B_1712, C_1713, D_1714]: (k2_partfun1(A_1711, B_1712, C_1713, D_1714)=k7_relat_1(C_1713, D_1714) | ~m1_subset_1(C_1713, k1_zfmisc_1(k2_zfmisc_1(A_1711, B_1712))) | ~v1_funct_1(C_1713))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.55/5.29  tff(c_26564, plain, (![D_1714]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_1714)=k7_relat_1('#skF_7', D_1714) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_94, c_26538])).
% 12.55/5.29  tff(c_26575, plain, (![D_1714]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_1714)=k7_relat_1('#skF_7', D_1714))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_26564])).
% 12.55/5.29  tff(c_21719, plain, (![A_1541, B_1542, C_1543, D_1544]: (k7_relset_1(A_1541, B_1542, C_1543, D_1544)=k9_relat_1(C_1543, D_1544) | ~m1_subset_1(C_1543, k1_zfmisc_1(k2_zfmisc_1(A_1541, B_1542))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.55/5.29  tff(c_21733, plain, (![D_1544]: (k7_relset_1('#skF_3', '#skF_6', '#skF_7', D_1544)=k9_relat_1('#skF_7', D_1544))), inference(resolution, [status(thm)], [c_94, c_21719])).
% 12.55/5.29  tff(c_21743, plain, (r1_tarski(k9_relat_1('#skF_7', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21733, c_90])).
% 12.55/5.29  tff(c_36, plain, (![B_27, A_26]: (k2_relat_1(k7_relat_1(B_27, A_26))=k9_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.55/5.29  tff(c_26303, plain, (![A_1700, B_1701, C_1702, D_1703]: (k2_partfun1(A_1700, B_1701, C_1702, D_1703)=k7_relat_1(C_1702, D_1703) | ~m1_subset_1(C_1702, k1_zfmisc_1(k2_zfmisc_1(A_1700, B_1701))) | ~v1_funct_1(C_1702))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.55/5.29  tff(c_26329, plain, (![D_1703]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_1703)=k7_relat_1('#skF_7', D_1703) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_94, c_26303])).
% 12.55/5.29  tff(c_26340, plain, (![D_1703]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_1703)=k7_relat_1('#skF_7', D_1703))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_26329])).
% 12.55/5.29  tff(c_23768, plain, (![A_1624, B_1625, C_1626, D_1627]: (k2_partfun1(A_1624, B_1625, C_1626, D_1627)=k7_relat_1(C_1626, D_1627) | ~m1_subset_1(C_1626, k1_zfmisc_1(k2_zfmisc_1(A_1624, B_1625))) | ~v1_funct_1(C_1626))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.55/5.29  tff(c_23794, plain, (![D_1627]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_1627)=k7_relat_1('#skF_7', D_1627) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_94, c_23768])).
% 12.55/5.29  tff(c_23805, plain, (![D_1627]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_1627)=k7_relat_1('#skF_7', D_1627))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_23794])).
% 12.55/5.29  tff(c_26077, plain, (![A_1693, B_1694, C_1695, D_1696]: (m1_subset_1(k2_partfun1(A_1693, B_1694, C_1695, D_1696), k1_zfmisc_1(k2_zfmisc_1(A_1693, B_1694))) | ~m1_subset_1(C_1695, k1_zfmisc_1(k2_zfmisc_1(A_1693, B_1694))) | ~v1_funct_1(C_1695))), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.55/5.29  tff(c_26127, plain, (![D_1627]: (m1_subset_1(k7_relat_1('#skF_7', D_1627), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_6'))) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_23805, c_26077])).
% 12.55/5.29  tff(c_26167, plain, (![D_1697]: (m1_subset_1(k7_relat_1('#skF_7', D_1697), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_94, c_26127])).
% 12.55/5.29  tff(c_28, plain, (![B_21, A_19]: (v1_relat_1(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_19)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.55/5.29  tff(c_26205, plain, (![D_1697]: (v1_relat_1(k7_relat_1('#skF_7', D_1697)) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_6')))), inference(resolution, [status(thm)], [c_26167, c_28])).
% 12.55/5.29  tff(c_26233, plain, (![D_1697]: (v1_relat_1(k7_relat_1('#skF_7', D_1697)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26205])).
% 12.55/5.29  tff(c_23593, plain, (![C_1616, A_1617, B_1618]: (m1_subset_1(C_1616, k1_zfmisc_1(k2_zfmisc_1(A_1617, B_1618))) | ~r1_tarski(k2_relat_1(C_1616), B_1618) | ~r1_tarski(k1_relat_1(C_1616), A_1617) | ~v1_relat_1(C_1616))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.55/5.29  tff(c_1264, plain, (![A_204, B_205, C_206, D_207]: (v1_funct_1(k2_partfun1(A_204, B_205, C_206, D_207)) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_1(C_206))), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.55/5.29  tff(c_1272, plain, (![D_207]: (v1_funct_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_207)) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_94, c_1264])).
% 12.55/5.29  tff(c_1277, plain, (![D_207]: (v1_funct_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_207)))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1272])).
% 12.55/5.29  tff(c_88, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_4', '#skF_5') | ~v1_funct_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 12.55/5.29  tff(c_165, plain, (~v1_funct_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(splitLeft, [status(thm)], [c_88])).
% 12.55/5.29  tff(c_1280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1277, c_165])).
% 12.55/5.29  tff(c_1281, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_4', '#skF_5') | ~m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_88])).
% 12.55/5.29  tff(c_17191, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1281])).
% 12.55/5.29  tff(c_23650, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_5') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_23593, c_17191])).
% 12.55/5.29  tff(c_23725, plain, (~v1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(splitLeft, [status(thm)], [c_23650])).
% 12.55/5.29  tff(c_23806, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_23805, c_23725])).
% 12.55/5.29  tff(c_26242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26233, c_23806])).
% 12.55/5.29  tff(c_26243, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_4') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_5')), inference(splitRight, [status(thm)], [c_23650])).
% 12.55/5.29  tff(c_26245, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_5')), inference(splitLeft, [status(thm)], [c_26243])).
% 12.55/5.29  tff(c_26353, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26340, c_26245])).
% 12.55/5.29  tff(c_26473, plain, (~r1_tarski(k9_relat_1('#skF_7', '#skF_4'), '#skF_5') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36, c_26353])).
% 12.55/5.29  tff(c_26480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_21743, c_26473])).
% 12.55/5.29  tff(c_26481, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_4')), inference(splitRight, [status(thm)], [c_26243])).
% 12.55/5.29  tff(c_26702, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26575, c_26481])).
% 12.55/5.29  tff(c_26705, plain, (~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20714, c_26702])).
% 12.55/5.29  tff(c_26714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_12, c_26705])).
% 12.55/5.29  tff(c_26715, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1281])).
% 12.55/5.29  tff(c_35740, plain, (~v1_funct_2(k7_relat_1('#skF_7', '#skF_4'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_35729, c_26715])).
% 12.55/5.29  tff(c_26716, plain, (m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1281])).
% 12.55/5.29  tff(c_32912, plain, (![A_2051, B_2052, C_2053]: (k1_relset_1(A_2051, B_2052, C_2053)=k1_relat_1(C_2053) | ~m1_subset_1(C_2053, k1_zfmisc_1(k2_zfmisc_1(A_2051, B_2052))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.55/5.29  tff(c_32930, plain, (k1_relset_1('#skF_4', '#skF_5', k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))=k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_26716, c_32912])).
% 12.55/5.29  tff(c_35734, plain, (k1_relset_1('#skF_4', '#skF_5', k7_relat_1('#skF_7', '#skF_4'))=k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_35729, c_35729, c_32930])).
% 12.55/5.29  tff(c_35739, plain, (m1_subset_1(k7_relat_1('#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_35729, c_26716])).
% 12.55/5.29  tff(c_36005, plain, (![B_2179, C_2180, A_2181]: (k1_xboole_0=B_2179 | v1_funct_2(C_2180, A_2181, B_2179) | k1_relset_1(A_2181, B_2179, C_2180)!=A_2181 | ~m1_subset_1(C_2180, k1_zfmisc_1(k2_zfmisc_1(A_2181, B_2179))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 12.55/5.29  tff(c_36008, plain, (k1_xboole_0='#skF_5' | v1_funct_2(k7_relat_1('#skF_7', '#skF_4'), '#skF_4', '#skF_5') | k1_relset_1('#skF_4', '#skF_5', k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_35739, c_36005])).
% 12.55/5.29  tff(c_36048, plain, (k1_xboole_0='#skF_5' | v1_funct_2(k7_relat_1('#skF_7', '#skF_4'), '#skF_4', '#skF_5') | k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35734, c_36008])).
% 12.55/5.29  tff(c_36049, plain, (k1_xboole_0='#skF_5' | k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_35740, c_36048])).
% 12.55/5.29  tff(c_36059, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_36049])).
% 12.55/5.29  tff(c_36068, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32400, c_36059])).
% 12.55/5.29  tff(c_36077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_36068])).
% 12.55/5.29  tff(c_36078, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_36049])).
% 12.55/5.29  tff(c_36130, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36078, c_1349])).
% 12.55/5.29  tff(c_36134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17010, c_36130])).
% 12.55/5.29  tff(c_36136, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1339])).
% 12.55/5.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.55/5.29  tff(c_37094, plain, (![C_2276, B_2277, A_2278]: (~v1_xboole_0(C_2276) | ~m1_subset_1(B_2277, k1_zfmisc_1(C_2276)) | ~r2_hidden(A_2278, B_2277))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.55/5.29  tff(c_37492, plain, (![B_2307, A_2308, A_2309]: (~v1_xboole_0(B_2307) | ~r2_hidden(A_2308, A_2309) | ~r1_tarski(A_2309, B_2307))), inference(resolution, [status(thm)], [c_24, c_37094])).
% 12.55/5.29  tff(c_37496, plain, (![B_2310, A_2311, B_2312]: (~v1_xboole_0(B_2310) | ~r1_tarski(A_2311, B_2310) | r1_tarski(A_2311, B_2312))), inference(resolution, [status(thm)], [c_6, c_37492])).
% 12.55/5.29  tff(c_37532, plain, (![B_2314, B_2315]: (~v1_xboole_0(B_2314) | r1_tarski(B_2314, B_2315))), inference(resolution, [status(thm)], [c_12, c_37496])).
% 12.55/5.29  tff(c_1357, plain, (![B_218, A_219]: (B_218=A_219 | ~r1_tarski(B_218, A_219) | ~r1_tarski(A_219, B_218))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.55/5.29  tff(c_1380, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_1357])).
% 12.55/5.29  tff(c_37593, plain, (![B_2316]: (k1_xboole_0=B_2316 | ~v1_xboole_0(B_2316))), inference(resolution, [status(thm)], [c_37532, c_1380])).
% 12.55/5.29  tff(c_37603, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_36136, c_37593])).
% 12.55/5.29  tff(c_74, plain, (![B_60, A_59, C_61]: (k1_xboole_0=B_60 | k1_relset_1(A_59, B_60, C_61)=A_59 | ~v1_funct_2(C_61, A_59, B_60) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 12.55/5.29  tff(c_38447, plain, (![B_2390, A_2391, C_2392]: (B_2390='#skF_5' | k1_relset_1(A_2391, B_2390, C_2392)=A_2391 | ~v1_funct_2(C_2392, A_2391, B_2390) | ~m1_subset_1(C_2392, k1_zfmisc_1(k2_zfmisc_1(A_2391, B_2390))))), inference(demodulation, [status(thm), theory('equality')], [c_37603, c_74])).
% 12.55/5.29  tff(c_38464, plain, ('#skF_5'='#skF_6' | k1_relset_1('#skF_3', '#skF_6', '#skF_7')='#skF_3' | ~v1_funct_2('#skF_7', '#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_94, c_38447])).
% 12.55/5.29  tff(c_38472, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_7')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_37675, c_38464])).
% 12.55/5.29  tff(c_38473, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_38472])).
% 12.55/5.29  tff(c_36895, plain, (![C_2260, A_2261, B_2262]: (v4_relat_1(C_2260, A_2261) | ~m1_subset_1(C_2260, k1_zfmisc_1(k2_zfmisc_1(A_2261, B_2262))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.55/5.29  tff(c_36908, plain, (v4_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_94, c_36895])).
% 12.55/5.29  tff(c_36912, plain, (k7_relat_1('#skF_7', '#skF_3')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_36908, c_38])).
% 12.55/5.29  tff(c_36915, plain, (k7_relat_1('#skF_7', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_36912])).
% 12.55/5.29  tff(c_36919, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_3') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36915, c_40])).
% 12.55/5.29  tff(c_36923, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_36919])).
% 12.55/5.29  tff(c_36933, plain, (k1_relat_1('#skF_7')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_36923, c_8])).
% 12.55/5.29  tff(c_36945, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_36933])).
% 12.55/5.29  tff(c_38475, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38473, c_36945])).
% 12.55/5.29  tff(c_38479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_38475])).
% 12.55/5.29  tff(c_38480, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_38472])).
% 12.55/5.29  tff(c_38511, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38480, c_36136])).
% 12.55/5.29  tff(c_38514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_38511])).
% 12.55/5.29  tff(c_38515, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(splitRight, [status(thm)], [c_36933])).
% 12.55/5.29  tff(c_39035, plain, (![B_2436, A_2437]: (k1_relat_1(k7_relat_1(B_2436, A_2437))=A_2437 | ~r1_tarski(A_2437, k1_relat_1(B_2436)) | ~v1_relat_1(B_2436))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.55/5.29  tff(c_39045, plain, (![A_2437]: (k1_relat_1(k7_relat_1('#skF_7', A_2437))=A_2437 | ~r1_tarski(A_2437, '#skF_3') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_38515, c_39035])).
% 12.55/5.29  tff(c_39073, plain, (![A_2437]: (k1_relat_1(k7_relat_1('#skF_7', A_2437))=A_2437 | ~r1_tarski(A_2437, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_39045])).
% 12.55/5.29  tff(c_38701, plain, (![C_2406, B_2407, A_2408]: (~v1_xboole_0(C_2406) | ~m1_subset_1(B_2407, k1_zfmisc_1(C_2406)) | ~r2_hidden(A_2408, B_2407))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.55/5.29  tff(c_39031, plain, (![B_2433, A_2434, A_2435]: (~v1_xboole_0(B_2433) | ~r2_hidden(A_2434, A_2435) | ~r1_tarski(A_2435, B_2433))), inference(resolution, [status(thm)], [c_24, c_38701])).
% 12.55/5.29  tff(c_39079, plain, (![B_2438, A_2439, B_2440]: (~v1_xboole_0(B_2438) | ~r1_tarski(A_2439, B_2438) | r1_tarski(A_2439, B_2440))), inference(resolution, [status(thm)], [c_6, c_39031])).
% 12.55/5.29  tff(c_39105, plain, (![B_2441, B_2442]: (~v1_xboole_0(B_2441) | r1_tarski(B_2441, B_2442))), inference(resolution, [status(thm)], [c_12, c_39079])).
% 12.55/5.29  tff(c_39162, plain, (![B_2443]: (k1_xboole_0=B_2443 | ~v1_xboole_0(B_2443))), inference(resolution, [status(thm)], [c_39105, c_1380])).
% 12.55/5.29  tff(c_39172, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_36136, c_39162])).
% 12.55/5.29  tff(c_39175, plain, (![A_9]: ('#skF_2'(A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_39162])).
% 12.55/5.29  tff(c_39205, plain, (![A_9]: ('#skF_2'(A_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_39172, c_39175])).
% 12.55/5.29  tff(c_18, plain, (![A_9]: (m1_subset_1('#skF_2'(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.55/5.29  tff(c_108, plain, (![A_81, B_82]: (r1_tarski(A_81, B_82) | ~m1_subset_1(A_81, k1_zfmisc_1(B_82)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.55/5.29  tff(c_120, plain, (![A_9]: (r1_tarski('#skF_2'(A_9), A_9))), inference(resolution, [status(thm)], [c_18, c_108])).
% 12.55/5.29  tff(c_39215, plain, (![A_9]: (r1_tarski('#skF_5', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_39205, c_120])).
% 12.55/5.29  tff(c_39551, plain, (![A_2471, B_2472, C_2473, D_2474]: (k7_relset_1(A_2471, B_2472, C_2473, D_2474)=k9_relat_1(C_2473, D_2474) | ~m1_subset_1(C_2473, k1_zfmisc_1(k2_zfmisc_1(A_2471, B_2472))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.55/5.29  tff(c_39627, plain, (![D_2488]: (k7_relset_1('#skF_3', '#skF_6', '#skF_7', D_2488)=k9_relat_1('#skF_7', D_2488))), inference(resolution, [status(thm)], [c_94, c_39551])).
% 12.55/5.29  tff(c_36261, plain, (![C_2199, B_2200, A_2201]: (~v1_xboole_0(C_2199) | ~m1_subset_1(B_2200, k1_zfmisc_1(C_2199)) | ~r2_hidden(A_2201, B_2200))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.55/5.29  tff(c_36631, plain, (![B_2224, A_2225, A_2226]: (~v1_xboole_0(B_2224) | ~r2_hidden(A_2225, A_2226) | ~r1_tarski(A_2226, B_2224))), inference(resolution, [status(thm)], [c_24, c_36261])).
% 12.55/5.29  tff(c_36713, plain, (![B_2237, A_2238, B_2239]: (~v1_xboole_0(B_2237) | ~r1_tarski(A_2238, B_2237) | r1_tarski(A_2238, B_2239))), inference(resolution, [status(thm)], [c_6, c_36631])).
% 12.55/5.29  tff(c_36744, plain, (![B_2240, B_2241]: (~v1_xboole_0(B_2240) | r1_tarski(B_2240, B_2241))), inference(resolution, [status(thm)], [c_12, c_36713])).
% 12.55/5.29  tff(c_1375, plain, (k7_relset_1('#skF_3', '#skF_6', '#skF_7', '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', k7_relset_1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_1357])).
% 12.55/5.29  tff(c_36137, plain, (~r1_tarski('#skF_5', k7_relset_1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1375])).
% 12.55/5.29  tff(c_36767, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36744, c_36137])).
% 12.55/5.29  tff(c_36796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36136, c_36767])).
% 12.55/5.29  tff(c_36797, plain, (k7_relset_1('#skF_3', '#skF_6', '#skF_7', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_1375])).
% 12.55/5.29  tff(c_39633, plain, (k9_relat_1('#skF_7', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_39627, c_36797])).
% 12.55/5.29  tff(c_41377, plain, (![A_2599, B_2600, C_2601, D_2602]: (k2_partfun1(A_2599, B_2600, C_2601, D_2602)=k7_relat_1(C_2601, D_2602) | ~m1_subset_1(C_2601, k1_zfmisc_1(k2_zfmisc_1(A_2599, B_2600))) | ~v1_funct_1(C_2601))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.55/5.29  tff(c_41391, plain, (![D_2602]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_2602)=k7_relat_1('#skF_7', D_2602) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_94, c_41377])).
% 12.55/5.29  tff(c_41402, plain, (![D_2602]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_2602)=k7_relat_1('#skF_7', D_2602))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_41391])).
% 12.55/5.29  tff(c_40411, plain, (![A_2540, B_2541, C_2542, D_2543]: (k2_partfun1(A_2540, B_2541, C_2542, D_2543)=k7_relat_1(C_2542, D_2543) | ~m1_subset_1(C_2542, k1_zfmisc_1(k2_zfmisc_1(A_2540, B_2541))) | ~v1_funct_1(C_2542))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.55/5.29  tff(c_40425, plain, (![D_2543]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_2543)=k7_relat_1('#skF_7', D_2543) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_94, c_40411])).
% 12.55/5.29  tff(c_40436, plain, (![D_2543]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_2543)=k7_relat_1('#skF_7', D_2543))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_40425])).
% 12.55/5.29  tff(c_41024, plain, (![A_2575, B_2576, C_2577, D_2578]: (m1_subset_1(k2_partfun1(A_2575, B_2576, C_2577, D_2578), k1_zfmisc_1(k2_zfmisc_1(A_2575, B_2576))) | ~m1_subset_1(C_2577, k1_zfmisc_1(k2_zfmisc_1(A_2575, B_2576))) | ~v1_funct_1(C_2577))), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.55/5.29  tff(c_41076, plain, (![D_2543]: (m1_subset_1(k7_relat_1('#skF_7', D_2543), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_6'))) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_40436, c_41024])).
% 12.55/5.29  tff(c_41251, plain, (![D_2594]: (m1_subset_1(k7_relat_1('#skF_7', D_2594), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_94, c_41076])).
% 12.55/5.29  tff(c_41289, plain, (![D_2594]: (v1_relat_1(k7_relat_1('#skF_7', D_2594)) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_6')))), inference(resolution, [status(thm)], [c_41251, c_28])).
% 12.55/5.29  tff(c_41317, plain, (![D_2594]: (v1_relat_1(k7_relat_1('#skF_7', D_2594)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_41289])).
% 12.55/5.29  tff(c_40207, plain, (![C_2522, A_2523, B_2524]: (m1_subset_1(C_2522, k1_zfmisc_1(k2_zfmisc_1(A_2523, B_2524))) | ~r1_tarski(k2_relat_1(C_2522), B_2524) | ~r1_tarski(k1_relat_1(C_2522), A_2523) | ~v1_relat_1(C_2522))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.55/5.29  tff(c_36799, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1281])).
% 12.55/5.29  tff(c_40262, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_5') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_40207, c_36799])).
% 12.55/5.29  tff(c_40343, plain, (~v1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(splitLeft, [status(thm)], [c_40262])).
% 12.55/5.29  tff(c_40437, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40436, c_40343])).
% 12.55/5.29  tff(c_41322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41317, c_40437])).
% 12.55/5.29  tff(c_41323, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_4') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_5')), inference(splitRight, [status(thm)], [c_40262])).
% 12.55/5.29  tff(c_41517, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_4') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_41402, c_41402, c_41323])).
% 12.55/5.29  tff(c_41518, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_5')), inference(splitLeft, [status(thm)], [c_41517])).
% 12.55/5.29  tff(c_41524, plain, (~r1_tarski(k9_relat_1('#skF_7', '#skF_4'), '#skF_5') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36, c_41518])).
% 12.55/5.29  tff(c_41531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_39215, c_39633, c_41524])).
% 12.55/5.29  tff(c_41533, plain, (r1_tarski(k2_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_5')), inference(splitRight, [status(thm)], [c_41517])).
% 12.55/5.29  tff(c_41546, plain, (k2_relat_1(k7_relat_1('#skF_7', '#skF_4'))='#skF_5' | ~r1_tarski('#skF_5', k2_relat_1(k7_relat_1('#skF_7', '#skF_4')))), inference(resolution, [status(thm)], [c_41533, c_8])).
% 12.55/5.29  tff(c_41568, plain, (k2_relat_1(k7_relat_1('#skF_7', '#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_39215, c_41546])).
% 12.55/5.29  tff(c_41324, plain, (v1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(splitRight, [status(thm)], [c_40262])).
% 12.55/5.29  tff(c_41403, plain, (v1_relat_1(k7_relat_1('#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_41402, c_41324])).
% 12.55/5.29  tff(c_56, plain, (![C_54, A_52, B_53]: (m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~r1_tarski(k2_relat_1(C_54), B_53) | ~r1_tarski(k1_relat_1(C_54), A_52) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.55/5.29  tff(c_41407, plain, (~m1_subset_1(k7_relat_1('#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_41402, c_36799])).
% 12.55/5.29  tff(c_41423, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_5') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_41407])).
% 12.55/5.29  tff(c_41429, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_5') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41403, c_41423])).
% 12.55/5.29  tff(c_41697, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39215, c_41568, c_41429])).
% 12.55/5.29  tff(c_41700, plain, (~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_39073, c_41697])).
% 12.55/5.29  tff(c_41709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_12, c_41700])).
% 12.55/5.29  tff(c_41711, plain, (m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1281])).
% 12.55/5.29  tff(c_42509, plain, (![C_2683, A_2684, B_2685]: (v1_xboole_0(C_2683) | ~m1_subset_1(C_2683, k1_zfmisc_1(k2_zfmisc_1(A_2684, B_2685))) | ~v1_xboole_0(A_2684))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.55/5.29  tff(c_42526, plain, (v1_xboole_0(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_41711, c_42509])).
% 12.55/5.29  tff(c_42538, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_42526])).
% 12.55/5.29  tff(c_41794, plain, (![C_2640, B_2641, A_2642]: (~v1_xboole_0(C_2640) | ~m1_subset_1(B_2641, k1_zfmisc_1(C_2640)) | ~r2_hidden(A_2642, B_2641))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.55/5.29  tff(c_42106, plain, (![B_2656, A_2657, A_2658]: (~v1_xboole_0(B_2656) | ~r2_hidden(A_2657, A_2658) | ~r1_tarski(A_2658, B_2656))), inference(resolution, [status(thm)], [c_24, c_41794])).
% 12.55/5.29  tff(c_42203, plain, (![B_2665, A_2666, B_2667]: (~v1_xboole_0(B_2665) | ~r1_tarski(A_2666, B_2665) | r1_tarski(A_2666, B_2667))), inference(resolution, [status(thm)], [c_6, c_42106])).
% 12.55/5.29  tff(c_42232, plain, (![B_2668, B_2669]: (~v1_xboole_0(B_2668) | r1_tarski(B_2668, B_2669))), inference(resolution, [status(thm)], [c_12, c_42203])).
% 12.55/5.29  tff(c_42275, plain, (![B_2670]: (k1_xboole_0=B_2670 | ~v1_xboole_0(B_2670))), inference(resolution, [status(thm)], [c_42232, c_1380])).
% 12.55/5.29  tff(c_42285, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_36136, c_42275])).
% 12.55/5.29  tff(c_42288, plain, (![A_9]: ('#skF_2'(A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_42275])).
% 12.55/5.29  tff(c_42339, plain, (![A_9]: ('#skF_2'(A_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42285, c_42288])).
% 12.55/5.29  tff(c_42348, plain, (![A_9]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_42339, c_18])).
% 12.55/5.29  tff(c_64, plain, (![A_59]: (v1_funct_2(k1_xboole_0, A_59, k1_xboole_0) | k1_xboole_0=A_59 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_59, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 12.55/5.29  tff(c_42671, plain, (![A_59]: (v1_funct_2('#skF_5', A_59, '#skF_5') | A_59='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42348, c_42285, c_42285, c_42285, c_42285, c_42285, c_64])).
% 12.55/5.29  tff(c_42426, plain, (![C_2678, B_2679, A_2680]: (v1_xboole_0(C_2678) | ~m1_subset_1(C_2678, k1_zfmisc_1(k2_zfmisc_1(B_2679, A_2680))) | ~v1_xboole_0(A_2680))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.55/5.29  tff(c_42429, plain, (v1_xboole_0(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_41711, c_42426])).
% 12.55/5.29  tff(c_42439, plain, (v1_xboole_0(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36136, c_42429])).
% 12.55/5.29  tff(c_42271, plain, (![B_2668]: (k1_xboole_0=B_2668 | ~v1_xboole_0(B_2668))), inference(resolution, [status(thm)], [c_42232, c_1380])).
% 12.55/5.29  tff(c_42289, plain, (![B_2668]: (B_2668='#skF_5' | ~v1_xboole_0(B_2668))), inference(demodulation, [status(thm), theory('equality')], [c_42285, c_42271])).
% 12.55/5.29  tff(c_42738, plain, (k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_42439, c_42289])).
% 12.55/5.29  tff(c_41710, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1281])).
% 12.55/5.29  tff(c_42771, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42738, c_41710])).
% 12.55/5.29  tff(c_42786, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_42671, c_42771])).
% 12.55/5.29  tff(c_42809, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42786, c_36136])).
% 12.55/5.29  tff(c_42812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42538, c_42809])).
% 12.55/5.29  tff(c_42813, plain, (v1_xboole_0(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(splitRight, [status(thm)], [c_42526])).
% 12.55/5.29  tff(c_42814, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_42526])).
% 12.55/5.29  tff(c_42818, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_42814, c_42289])).
% 12.55/5.29  tff(c_42821, plain, (![B_2668]: (B_2668='#skF_4' | ~v1_xboole_0(B_2668))), inference(demodulation, [status(thm), theory('equality')], [c_42818, c_42289])).
% 12.55/5.29  tff(c_43253, plain, (k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_42813, c_42821])).
% 12.55/5.29  tff(c_1282, plain, (v1_funct_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(splitRight, [status(thm)], [c_88])).
% 12.55/5.29  tff(c_43300, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_43253, c_1282])).
% 12.55/5.29  tff(c_138, plain, (![A_87, B_88]: (v1_relat_1(A_87) | ~v1_relat_1(B_88) | ~r1_tarski(A_87, B_88))), inference(resolution, [status(thm)], [c_24, c_122])).
% 12.55/5.29  tff(c_161, plain, (v1_relat_1(k7_relset_1('#skF_3', '#skF_6', '#skF_7', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_90, c_138])).
% 12.55/5.29  tff(c_1467, plain, (~v1_relat_1('#skF_5')), inference(splitLeft, [status(thm)], [c_161])).
% 12.55/5.29  tff(c_1490, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1339])).
% 12.55/5.29  tff(c_9412, plain, (![A_747, B_748, C_749]: (k1_relset_1(A_747, B_748, C_749)=k1_relat_1(C_749) | ~m1_subset_1(C_749, k1_zfmisc_1(k2_zfmisc_1(A_747, B_748))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.55/5.29  tff(c_9431, plain, (k1_relset_1('#skF_3', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_94, c_9412])).
% 12.55/5.29  tff(c_12304, plain, (![B_892, A_893, C_894]: (k1_xboole_0=B_892 | k1_relset_1(A_893, B_892, C_894)=A_893 | ~v1_funct_2(C_894, A_893, B_892) | ~m1_subset_1(C_894, k1_zfmisc_1(k2_zfmisc_1(A_893, B_892))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 12.55/5.29  tff(c_12339, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_3', '#skF_6', '#skF_7')='#skF_3' | ~v1_funct_2('#skF_7', '#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_94, c_12304])).
% 12.55/5.29  tff(c_12348, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_9431, c_12339])).
% 12.55/5.29  tff(c_12349, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_12348])).
% 12.55/5.29  tff(c_8587, plain, (![C_677, A_678, B_679]: (v4_relat_1(C_677, A_678) | ~m1_subset_1(C_677, k1_zfmisc_1(k2_zfmisc_1(A_678, B_679))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.55/5.29  tff(c_8600, plain, (v4_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_94, c_8587])).
% 12.55/5.29  tff(c_8604, plain, (k7_relat_1('#skF_7', '#skF_3')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_8600, c_38])).
% 12.55/5.29  tff(c_8607, plain, (k7_relat_1('#skF_7', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_8604])).
% 12.55/5.29  tff(c_8614, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_3') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_8607, c_40])).
% 12.55/5.29  tff(c_8620, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_8614])).
% 12.55/5.29  tff(c_8630, plain, (k1_relat_1('#skF_7')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_8620, c_8])).
% 12.55/5.29  tff(c_8669, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_8630])).
% 12.55/5.29  tff(c_12351, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12349, c_8669])).
% 12.55/5.29  tff(c_12355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_12351])).
% 12.55/5.29  tff(c_12356, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_12348])).
% 12.55/5.29  tff(c_12404, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12356, c_1349])).
% 12.55/5.29  tff(c_12408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_12404])).
% 12.55/5.29  tff(c_12409, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(splitRight, [status(thm)], [c_8630])).
% 12.55/5.29  tff(c_12910, plain, (![B_939, A_940]: (k1_relat_1(k7_relat_1(B_939, A_940))=A_940 | ~r1_tarski(A_940, k1_relat_1(B_939)) | ~v1_relat_1(B_939))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.55/5.29  tff(c_12920, plain, (![A_940]: (k1_relat_1(k7_relat_1('#skF_7', A_940))=A_940 | ~r1_tarski(A_940, '#skF_3') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_12409, c_12910])).
% 12.55/5.29  tff(c_12944, plain, (![A_940]: (k1_relat_1(k7_relat_1('#skF_7', A_940))=A_940 | ~r1_tarski(A_940, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_12920])).
% 12.55/5.29  tff(c_15501, plain, (![A_1084, B_1085, C_1086, D_1087]: (k2_partfun1(A_1084, B_1085, C_1086, D_1087)=k7_relat_1(C_1086, D_1087) | ~m1_subset_1(C_1086, k1_zfmisc_1(k2_zfmisc_1(A_1084, B_1085))) | ~v1_funct_1(C_1086))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.55/5.29  tff(c_15525, plain, (![D_1087]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_1087)=k7_relat_1('#skF_7', D_1087) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_94, c_15501])).
% 12.55/5.29  tff(c_15535, plain, (![D_1087]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_1087)=k7_relat_1('#skF_7', D_1087))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_15525])).
% 12.55/5.29  tff(c_2331, plain, (![A_309, B_310, C_311]: (k1_relset_1(A_309, B_310, C_311)=k1_relat_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.55/5.29  tff(c_2346, plain, (k1_relset_1('#skF_3', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_94, c_2331])).
% 12.55/5.29  tff(c_3728, plain, (![B_419, A_420, C_421]: (k1_xboole_0=B_419 | k1_relset_1(A_420, B_419, C_421)=A_420 | ~v1_funct_2(C_421, A_420, B_419) | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(A_420, B_419))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 12.55/5.29  tff(c_3751, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_3', '#skF_6', '#skF_7')='#skF_3' | ~v1_funct_2('#skF_7', '#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_94, c_3728])).
% 12.55/5.29  tff(c_3760, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2346, c_3751])).
% 12.55/5.29  tff(c_3761, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(splitLeft, [status(thm)], [c_3760])).
% 12.55/5.29  tff(c_1763, plain, (![C_260, A_261, B_262]: (v4_relat_1(C_260, A_261) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.55/5.29  tff(c_1776, plain, (v4_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_94, c_1763])).
% 12.55/5.29  tff(c_1780, plain, (k7_relat_1('#skF_7', '#skF_3')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1776, c_38])).
% 12.55/5.29  tff(c_1783, plain, (k7_relat_1('#skF_7', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_1780])).
% 12.55/5.29  tff(c_1809, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_3') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1783, c_40])).
% 12.55/5.29  tff(c_1815, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_1809])).
% 12.55/5.29  tff(c_1826, plain, (k1_relat_1('#skF_7')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1815, c_8])).
% 12.55/5.29  tff(c_1912, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1826])).
% 12.55/5.29  tff(c_3763, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3761, c_1912])).
% 12.55/5.29  tff(c_3767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3763])).
% 12.55/5.29  tff(c_3768, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_3760])).
% 12.55/5.29  tff(c_3811, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3768, c_1349])).
% 12.55/5.29  tff(c_3815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_3811])).
% 12.55/5.29  tff(c_3816, plain, (k1_relat_1('#skF_7')='#skF_3'), inference(splitRight, [status(thm)], [c_1826])).
% 12.55/5.29  tff(c_3942, plain, (![B_435, A_436]: (k1_relat_1(k7_relat_1(B_435, A_436))=A_436 | ~r1_tarski(A_436, k1_relat_1(B_435)) | ~v1_relat_1(B_435))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.55/5.29  tff(c_3948, plain, (![A_436]: (k1_relat_1(k7_relat_1('#skF_7', A_436))=A_436 | ~r1_tarski(A_436, '#skF_3') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3816, c_3942])).
% 12.55/5.29  tff(c_3979, plain, (![A_436]: (k1_relat_1(k7_relat_1('#skF_7', A_436))=A_436 | ~r1_tarski(A_436, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_3948])).
% 12.55/5.29  tff(c_8011, plain, (![A_650, B_651, C_652, D_653]: (k2_partfun1(A_650, B_651, C_652, D_653)=k7_relat_1(C_652, D_653) | ~m1_subset_1(C_652, k1_zfmisc_1(k2_zfmisc_1(A_650, B_651))) | ~v1_funct_1(C_652))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.55/5.29  tff(c_8029, plain, (![D_653]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_653)=k7_relat_1('#skF_7', D_653) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_94, c_8011])).
% 12.55/5.29  tff(c_8040, plain, (![D_653]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_653)=k7_relat_1('#skF_7', D_653))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_8029])).
% 12.55/5.29  tff(c_4843, plain, (![A_513, B_514, C_515, D_516]: (k7_relset_1(A_513, B_514, C_515, D_516)=k9_relat_1(C_515, D_516) | ~m1_subset_1(C_515, k1_zfmisc_1(k2_zfmisc_1(A_513, B_514))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.55/5.29  tff(c_4855, plain, (![D_516]: (k7_relset_1('#skF_3', '#skF_6', '#skF_7', D_516)=k9_relat_1('#skF_7', D_516))), inference(resolution, [status(thm)], [c_94, c_4843])).
% 12.55/5.29  tff(c_5027, plain, (r1_tarski(k9_relat_1('#skF_7', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4855, c_90])).
% 12.55/5.29  tff(c_7912, plain, (![A_641, B_642, C_643, D_644]: (k2_partfun1(A_641, B_642, C_643, D_644)=k7_relat_1(C_643, D_644) | ~m1_subset_1(C_643, k1_zfmisc_1(k2_zfmisc_1(A_641, B_642))) | ~v1_funct_1(C_643))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.55/5.29  tff(c_7932, plain, (![D_644]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_644)=k7_relat_1('#skF_7', D_644) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_94, c_7912])).
% 12.55/5.29  tff(c_7943, plain, (![D_644]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_644)=k7_relat_1('#skF_7', D_644))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_7932])).
% 12.55/5.29  tff(c_6431, plain, (![A_584, B_585, C_586, D_587]: (k2_partfun1(A_584, B_585, C_586, D_587)=k7_relat_1(C_586, D_587) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_zfmisc_1(A_584, B_585))) | ~v1_funct_1(C_586))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.55/5.29  tff(c_6451, plain, (![D_587]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_587)=k7_relat_1('#skF_7', D_587) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_94, c_6431])).
% 12.55/5.29  tff(c_6462, plain, (![D_587]: (k2_partfun1('#skF_3', '#skF_6', '#skF_7', D_587)=k7_relat_1('#skF_7', D_587))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_6451])).
% 12.55/5.29  tff(c_7496, plain, (![A_627, B_628, C_629, D_630]: (m1_subset_1(k2_partfun1(A_627, B_628, C_629, D_630), k1_zfmisc_1(k2_zfmisc_1(A_627, B_628))) | ~m1_subset_1(C_629, k1_zfmisc_1(k2_zfmisc_1(A_627, B_628))) | ~v1_funct_1(C_629))), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.55/5.29  tff(c_7546, plain, (![D_587]: (m1_subset_1(k7_relat_1('#skF_7', D_587), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_6'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_6'))) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6462, c_7496])).
% 12.55/5.29  tff(c_7576, plain, (![D_631]: (m1_subset_1(k7_relat_1('#skF_7', D_631), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_94, c_7546])).
% 12.55/5.29  tff(c_7611, plain, (![D_631]: (v1_relat_1(k7_relat_1('#skF_7', D_631)) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_6')))), inference(resolution, [status(thm)], [c_7576, c_28])).
% 12.55/5.29  tff(c_7635, plain, (![D_631]: (v1_relat_1(k7_relat_1('#skF_7', D_631)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7611])).
% 12.55/5.29  tff(c_5921, plain, (![C_568, A_569, B_570]: (m1_subset_1(C_568, k1_zfmisc_1(k2_zfmisc_1(A_569, B_570))) | ~r1_tarski(k2_relat_1(C_568), B_570) | ~r1_tarski(k1_relat_1(C_568), A_569) | ~v1_relat_1(C_568))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.55/5.29  tff(c_1560, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1281])).
% 12.55/5.29  tff(c_5970, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_5') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_5921, c_1560])).
% 12.55/5.29  tff(c_6174, plain, (~v1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(splitLeft, [status(thm)], [c_5970])).
% 12.55/5.29  tff(c_6500, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6462, c_6174])).
% 12.55/5.29  tff(c_7642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7635, c_6500])).
% 12.55/5.29  tff(c_7643, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_4') | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_5')), inference(splitRight, [status(thm)], [c_5970])).
% 12.55/5.29  tff(c_7645, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_5')), inference(splitLeft, [status(thm)], [c_7643])).
% 12.55/5.29  tff(c_7995, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7943, c_7645])).
% 12.55/5.29  tff(c_8001, plain, (~r1_tarski(k9_relat_1('#skF_7', '#skF_4'), '#skF_5') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36, c_7995])).
% 12.55/5.29  tff(c_8008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_5027, c_8001])).
% 12.55/5.29  tff(c_8009, plain, (~r1_tarski(k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), '#skF_4')), inference(splitRight, [status(thm)], [c_7643])).
% 12.55/5.29  tff(c_8440, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_7', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8040, c_8009])).
% 12.55/5.29  tff(c_8443, plain, (~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3979, c_8440])).
% 12.55/5.29  tff(c_8452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_12, c_8443])).
% 12.55/5.29  tff(c_8453, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1281])).
% 12.55/5.29  tff(c_15548, plain, (~v1_funct_2(k7_relat_1('#skF_7', '#skF_4'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15535, c_8453])).
% 12.55/5.29  tff(c_8454, plain, (m1_subset_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1281])).
% 12.55/5.29  tff(c_13181, plain, (![A_965, B_966, C_967]: (k1_relset_1(A_965, B_966, C_967)=k1_relat_1(C_967) | ~m1_subset_1(C_967, k1_zfmisc_1(k2_zfmisc_1(A_965, B_966))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.55/5.29  tff(c_13198, plain, (k1_relset_1('#skF_4', '#skF_5', k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))=k1_relat_1(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(resolution, [status(thm)], [c_8454, c_13181])).
% 12.55/5.29  tff(c_15542, plain, (k1_relset_1('#skF_4', '#skF_5', k7_relat_1('#skF_7', '#skF_4'))=k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15535, c_15535, c_13198])).
% 12.55/5.29  tff(c_15547, plain, (m1_subset_1(k7_relat_1('#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_15535, c_8454])).
% 12.55/5.29  tff(c_15838, plain, (![B_1096, C_1097, A_1098]: (k1_xboole_0=B_1096 | v1_funct_2(C_1097, A_1098, B_1096) | k1_relset_1(A_1098, B_1096, C_1097)!=A_1098 | ~m1_subset_1(C_1097, k1_zfmisc_1(k2_zfmisc_1(A_1098, B_1096))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 12.55/5.29  tff(c_15841, plain, (k1_xboole_0='#skF_5' | v1_funct_2(k7_relat_1('#skF_7', '#skF_4'), '#skF_4', '#skF_5') | k1_relset_1('#skF_4', '#skF_5', k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_15547, c_15838])).
% 12.55/5.29  tff(c_15878, plain, (k1_xboole_0='#skF_5' | v1_funct_2(k7_relat_1('#skF_7', '#skF_4'), '#skF_4', '#skF_5') | k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15542, c_15841])).
% 12.55/5.29  tff(c_15879, plain, (k1_xboole_0='#skF_5' | k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_15548, c_15878])).
% 12.55/5.29  tff(c_15889, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_15879])).
% 12.55/5.29  tff(c_15892, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12944, c_15889])).
% 12.55/5.29  tff(c_15896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_15892])).
% 12.55/5.29  tff(c_15897, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_15879])).
% 12.55/5.29  tff(c_15946, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15897, c_1349])).
% 12.55/5.29  tff(c_15950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1490, c_15946])).
% 12.55/5.29  tff(c_15952, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1339])).
% 12.55/5.29  tff(c_16658, plain, (![C_1156, B_1157, A_1158]: (~v1_xboole_0(C_1156) | ~m1_subset_1(B_1157, k1_zfmisc_1(C_1156)) | ~r2_hidden(A_1158, B_1157))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.55/5.29  tff(c_16911, plain, (![B_1170, A_1171, A_1172]: (~v1_xboole_0(B_1170) | ~r2_hidden(A_1171, A_1172) | ~r1_tarski(A_1172, B_1170))), inference(resolution, [status(thm)], [c_24, c_16658])).
% 12.55/5.29  tff(c_16920, plain, (![B_1177, A_1178, B_1179]: (~v1_xboole_0(B_1177) | ~r1_tarski(A_1178, B_1177) | r1_tarski(A_1178, B_1179))), inference(resolution, [status(thm)], [c_6, c_16911])).
% 12.55/5.29  tff(c_16946, plain, (![B_1180, B_1181]: (~v1_xboole_0(B_1180) | r1_tarski(B_1180, B_1181))), inference(resolution, [status(thm)], [c_12, c_16920])).
% 12.55/5.29  tff(c_16976, plain, (![B_1182]: (k1_xboole_0=B_1182 | ~v1_xboole_0(B_1182))), inference(resolution, [status(thm)], [c_16946, c_1380])).
% 12.55/5.29  tff(c_16986, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_15952, c_16976])).
% 12.55/5.29  tff(c_163, plain, (![A_8]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_14, c_138])).
% 12.55/5.29  tff(c_1284, plain, (![A_8]: (~v1_relat_1(A_8))), inference(splitLeft, [status(thm)], [c_163])).
% 12.55/5.29  tff(c_1290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1284, c_135])).
% 12.55/5.29  tff(c_1291, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_163])).
% 12.55/5.29  tff(c_17003, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16986, c_1291])).
% 12.55/5.29  tff(c_17007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1467, c_17003])).
% 12.55/5.29  tff(c_17009, plain, (v1_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_161])).
% 12.55/5.29  tff(c_42834, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42818, c_17009])).
% 12.55/5.29  tff(c_42307, plain, (![A_8]: (r1_tarski('#skF_5', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_42285, c_14])).
% 12.55/5.29  tff(c_42825, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_42818, c_42307])).
% 12.55/5.29  tff(c_41722, plain, (![C_2621, B_2622, A_2623]: (v5_relat_1(C_2621, B_2622) | ~m1_subset_1(C_2621, k1_zfmisc_1(k2_zfmisc_1(A_2623, B_2622))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.55/5.29  tff(c_41746, plain, (![A_2629, B_2630, A_2631]: (v5_relat_1(A_2629, B_2630) | ~r1_tarski(A_2629, k2_zfmisc_1(A_2631, B_2630)))), inference(resolution, [status(thm)], [c_24, c_41722])).
% 12.55/5.29  tff(c_41772, plain, (![B_2630]: (v5_relat_1(k1_xboole_0, B_2630))), inference(resolution, [status(thm)], [c_14, c_41746])).
% 12.55/5.29  tff(c_41975, plain, (![B_2650, A_2651]: (r1_tarski(k2_relat_1(B_2650), A_2651) | ~v5_relat_1(B_2650, A_2651) | ~v1_relat_1(B_2650))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.55/5.29  tff(c_42111, plain, (![B_2661]: (k2_relat_1(B_2661)=k1_xboole_0 | ~v5_relat_1(B_2661, k1_xboole_0) | ~v1_relat_1(B_2661))), inference(resolution, [status(thm)], [c_41975, c_1380])).
% 12.55/5.29  tff(c_42123, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_41772, c_42111])).
% 12.55/5.29  tff(c_42134, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1291, c_42123])).
% 12.55/5.29  tff(c_42292, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42285, c_42285, c_42134])).
% 12.55/5.29  tff(c_42824, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42818, c_42818, c_42292])).
% 12.55/5.29  tff(c_42473, plain, (![A_2682]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_2682)))), inference(demodulation, [status(thm), theory('equality')], [c_42339, c_18])).
% 12.55/5.29  tff(c_46, plain, (![C_36, A_34, B_35]: (v4_relat_1(C_36, A_34) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.55/5.29  tff(c_42499, plain, (![A_34]: (v4_relat_1('#skF_5', A_34))), inference(resolution, [status(thm)], [c_42473, c_46])).
% 12.55/5.29  tff(c_42871, plain, (![A_2711]: (v4_relat_1('#skF_4', A_2711))), inference(demodulation, [status(thm), theory('equality')], [c_42818, c_42499])).
% 12.55/5.29  tff(c_42874, plain, (![A_2711]: (k7_relat_1('#skF_4', A_2711)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_42871, c_38])).
% 12.55/5.29  tff(c_43024, plain, (![A_2718]: (k7_relat_1('#skF_4', A_2718)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42834, c_42874])).
% 12.55/5.29  tff(c_43032, plain, (![A_2718]: (r1_tarski(k1_relat_1('#skF_4'), A_2718) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_43024, c_40])).
% 12.55/5.29  tff(c_43039, plain, (![A_2718]: (r1_tarski(k1_relat_1('#skF_4'), A_2718))), inference(demodulation, [status(thm), theory('equality')], [c_42834, c_43032])).
% 12.55/5.29  tff(c_1374, plain, (![A_9]: ('#skF_2'(A_9)=A_9 | ~r1_tarski(A_9, '#skF_2'(A_9)))), inference(resolution, [status(thm)], [c_120, c_1357])).
% 12.55/5.29  tff(c_42345, plain, (![A_9]: (A_9='#skF_5' | ~r1_tarski(A_9, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42339, c_42339, c_1374])).
% 12.55/5.29  tff(c_43105, plain, (![A_2727]: (A_2727='#skF_4' | ~r1_tarski(A_2727, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42818, c_42818, c_42345])).
% 12.55/5.29  tff(c_43130, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_43039, c_43105])).
% 12.55/5.29  tff(c_84, plain, (![B_71, A_70]: (v1_funct_2(B_71, k1_relat_1(B_71), A_70) | ~r1_tarski(k2_relat_1(B_71), A_70) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_198])).
% 12.55/5.29  tff(c_43146, plain, (![A_70]: (v1_funct_2('#skF_4', '#skF_4', A_70) | ~r1_tarski(k2_relat_1('#skF_4'), A_70) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_43130, c_84])).
% 12.55/5.29  tff(c_43153, plain, (![A_70]: (v1_funct_2('#skF_4', '#skF_4', A_70) | ~v1_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42834, c_42825, c_42824, c_43146])).
% 12.55/5.29  tff(c_43350, plain, (![A_70]: (v1_funct_2('#skF_4', '#skF_4', A_70))), inference(demodulation, [status(thm), theory('equality')], [c_43300, c_43153])).
% 12.55/5.29  tff(c_42831, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42818, c_41710])).
% 12.55/5.29  tff(c_43297, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_43253, c_42831])).
% 12.55/5.29  tff(c_43353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43350, c_43297])).
% 12.55/5.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.55/5.29  
% 12.55/5.29  Inference rules
% 12.55/5.29  ----------------------
% 12.55/5.29  #Ref     : 0
% 12.55/5.29  #Sup     : 9727
% 12.55/5.29  #Fact    : 0
% 12.55/5.29  #Define  : 0
% 12.55/5.29  #Split   : 128
% 12.55/5.29  #Chain   : 0
% 12.55/5.29  #Close   : 0
% 12.55/5.29  
% 12.55/5.29  Ordering : KBO
% 12.55/5.29  
% 12.55/5.29  Simplification rules
% 12.55/5.29  ----------------------
% 12.55/5.29  #Subsume      : 2099
% 12.55/5.29  #Demod        : 8484
% 12.55/5.29  #Tautology    : 4858
% 12.55/5.29  #SimpNegUnit  : 224
% 12.55/5.29  #BackRed      : 926
% 12.55/5.29  
% 12.55/5.29  #Partial instantiations: 0
% 12.55/5.29  #Strategies tried      : 1
% 12.55/5.29  
% 12.55/5.29  Timing (in seconds)
% 12.55/5.29  ----------------------
% 12.55/5.29  Preprocessing        : 0.38
% 12.55/5.29  Parsing              : 0.20
% 12.55/5.29  CNF conversion       : 0.03
% 12.55/5.29  Main loop            : 4.03
% 12.55/5.29  Inferencing          : 1.17
% 12.55/5.29  Reduction            : 1.51
% 12.55/5.29  Demodulation         : 1.10
% 12.55/5.29  BG Simplification    : 0.11
% 12.55/5.29  Subsumption          : 0.92
% 12.55/5.29  Abstraction          : 0.14
% 12.55/5.29  MUC search           : 0.00
% 12.55/5.29  Cooper               : 0.00
% 12.55/5.29  Total                : 4.55
% 12.55/5.29  Index Insertion      : 0.00
% 12.55/5.29  Index Deletion       : 0.00
% 12.55/5.29  Index Matching       : 0.00
% 12.55/5.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
