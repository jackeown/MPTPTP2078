%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:35 EST 2020

% Result     : Theorem 12.44s
% Output     : CNFRefutation 12.93s
% Verified   : 
% Statistics : Number of formulae       :  375 (4108 expanded)
%              Number of leaves         :   50 (1341 expanded)
%              Depth                    :   23
%              Number of atoms          :  672 (10551 expanded)
%              Number of equality atoms :  211 (2307 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_188,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_122,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_148,axiom,(
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

tff(f_105,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_171,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_161,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_90,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_659,plain,(
    ! [C_127,B_128,A_129] :
      ( v1_xboole_0(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(B_128,A_129)))
      | ~ v1_xboole_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_678,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_659])).

tff(c_681,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_678])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_30,plain,(
    ! [A_18] :
      ( v1_funct_1(k2_funct_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_84,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_149,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_152,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_149])).

tff(c_155,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_152])).

tff(c_156,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_163,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_156])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_163])).

tff(c_173,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_195,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_205,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_195])).

tff(c_175,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_188,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_175])).

tff(c_32,plain,(
    ! [A_18] :
      ( v1_relat_1(k2_funct_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_88,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_86,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1046,plain,(
    ! [A_169,B_170,C_171] :
      ( k2_relset_1(A_169,B_170,C_171) = k2_relat_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1059,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_1046])).

tff(c_1070,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1059])).

tff(c_619,plain,(
    ! [C_124,A_125,B_126] :
      ( v4_relat_1(C_124,A_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_639,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_619])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_642,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_639,c_28])).

tff(c_645,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_642])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_649,plain,
    ( k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_22])).

tff(c_653,plain,(
    k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_649])).

tff(c_1071,plain,(
    k9_relat_1('#skF_4','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1070,c_653])).

tff(c_1308,plain,(
    ! [B_178,A_179] :
      ( k10_relat_1(k2_funct_1(B_178),A_179) = k9_relat_1(B_178,A_179)
      | ~ v2_funct_1(B_178)
      | ~ v1_funct_1(B_178)
      | ~ v1_relat_1(B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k10_relat_1(B_14,A_13),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14730,plain,(
    ! [B_26870,A_26871] :
      ( r1_tarski(k9_relat_1(B_26870,A_26871),k1_relat_1(k2_funct_1(B_26870)))
      | ~ v1_relat_1(k2_funct_1(B_26870))
      | ~ v2_funct_1(B_26870)
      | ~ v1_funct_1(B_26870)
      | ~ v1_relat_1(B_26870) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_24])).

tff(c_14742,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1071,c_14730])).

tff(c_14759,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_88,c_14742])).

tff(c_14764,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14759])).

tff(c_14767,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_14764])).

tff(c_14771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_14767])).

tff(c_14773,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_14759])).

tff(c_174,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_92,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1231,plain,(
    ! [A_174,B_175,C_176] :
      ( k1_relset_1(A_174,B_175,C_176) = k1_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1258,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_1231])).

tff(c_1421,plain,(
    ! [B_195,A_196,C_197] :
      ( k1_xboole_0 = B_195
      | k1_relset_1(A_196,B_195,C_197) = A_196
      | ~ v1_funct_2(C_197,A_196,B_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1437,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_1421])).

tff(c_1454,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1258,c_1437])).

tff(c_1456,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1454])).

tff(c_742,plain,(
    ! [A_139] :
      ( k2_relat_1(k2_funct_1(A_139)) = k1_relat_1(A_139)
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_26,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18849,plain,(
    ! [A_39220] :
      ( k10_relat_1(k2_funct_1(A_39220),k1_relat_1(A_39220)) = k1_relat_1(k2_funct_1(A_39220))
      | ~ v1_relat_1(k2_funct_1(A_39220))
      | ~ v2_funct_1(A_39220)
      | ~ v1_funct_1(A_39220)
      | ~ v1_relat_1(A_39220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_742,c_26])).

tff(c_18895,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_18849])).

tff(c_18923,plain,(
    k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_88,c_14773,c_18895])).

tff(c_34,plain,(
    ! [B_20,A_19] :
      ( k10_relat_1(k2_funct_1(B_20),A_19) = k9_relat_1(B_20,A_19)
      | ~ v2_funct_1(B_20)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18932,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k9_relat_1('#skF_4','#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18923,c_34])).

tff(c_18948,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_88,c_1071,c_18932])).

tff(c_1087,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1070,c_26])).

tff(c_1099,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_1087])).

tff(c_1467,plain,(
    k10_relat_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_1099])).

tff(c_20,plain,(
    ! [A_10] :
      ( k9_relat_1(A_10,k1_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_19010,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18948,c_20])).

tff(c_19049,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14773,c_19010])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( k9_relat_1(k2_funct_1(B_22),A_21) = k10_relat_1(B_22,A_21)
      | ~ v2_funct_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_19117,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k10_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19049,c_36])).

tff(c_19128,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_88,c_1467,c_19117])).

tff(c_990,plain,(
    ! [A_165] :
      ( m1_subset_1(A_165,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_165),k2_relat_1(A_165))))
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1023,plain,(
    ! [A_165] :
      ( r1_tarski(A_165,k2_zfmisc_1(k1_relat_1(A_165),k2_relat_1(A_165)))
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(resolution,[status(thm)],[c_990,c_16])).

tff(c_19148,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19128,c_1023])).

tff(c_19181,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14773,c_174,c_18948,c_19148])).

tff(c_19183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_19181])).

tff(c_19184,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1454])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_19247,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19184,c_2])).

tff(c_19249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_681,c_19247])).

tff(c_19250,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_678])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_19255,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_19250,c_4])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_19276,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19255,c_19255,c_10])).

tff(c_19251,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_678])).

tff(c_19259,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_19251,c_4])).

tff(c_19288,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19255,c_19259])).

tff(c_306,plain,(
    ! [B_90,A_91] :
      ( v1_xboole_0(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_91))
      | ~ v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_330,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_90,c_306])).

tff(c_386,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_19291,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19288,c_386])).

tff(c_19424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19250,c_19276,c_19291])).

tff(c_19425,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_19430,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_19425,c_4])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_244,plain,(
    ! [A_82,B_83] : m1_subset_1('#skF_1'(A_82,B_83),k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_256,plain,(
    ! [B_4] : m1_subset_1('#skF_1'(k1_xboole_0,B_4),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_244])).

tff(c_309,plain,(
    ! [B_4] :
      ( v1_xboole_0('#skF_1'(k1_xboole_0,B_4))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_256,c_306])).

tff(c_331,plain,(
    ! [B_92] : v1_xboole_0('#skF_1'(k1_xboole_0,B_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_309])).

tff(c_335,plain,(
    ! [B_92] : '#skF_1'(k1_xboole_0,B_92) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_331,c_4])).

tff(c_343,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_256])).

tff(c_19551,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_19430,c_343])).

tff(c_74,plain,(
    ! [A_43,B_44] : v1_relat_1('#skF_1'(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_66,plain,(
    ! [A_43,B_44] : v1_funct_2('#skF_1'(A_43,B_44),A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_76,plain,(
    ! [A_43,B_44] : m1_subset_1('#skF_1'(A_43,B_44),k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_26404,plain,(
    ! [A_52905,B_52906,C_52907] :
      ( k1_relset_1(A_52905,B_52906,C_52907) = k1_relat_1(C_52907)
      | ~ m1_subset_1(C_52907,k1_zfmisc_1(k2_zfmisc_1(A_52905,B_52906))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_26422,plain,(
    ! [A_43,B_44] : k1_relset_1(A_43,B_44,'#skF_1'(A_43,B_44)) = k1_relat_1('#skF_1'(A_43,B_44)) ),
    inference(resolution,[status(thm)],[c_76,c_26404])).

tff(c_64,plain,(
    ! [B_41,A_40,C_42] :
      ( k1_xboole_0 = B_41
      | k1_relset_1(A_40,B_41,C_42) = A_40
      | ~ v1_funct_2(C_42,A_40,B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_27017,plain,(
    ! [B_52955,A_52956,C_52957] :
      ( B_52955 = '#skF_4'
      | k1_relset_1(A_52956,B_52955,C_52957) = A_52956
      | ~ v1_funct_2(C_52957,A_52956,B_52955)
      | ~ m1_subset_1(C_52957,k1_zfmisc_1(k2_zfmisc_1(A_52956,B_52955))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_64])).

tff(c_27032,plain,(
    ! [B_44,A_43] :
      ( B_44 = '#skF_4'
      | k1_relset_1(A_43,B_44,'#skF_1'(A_43,B_44)) = A_43
      | ~ v1_funct_2('#skF_1'(A_43,B_44),A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_76,c_27017])).

tff(c_27046,plain,(
    ! [B_52958,A_52959] :
      ( B_52958 = '#skF_4'
      | k1_relat_1('#skF_1'(A_52959,B_52958)) = A_52959 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_26422,c_27032])).

tff(c_232,plain,(
    ! [A_81] :
      ( k10_relat_1(A_81,k2_relat_1(A_81)) = k1_relat_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_238,plain,(
    ! [A_81] :
      ( r1_tarski(k1_relat_1(A_81),k1_relat_1(A_81))
      | ~ v1_relat_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_24])).

tff(c_27066,plain,(
    ! [A_52959,B_52958] :
      ( r1_tarski(k1_relat_1('#skF_1'(A_52959,B_52958)),A_52959)
      | ~ v1_relat_1('#skF_1'(A_52959,B_52958))
      | ~ v1_relat_1('#skF_1'(A_52959,B_52958))
      | B_52958 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27046,c_238])).

tff(c_27863,plain,(
    ! [A_59201,B_59202] :
      ( r1_tarski(k1_relat_1('#skF_1'(A_59201,B_59202)),A_59201)
      | B_59202 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_27066])).

tff(c_329,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(A_8)
      | ~ v1_xboole_0(B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_306])).

tff(c_28501,plain,(
    ! [A_59224,B_59225] :
      ( v1_xboole_0(k1_relat_1('#skF_1'(A_59224,B_59225)))
      | ~ v1_xboole_0(A_59224)
      | B_59225 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_27863,c_329])).

tff(c_19439,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_4])).

tff(c_28655,plain,(
    ! [A_59236,B_59237] :
      ( k1_relat_1('#skF_1'(A_59236,B_59237)) = '#skF_4'
      | ~ v1_xboole_0(A_59236)
      | B_59237 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_28501,c_19439])).

tff(c_27063,plain,(
    ! [A_52959,B_52958] :
      ( r1_tarski(A_52959,k1_relat_1('#skF_1'(A_52959,B_52958)))
      | ~ v1_relat_1('#skF_1'(A_52959,B_52958))
      | ~ v1_relat_1('#skF_1'(A_52959,B_52958))
      | B_52958 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27046,c_238])).

tff(c_27098,plain,(
    ! [A_52959,B_52958] :
      ( r1_tarski(A_52959,k1_relat_1('#skF_1'(A_52959,B_52958)))
      | B_52958 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_27063])).

tff(c_28677,plain,(
    ! [A_59236,B_59237] :
      ( r1_tarski(A_59236,'#skF_4')
      | B_59237 = '#skF_4'
      | ~ v1_xboole_0(A_59236)
      | B_59237 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28655,c_27098])).

tff(c_28930,plain,(
    ! [B_59237] :
      ( B_59237 = '#skF_4'
      | B_59237 = '#skF_4' ) ),
    inference(splitLeft,[status(thm)],[c_28677])).

tff(c_29331,plain,(
    ! [B_64731] : B_64731 = '#skF_4' ),
    inference(factorization,[status(thm),theory(equality)],[c_28930])).

tff(c_19440,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_19430,c_12])).

tff(c_19438,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_19430,c_10])).

tff(c_19431,plain,(
    ! [B_92] : '#skF_1'('#skF_4',B_92) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_19430,c_335])).

tff(c_20428,plain,(
    ! [A_39324,B_39325,C_39326] :
      ( k1_relset_1(A_39324,B_39325,C_39326) = k1_relat_1(C_39326)
      | ~ m1_subset_1(C_39326,k1_zfmisc_1(k2_zfmisc_1(A_39324,B_39325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_20485,plain,(
    ! [A_39328,B_39329] : k1_relset_1(A_39328,B_39329,'#skF_1'(A_39328,B_39329)) = k1_relat_1('#skF_1'(A_39328,B_39329)) ),
    inference(resolution,[status(thm)],[c_76,c_20428])).

tff(c_20497,plain,(
    ! [B_92] : k1_relat_1('#skF_1'('#skF_4',B_92)) = k1_relset_1('#skF_4',B_92,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19431,c_20485])).

tff(c_20503,plain,(
    ! [B_92] : k1_relset_1('#skF_4',B_92,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19431,c_20497])).

tff(c_62,plain,(
    ! [B_41,C_42] :
      ( k1_relset_1(k1_xboole_0,B_41,C_42) = k1_xboole_0
      | ~ v1_funct_2(C_42,k1_xboole_0,B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_95,plain,(
    ! [B_41,C_42] :
      ( k1_relset_1(k1_xboole_0,B_41,C_42) = k1_xboole_0
      | ~ v1_funct_2(C_42,k1_xboole_0,B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_62])).

tff(c_20569,plain,(
    ! [B_39340,C_39341] :
      ( k1_relset_1('#skF_4',B_39340,C_39341) = '#skF_4'
      | ~ v1_funct_2(C_39341,'#skF_4',B_39340)
      | ~ m1_subset_1(C_39341,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_19430,c_19430,c_19430,c_95])).

tff(c_20580,plain,(
    ! [B_44] :
      ( k1_relset_1('#skF_4',B_44,'#skF_1'('#skF_4',B_44)) = '#skF_4'
      | ~ m1_subset_1('#skF_1'('#skF_4',B_44),k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_66,c_20569])).

tff(c_20592,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19551,c_19431,c_20503,c_19431,c_20580])).

tff(c_38,plain,(
    ! [A_23] :
      ( k2_relat_1(k2_funct_1(A_23)) = k1_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_20450,plain,(
    ! [A_43,B_44] : k1_relset_1(A_43,B_44,'#skF_1'(A_43,B_44)) = k1_relat_1('#skF_1'(A_43,B_44)) ),
    inference(resolution,[status(thm)],[c_76,c_20428])).

tff(c_20883,plain,(
    ! [B_39365,A_39366,C_39367] :
      ( B_39365 = '#skF_4'
      | k1_relset_1(A_39366,B_39365,C_39367) = A_39366
      | ~ v1_funct_2(C_39367,A_39366,B_39365)
      | ~ m1_subset_1(C_39367,k1_zfmisc_1(k2_zfmisc_1(A_39366,B_39365))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_64])).

tff(c_20898,plain,(
    ! [B_44,A_43] :
      ( B_44 = '#skF_4'
      | k1_relset_1(A_43,B_44,'#skF_1'(A_43,B_44)) = A_43
      | ~ v1_funct_2('#skF_1'(A_43,B_44),A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_76,c_20883])).

tff(c_20912,plain,(
    ! [B_39368,A_39369] :
      ( B_39368 = '#skF_4'
      | k1_relat_1('#skF_1'(A_39369,B_39368)) = A_39369 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_20450,c_20898])).

tff(c_20932,plain,(
    ! [A_39369,B_39368] :
      ( r1_tarski(k1_relat_1('#skF_1'(A_39369,B_39368)),A_39369)
      | ~ v1_relat_1('#skF_1'(A_39369,B_39368))
      | ~ v1_relat_1('#skF_1'(A_39369,B_39368))
      | B_39368 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20912,c_238])).

tff(c_21702,plain,(
    ! [A_45416,B_45417] :
      ( r1_tarski(k1_relat_1('#skF_1'(A_45416,B_45417)),A_45416)
      | B_45417 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_20932])).

tff(c_22465,plain,(
    ! [A_45447,B_45448] :
      ( v1_xboole_0(k1_relat_1('#skF_1'(A_45447,B_45448)))
      | ~ v1_xboole_0(A_45447)
      | B_45448 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_21702,c_329])).

tff(c_22593,plain,(
    ! [A_45457,B_45458] :
      ( k1_relat_1('#skF_1'(A_45457,B_45458)) = '#skF_4'
      | ~ v1_xboole_0(A_45457)
      | B_45458 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_22465,c_19439])).

tff(c_20929,plain,(
    ! [A_39369,B_39368] :
      ( r1_tarski(A_39369,k1_relat_1('#skF_1'(A_39369,B_39368)))
      | ~ v1_relat_1('#skF_1'(A_39369,B_39368))
      | ~ v1_relat_1('#skF_1'(A_39369,B_39368))
      | B_39368 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20912,c_238])).

tff(c_20964,plain,(
    ! [A_39369,B_39368] :
      ( r1_tarski(A_39369,k1_relat_1('#skF_1'(A_39369,B_39368)))
      | B_39368 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_20929])).

tff(c_22615,plain,(
    ! [A_45457,B_45458] :
      ( r1_tarski(A_45457,'#skF_4')
      | B_45458 = '#skF_4'
      | ~ v1_xboole_0(A_45457)
      | B_45458 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22593,c_20964])).

tff(c_22859,plain,(
    ! [B_45458] :
      ( B_45458 = '#skF_4'
      | B_45458 = '#skF_4' ) ),
    inference(splitLeft,[status(thm)],[c_22615])).

tff(c_23251,plain,(
    ! [B_50750] : B_50750 = '#skF_4' ),
    inference(factorization,[status(thm),theory(equality)],[c_22859])).

tff(c_19426,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_19463,plain,(
    ! [A_39234] :
      ( A_39234 = '#skF_4'
      | ~ v1_xboole_0(A_39234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_4])).

tff(c_19470,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_19426,c_19463])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_19449,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_4'
      | A_3 = '#skF_4'
      | k2_zfmisc_1(A_3,B_4) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_19430,c_19430,c_8])).

tff(c_19620,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_19470,c_19449])).

tff(c_19691,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_19620])).

tff(c_19695,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19691,c_195])).

tff(c_19701,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19438,c_19695])).

tff(c_23434,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23251,c_19701])).

tff(c_23526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19551,c_23434])).

tff(c_23528,plain,(
    ! [A_52711] :
      ( r1_tarski(A_52711,'#skF_4')
      | ~ v1_xboole_0(A_52711) ) ),
    inference(splitRight,[status(thm)],[c_22615])).

tff(c_19694,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19691,c_205])).

tff(c_19700,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19438,c_19694])).

tff(c_23561,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_23528,c_19700])).

tff(c_20158,plain,(
    ! [A_39305,B_39306,C_39307] :
      ( k2_relset_1(A_39305,B_39306,C_39307) = k2_relat_1(C_39307)
      | ~ m1_subset_1(C_39307,k1_zfmisc_1(k2_zfmisc_1(A_39305,B_39306))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_20184,plain,(
    ! [A_39312,B_39313] : k2_relset_1(A_39312,B_39313,'#skF_1'(A_39312,B_39313)) = k2_relat_1('#skF_1'(A_39312,B_39313)) ),
    inference(resolution,[status(thm)],[c_76,c_20158])).

tff(c_20196,plain,(
    ! [B_92] : k2_relat_1('#skF_1'('#skF_4',B_92)) = k2_relset_1('#skF_4',B_92,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19431,c_20184])).

tff(c_20242,plain,(
    ! [B_39315] : k2_relset_1('#skF_4',B_39315,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19431,c_20196])).

tff(c_19696,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19691,c_86])).

tff(c_20246,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_20242,c_19696])).

tff(c_253,plain,(
    ! [A_3] : m1_subset_1('#skF_1'(A_3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_244])).

tff(c_312,plain,(
    ! [A_3] :
      ( v1_xboole_0('#skF_1'(A_3,k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_253,c_306])).

tff(c_336,plain,(
    ! [A_93] : v1_xboole_0('#skF_1'(A_93,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_312])).

tff(c_340,plain,(
    ! [A_93] : '#skF_1'(A_93,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_336,c_4])).

tff(c_19566,plain,(
    ! [A_39241] : '#skF_1'(A_39241,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_19430,c_340])).

tff(c_72,plain,(
    ! [A_43,B_44] : v4_relat_1('#skF_1'(A_43,B_44),A_43) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_19583,plain,(
    ! [A_39241] : v4_relat_1('#skF_4',A_39241) ),
    inference(superposition,[status(thm),theory(equality)],[c_19566,c_72])).

tff(c_19716,plain,(
    ! [B_39250,A_39251] :
      ( k7_relat_1(B_39250,A_39251) = B_39250
      | ~ v4_relat_1(B_39250,A_39251)
      | ~ v1_relat_1(B_39250) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_19719,plain,(
    ! [A_39241] :
      ( k7_relat_1('#skF_4',A_39241) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_19583,c_19716])).

tff(c_19725,plain,(
    ! [A_39241] : k7_relat_1('#skF_4',A_39241) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_19719])).

tff(c_19747,plain,(
    ! [B_39253,A_39254] :
      ( k2_relat_1(k7_relat_1(B_39253,A_39254)) = k9_relat_1(B_39253,A_39254)
      | ~ v1_relat_1(B_39253) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_19759,plain,(
    ! [A_39241] :
      ( k9_relat_1('#skF_4',A_39241) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19725,c_19747])).

tff(c_19763,plain,(
    ! [A_39241] : k9_relat_1('#skF_4',A_39241) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_19759])).

tff(c_20254,plain,(
    ! [A_39241] : k9_relat_1('#skF_4',A_39241) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20246,c_19763])).

tff(c_20750,plain,(
    ! [B_39351,A_39352] :
      ( k10_relat_1(k2_funct_1(B_39351),A_39352) = k9_relat_1(B_39351,A_39352)
      | ~ v2_funct_1(B_39351)
      | ~ v1_funct_1(B_39351)
      | ~ v1_relat_1(B_39351) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24961,plain,(
    ! [B_52795,A_52796] :
      ( r1_tarski(k9_relat_1(B_52795,A_52796),k1_relat_1(k2_funct_1(B_52795)))
      | ~ v1_relat_1(k2_funct_1(B_52795))
      | ~ v2_funct_1(B_52795)
      | ~ v1_funct_1(B_52795)
      | ~ v1_relat_1(B_52795) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20750,c_24])).

tff(c_24973,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20254,c_24961])).

tff(c_24987,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_88,c_24973])).

tff(c_24990,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_24987])).

tff(c_24993,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_24990])).

tff(c_24997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_24993])).

tff(c_24999,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_24987])).

tff(c_20067,plain,(
    ! [A_39293] :
      ( k2_relat_1(k2_funct_1(A_39293)) = k1_relat_1(A_39293)
      | ~ v2_funct_1(A_39293)
      | ~ v1_funct_1(A_39293)
      | ~ v1_relat_1(A_39293) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_25469,plain,(
    ! [A_52821] :
      ( k10_relat_1(k2_funct_1(A_52821),k1_relat_1(A_52821)) = k1_relat_1(k2_funct_1(A_52821))
      | ~ v1_relat_1(k2_funct_1(A_52821))
      | ~ v2_funct_1(A_52821)
      | ~ v1_funct_1(A_52821)
      | ~ v1_relat_1(A_52821) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20067,c_26])).

tff(c_25513,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20592,c_25469])).

tff(c_25533,plain,(
    k10_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_88,c_24999,c_25513])).

tff(c_25542,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k9_relat_1('#skF_4','#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25533,c_34])).

tff(c_25558,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_88,c_20254,c_25542])).

tff(c_20204,plain,(
    ! [A_39314] :
      ( m1_subset_1(A_39314,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_39314),k2_relat_1(A_39314))))
      | ~ v1_funct_1(A_39314)
      | ~ v1_relat_1(A_39314) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_14,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20239,plain,(
    ! [A_39314] :
      ( v1_xboole_0(A_39314)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_39314),k2_relat_1(A_39314)))
      | ~ v1_funct_1(A_39314)
      | ~ v1_relat_1(A_39314) ) ),
    inference(resolution,[status(thm)],[c_20204,c_14])).

tff(c_25587,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25558,c_20239])).

tff(c_25631,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24999,c_174,c_25587])).

tff(c_25632,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_23561,c_25631])).

tff(c_25662,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_25632])).

tff(c_25666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_88,c_19425,c_19438,c_20592,c_25662])).

tff(c_25667,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_19620])).

tff(c_25671,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25667,c_195])).

tff(c_25676,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19440,c_25671])).

tff(c_29506,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29331,c_25676])).

tff(c_29602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19551,c_29506])).

tff(c_29604,plain,(
    ! [A_66672] :
      ( r1_tarski(A_66672,'#skF_4')
      | ~ v1_xboole_0(A_66672) ) ),
    inference(splitRight,[status(thm)],[c_28677])).

tff(c_25670,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25667,c_205])).

tff(c_25675,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19440,c_25670])).

tff(c_29637,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_29604,c_25675])).

tff(c_19563,plain,(
    ! [A_93] : '#skF_1'(A_93,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_19430,c_340])).

tff(c_26137,plain,(
    ! [A_52881,B_52882,C_52883] :
      ( k2_relset_1(A_52881,B_52882,C_52883) = k2_relat_1(C_52883)
      | ~ m1_subset_1(C_52883,k1_zfmisc_1(k2_zfmisc_1(A_52881,B_52882))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_26160,plain,(
    ! [A_52886,B_52887] : k2_relset_1(A_52886,B_52887,'#skF_1'(A_52886,B_52887)) = k2_relat_1('#skF_1'(A_52886,B_52887)) ),
    inference(resolution,[status(thm)],[c_76,c_26137])).

tff(c_26175,plain,(
    ! [A_93] : k2_relat_1('#skF_1'(A_93,'#skF_4')) = k2_relset_1(A_93,'#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19563,c_26160])).

tff(c_26187,plain,(
    ! [A_52889] : k2_relset_1(A_52889,'#skF_4','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19563,c_26175])).

tff(c_25672,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25667,c_25667,c_86])).

tff(c_26194,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_26187,c_25672])).

tff(c_26078,plain,(
    ! [A_52874] :
      ( k1_relat_1(k2_funct_1(A_52874)) = k2_relat_1(A_52874)
      | ~ v2_funct_1(A_52874)
      | ~ v1_funct_1(A_52874)
      | ~ v1_relat_1(A_52874) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_31741,plain,(
    ! [A_66784,A_66785] :
      ( r1_tarski(k10_relat_1(k2_funct_1(A_66784),A_66785),k2_relat_1(A_66784))
      | ~ v1_relat_1(k2_funct_1(A_66784))
      | ~ v2_funct_1(A_66784)
      | ~ v1_funct_1(A_66784)
      | ~ v1_relat_1(A_66784) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26078,c_24])).

tff(c_31762,plain,(
    ! [A_66785] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_4'),A_66785),'#skF_4')
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26194,c_31741])).

tff(c_31783,plain,(
    ! [A_66785] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_4'),A_66785),'#skF_4')
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_88,c_31762])).

tff(c_31784,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_31783])).

tff(c_31787,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_31784])).

tff(c_31791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_31787])).

tff(c_31793,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_31783])).

tff(c_31794,plain,(
    ! [A_66786] : r1_tarski(k10_relat_1(k2_funct_1('#skF_4'),A_66786),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_31783])).

tff(c_25825,plain,(
    ! [C_52842,B_52843,A_52844] :
      ( v1_xboole_0(C_52842)
      | ~ m1_subset_1(C_52842,k1_zfmisc_1(k2_zfmisc_1(B_52843,A_52844)))
      | ~ v1_xboole_0(A_52844) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_25828,plain,(
    ! [C_52842] :
      ( v1_xboole_0(C_52842)
      | ~ m1_subset_1(C_52842,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19438,c_25825])).

tff(c_25857,plain,(
    ! [C_52847] :
      ( v1_xboole_0(C_52847)
      | ~ m1_subset_1(C_52847,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19425,c_25828])).

tff(c_25867,plain,(
    ! [A_8] :
      ( v1_xboole_0(A_8)
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_25857])).

tff(c_31836,plain,(
    ! [A_66787] : v1_xboole_0(k10_relat_1(k2_funct_1('#skF_4'),A_66787)) ),
    inference(resolution,[status(thm)],[c_31794,c_25867])).

tff(c_31866,plain,
    ( v1_xboole_0(k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_31836])).

tff(c_31880,plain,(
    v1_xboole_0(k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31793,c_31866])).

tff(c_31925,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_31880,c_19439])).

tff(c_26329,plain,(
    ! [A_52901] :
      ( m1_subset_1(A_52901,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52901),k2_relat_1(A_52901))))
      | ~ v1_funct_1(A_52901)
      | ~ v1_relat_1(A_52901) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_26367,plain,(
    ! [A_52901] :
      ( v1_xboole_0(A_52901)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_52901),k2_relat_1(A_52901)))
      | ~ v1_funct_1(A_52901)
      | ~ v1_relat_1(A_52901) ) ),
    inference(resolution,[status(thm)],[c_26329,c_14])).

tff(c_31949,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4'))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31925,c_26367])).

tff(c_31990,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31793,c_174,c_19425,c_19440,c_31949])).

tff(c_31992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29637,c_31990])).

tff(c_31994,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_32570,plain,(
    ! [C_66850,B_66851,A_66852] :
      ( v1_xboole_0(C_66850)
      | ~ m1_subset_1(C_66850,k1_zfmisc_1(k2_zfmisc_1(B_66851,A_66852)))
      | ~ v1_xboole_0(A_66852) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_32591,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_31994,c_32570])).

tff(c_32597,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_32591])).

tff(c_32936,plain,(
    ! [A_66890,B_66891,C_66892] :
      ( k2_relset_1(A_66890,B_66891,C_66892) = k2_relat_1(C_66892)
      | ~ m1_subset_1(C_66892,k1_zfmisc_1(k2_zfmisc_1(A_66890,B_66891))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_32949,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_32936])).

tff(c_32960,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_32949])).

tff(c_40,plain,(
    ! [A_23] :
      ( k1_relat_1(k2_funct_1(A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_31993,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_32823,plain,(
    ! [A_66875,B_66876,C_66877] :
      ( k1_relset_1(A_66875,B_66876,C_66877) = k1_relat_1(C_66877)
      | ~ m1_subset_1(C_66877,k1_zfmisc_1(k2_zfmisc_1(A_66875,B_66876))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_32844,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_31994,c_32823])).

tff(c_33474,plain,(
    ! [B_66913,C_66914,A_66915] :
      ( k1_xboole_0 = B_66913
      | v1_funct_2(C_66914,A_66915,B_66913)
      | k1_relset_1(A_66915,B_66913,C_66914) != A_66915
      | ~ m1_subset_1(C_66914,k1_zfmisc_1(k2_zfmisc_1(A_66915,B_66913))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_33486,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_31994,c_33474])).

tff(c_33507,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32844,c_33486])).

tff(c_33508,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_31993,c_33507])).

tff(c_33515,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_33508])).

tff(c_33518,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_33515])).

tff(c_33521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_94,c_88,c_32960,c_33518])).

tff(c_33522,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_33508])).

tff(c_33563,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33522,c_2])).

tff(c_33565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32597,c_33563])).

tff(c_33567,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_32591])).

tff(c_33571,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_33567,c_4])).

tff(c_33590,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33571,c_33571,c_10])).

tff(c_32101,plain,(
    ! [B_66801,A_66802] :
      ( v1_xboole_0(B_66801)
      | ~ m1_subset_1(B_66801,k1_zfmisc_1(A_66802))
      | ~ v1_xboole_0(A_66802) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32127,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_31994,c_32101])).

tff(c_32272,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_32127])).

tff(c_33717,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33590,c_32272])).

tff(c_33720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33567,c_33717])).

tff(c_33722,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32127])).

tff(c_33730,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33722,c_4])).

tff(c_33775,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_33730,c_8])).

tff(c_33777,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_33775])).

tff(c_33796,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33777,c_2])).

tff(c_33792,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33777,c_33777,c_10])).

tff(c_32129,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_90,c_32101])).

tff(c_32226,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_32129])).

tff(c_33914,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33792,c_32226])).

tff(c_33919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33796,c_33914])).

tff(c_33920,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_33775])).

tff(c_33940,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33920,c_2])).

tff(c_33938,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33920,c_33920,c_12])).

tff(c_34002,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33938,c_32226])).

tff(c_34007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33940,c_34002])).

tff(c_34008,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_32129])).

tff(c_34038,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34008,c_4])).

tff(c_34048,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34038,c_34038,c_10])).

tff(c_34050,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34038,c_34038,c_12])).

tff(c_34009,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32129])).

tff(c_34125,plain,(
    ! [A_66945] :
      ( A_66945 = '#skF_4'
      | ~ v1_xboole_0(A_66945) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34038,c_4])).

tff(c_34132,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34009,c_34125])).

tff(c_34713,plain,(
    ! [B_66997,A_66998] :
      ( B_66997 = '#skF_4'
      | A_66998 = '#skF_4'
      | k2_zfmisc_1(A_66998,B_66997) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34038,c_34038,c_34038,c_8])).

tff(c_34723,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_34132,c_34713])).

tff(c_34728,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_34723])).

tff(c_34332,plain,(
    ! [C_66958,B_66959,A_66960] :
      ( v1_xboole_0(C_66958)
      | ~ m1_subset_1(C_66958,k1_zfmisc_1(k2_zfmisc_1(B_66959,A_66960)))
      | ~ v1_xboole_0(A_66960) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_34355,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_31994,c_34332])).

tff(c_34357,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_34355])).

tff(c_34730,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34728,c_34357])).

tff(c_34742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34008,c_34730])).

tff(c_34743,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34723])).

tff(c_34253,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_32127])).

tff(c_34748,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34743,c_34253])).

tff(c_34759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34008,c_34050,c_34748])).

tff(c_34761,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_34355])).

tff(c_34049,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34038,c_4])).

tff(c_34765,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34761,c_34049])).

tff(c_34768,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34765,c_34253])).

tff(c_34778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34008,c_34048,c_34768])).

tff(c_34779,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_32127])).

tff(c_34784,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34779,c_34049])).

tff(c_34814,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34784,c_31993])).

tff(c_34780,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32127])).

tff(c_34838,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34780,c_34049])).

tff(c_34851,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34838,c_76])).

tff(c_34863,plain,(
    ! [C_67002,B_67003,A_67004] :
      ( v1_xboole_0(C_67002)
      | ~ m1_subset_1(C_67002,k1_zfmisc_1(k2_zfmisc_1(B_67003,A_67004)))
      | ~ v1_xboole_0(A_67004) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_34872,plain,(
    ! [C_67002] :
      ( v1_xboole_0(C_67002)
      | ~ m1_subset_1(C_67002,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34048,c_34863])).

tff(c_34884,plain,(
    ! [C_67002] :
      ( v1_xboole_0(C_67002)
      | ~ m1_subset_1(C_67002,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34008,c_34872])).

tff(c_35083,plain,(
    v1_xboole_0('#skF_1'('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34851,c_34884])).

tff(c_35131,plain,(
    '#skF_1'('#skF_3','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_35083,c_34049])).

tff(c_35161,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35131,c_66])).

tff(c_35177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34814,c_35161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.44/4.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.51/4.72  
% 12.51/4.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.74/4.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 12.74/4.72  
% 12.74/4.72  %Foreground sorts:
% 12.74/4.72  
% 12.74/4.72  
% 12.74/4.72  %Background operators:
% 12.74/4.72  
% 12.74/4.72  
% 12.74/4.72  %Foreground operators:
% 12.74/4.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.74/4.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.74/4.72  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.74/4.72  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.74/4.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.74/4.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.74/4.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.74/4.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.74/4.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.74/4.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.74/4.72  tff('#skF_2', type, '#skF_2': $i).
% 12.74/4.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.74/4.72  tff('#skF_3', type, '#skF_3': $i).
% 12.74/4.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.74/4.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.74/4.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.74/4.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.74/4.72  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.74/4.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.74/4.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.74/4.72  tff('#skF_4', type, '#skF_4': $i).
% 12.74/4.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.74/4.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.74/4.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.74/4.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.74/4.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.74/4.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.74/4.72  
% 12.93/4.76  tff(f_188, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 12.93/4.76  tff(f_122, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 12.93/4.76  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.93/4.76  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.93/4.76  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.93/4.76  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.93/4.76  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.93/4.76  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 12.93/4.76  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 12.93/4.76  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 12.93/4.76  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 12.93/4.76  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.93/4.76  tff(f_148, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.93/4.76  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 12.93/4.76  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 12.93/4.76  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 12.93/4.76  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 12.93/4.76  tff(f_171, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 12.93/4.76  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.93/4.76  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 12.93/4.76  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.93/4.76  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 12.93/4.76  tff(f_161, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 12.93/4.76  tff(c_90, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 12.93/4.76  tff(c_659, plain, (![C_127, B_128, A_129]: (v1_xboole_0(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(B_128, A_129))) | ~v1_xboole_0(A_129))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.93/4.76  tff(c_678, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_90, c_659])).
% 12.93/4.76  tff(c_681, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_678])).
% 12.93/4.76  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.93/4.76  tff(c_94, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 12.93/4.76  tff(c_30, plain, (![A_18]: (v1_funct_1(k2_funct_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.93/4.76  tff(c_84, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 12.93/4.76  tff(c_149, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_84])).
% 12.93/4.76  tff(c_152, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_149])).
% 12.93/4.76  tff(c_155, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_152])).
% 12.93/4.76  tff(c_156, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.93/4.76  tff(c_163, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_156])).
% 12.93/4.76  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_163])).
% 12.93/4.76  tff(c_173, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_84])).
% 12.93/4.76  tff(c_195, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_173])).
% 12.93/4.76  tff(c_205, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_195])).
% 12.93/4.76  tff(c_175, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.93/4.76  tff(c_188, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_175])).
% 12.93/4.76  tff(c_32, plain, (![A_18]: (v1_relat_1(k2_funct_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.93/4.76  tff(c_88, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 12.93/4.76  tff(c_86, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_188])).
% 12.93/4.76  tff(c_1046, plain, (![A_169, B_170, C_171]: (k2_relset_1(A_169, B_170, C_171)=k2_relat_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.93/4.76  tff(c_1059, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_1046])).
% 12.93/4.76  tff(c_1070, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1059])).
% 12.93/4.76  tff(c_619, plain, (![C_124, A_125, B_126]: (v4_relat_1(C_124, A_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.93/4.76  tff(c_639, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_90, c_619])).
% 12.93/4.76  tff(c_28, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.93/4.76  tff(c_642, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_639, c_28])).
% 12.93/4.76  tff(c_645, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_642])).
% 12.93/4.76  tff(c_22, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.93/4.76  tff(c_649, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_645, c_22])).
% 12.93/4.76  tff(c_653, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_649])).
% 12.93/4.76  tff(c_1071, plain, (k9_relat_1('#skF_4', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1070, c_653])).
% 12.93/4.76  tff(c_1308, plain, (![B_178, A_179]: (k10_relat_1(k2_funct_1(B_178), A_179)=k9_relat_1(B_178, A_179) | ~v2_funct_1(B_178) | ~v1_funct_1(B_178) | ~v1_relat_1(B_178))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.93/4.76  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k10_relat_1(B_14, A_13), k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.93/4.76  tff(c_14730, plain, (![B_26870, A_26871]: (r1_tarski(k9_relat_1(B_26870, A_26871), k1_relat_1(k2_funct_1(B_26870))) | ~v1_relat_1(k2_funct_1(B_26870)) | ~v2_funct_1(B_26870) | ~v1_funct_1(B_26870) | ~v1_relat_1(B_26870))), inference(superposition, [status(thm), theory('equality')], [c_1308, c_24])).
% 12.93/4.76  tff(c_14742, plain, (r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1071, c_14730])).
% 12.93/4.76  tff(c_14759, plain, (r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_88, c_14742])).
% 12.93/4.76  tff(c_14764, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_14759])).
% 12.93/4.76  tff(c_14767, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_14764])).
% 12.93/4.76  tff(c_14771, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_14767])).
% 12.93/4.76  tff(c_14773, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_14759])).
% 12.93/4.76  tff(c_174, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_84])).
% 12.93/4.76  tff(c_92, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 12.93/4.76  tff(c_1231, plain, (![A_174, B_175, C_176]: (k1_relset_1(A_174, B_175, C_176)=k1_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.93/4.76  tff(c_1258, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_1231])).
% 12.93/4.76  tff(c_1421, plain, (![B_195, A_196, C_197]: (k1_xboole_0=B_195 | k1_relset_1(A_196, B_195, C_197)=A_196 | ~v1_funct_2(C_197, A_196, B_195) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.93/4.76  tff(c_1437, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_1421])).
% 12.93/4.76  tff(c_1454, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1258, c_1437])).
% 12.93/4.76  tff(c_1456, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1454])).
% 12.93/4.76  tff(c_742, plain, (![A_139]: (k2_relat_1(k2_funct_1(A_139))=k1_relat_1(A_139) | ~v2_funct_1(A_139) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.93/4.76  tff(c_26, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.93/4.76  tff(c_18849, plain, (![A_39220]: (k10_relat_1(k2_funct_1(A_39220), k1_relat_1(A_39220))=k1_relat_1(k2_funct_1(A_39220)) | ~v1_relat_1(k2_funct_1(A_39220)) | ~v2_funct_1(A_39220) | ~v1_funct_1(A_39220) | ~v1_relat_1(A_39220))), inference(superposition, [status(thm), theory('equality')], [c_742, c_26])).
% 12.93/4.76  tff(c_18895, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1456, c_18849])).
% 12.93/4.76  tff(c_18923, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_88, c_14773, c_18895])).
% 12.93/4.76  tff(c_34, plain, (![B_20, A_19]: (k10_relat_1(k2_funct_1(B_20), A_19)=k9_relat_1(B_20, A_19) | ~v2_funct_1(B_20) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.93/4.76  tff(c_18932, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k9_relat_1('#skF_4', '#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18923, c_34])).
% 12.93/4.76  tff(c_18948, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_88, c_1071, c_18932])).
% 12.93/4.76  tff(c_1087, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1070, c_26])).
% 12.93/4.76  tff(c_1099, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_1087])).
% 12.93/4.76  tff(c_1467, plain, (k10_relat_1('#skF_4', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1456, c_1099])).
% 12.93/4.76  tff(c_20, plain, (![A_10]: (k9_relat_1(A_10, k1_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.93/4.76  tff(c_19010, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_18948, c_20])).
% 12.93/4.76  tff(c_19049, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14773, c_19010])).
% 12.93/4.76  tff(c_36, plain, (![B_22, A_21]: (k9_relat_1(k2_funct_1(B_22), A_21)=k10_relat_1(B_22, A_21) | ~v2_funct_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.93/4.76  tff(c_19117, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k10_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_19049, c_36])).
% 12.93/4.76  tff(c_19128, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_88, c_1467, c_19117])).
% 12.93/4.76  tff(c_990, plain, (![A_165]: (m1_subset_1(A_165, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_165), k2_relat_1(A_165)))) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_171])).
% 12.93/4.76  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.93/4.76  tff(c_1023, plain, (![A_165]: (r1_tarski(A_165, k2_zfmisc_1(k1_relat_1(A_165), k2_relat_1(A_165))) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165))), inference(resolution, [status(thm)], [c_990, c_16])).
% 12.93/4.76  tff(c_19148, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_19128, c_1023])).
% 12.93/4.76  tff(c_19181, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14773, c_174, c_18948, c_19148])).
% 12.93/4.76  tff(c_19183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_19181])).
% 12.93/4.76  tff(c_19184, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1454])).
% 12.93/4.76  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 12.93/4.76  tff(c_19247, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19184, c_2])).
% 12.93/4.76  tff(c_19249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_681, c_19247])).
% 12.93/4.76  tff(c_19250, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_678])).
% 12.93/4.76  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 12.93/4.76  tff(c_19255, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_19250, c_4])).
% 12.93/4.76  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.93/4.76  tff(c_19276, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19255, c_19255, c_10])).
% 12.93/4.76  tff(c_19251, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_678])).
% 12.93/4.76  tff(c_19259, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_19251, c_4])).
% 12.93/4.76  tff(c_19288, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19255, c_19259])).
% 12.93/4.76  tff(c_306, plain, (![B_90, A_91]: (v1_xboole_0(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_91)) | ~v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.93/4.76  tff(c_330, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_306])).
% 12.93/4.76  tff(c_386, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_330])).
% 12.93/4.76  tff(c_19291, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19288, c_386])).
% 12.93/4.76  tff(c_19424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19250, c_19276, c_19291])).
% 12.93/4.76  tff(c_19425, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_330])).
% 12.93/4.76  tff(c_19430, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_19425, c_4])).
% 12.93/4.76  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.93/4.76  tff(c_244, plain, (![A_82, B_83]: (m1_subset_1('#skF_1'(A_82, B_83), k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 12.93/4.76  tff(c_256, plain, (![B_4]: (m1_subset_1('#skF_1'(k1_xboole_0, B_4), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_244])).
% 12.93/4.76  tff(c_309, plain, (![B_4]: (v1_xboole_0('#skF_1'(k1_xboole_0, B_4)) | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_256, c_306])).
% 12.93/4.76  tff(c_331, plain, (![B_92]: (v1_xboole_0('#skF_1'(k1_xboole_0, B_92)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_309])).
% 12.93/4.76  tff(c_335, plain, (![B_92]: ('#skF_1'(k1_xboole_0, B_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_331, c_4])).
% 12.93/4.76  tff(c_343, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_256])).
% 12.93/4.76  tff(c_19551, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_19430, c_343])).
% 12.93/4.76  tff(c_74, plain, (![A_43, B_44]: (v1_relat_1('#skF_1'(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_161])).
% 12.93/4.76  tff(c_66, plain, (![A_43, B_44]: (v1_funct_2('#skF_1'(A_43, B_44), A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_161])).
% 12.93/4.76  tff(c_76, plain, (![A_43, B_44]: (m1_subset_1('#skF_1'(A_43, B_44), k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 12.93/4.76  tff(c_26404, plain, (![A_52905, B_52906, C_52907]: (k1_relset_1(A_52905, B_52906, C_52907)=k1_relat_1(C_52907) | ~m1_subset_1(C_52907, k1_zfmisc_1(k2_zfmisc_1(A_52905, B_52906))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.93/4.76  tff(c_26422, plain, (![A_43, B_44]: (k1_relset_1(A_43, B_44, '#skF_1'(A_43, B_44))=k1_relat_1('#skF_1'(A_43, B_44)))), inference(resolution, [status(thm)], [c_76, c_26404])).
% 12.93/4.76  tff(c_64, plain, (![B_41, A_40, C_42]: (k1_xboole_0=B_41 | k1_relset_1(A_40, B_41, C_42)=A_40 | ~v1_funct_2(C_42, A_40, B_41) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.93/4.76  tff(c_27017, plain, (![B_52955, A_52956, C_52957]: (B_52955='#skF_4' | k1_relset_1(A_52956, B_52955, C_52957)=A_52956 | ~v1_funct_2(C_52957, A_52956, B_52955) | ~m1_subset_1(C_52957, k1_zfmisc_1(k2_zfmisc_1(A_52956, B_52955))))), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_64])).
% 12.93/4.76  tff(c_27032, plain, (![B_44, A_43]: (B_44='#skF_4' | k1_relset_1(A_43, B_44, '#skF_1'(A_43, B_44))=A_43 | ~v1_funct_2('#skF_1'(A_43, B_44), A_43, B_44))), inference(resolution, [status(thm)], [c_76, c_27017])).
% 12.93/4.76  tff(c_27046, plain, (![B_52958, A_52959]: (B_52958='#skF_4' | k1_relat_1('#skF_1'(A_52959, B_52958))=A_52959)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_26422, c_27032])).
% 12.93/4.76  tff(c_232, plain, (![A_81]: (k10_relat_1(A_81, k2_relat_1(A_81))=k1_relat_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.93/4.76  tff(c_238, plain, (![A_81]: (r1_tarski(k1_relat_1(A_81), k1_relat_1(A_81)) | ~v1_relat_1(A_81) | ~v1_relat_1(A_81))), inference(superposition, [status(thm), theory('equality')], [c_232, c_24])).
% 12.93/4.76  tff(c_27066, plain, (![A_52959, B_52958]: (r1_tarski(k1_relat_1('#skF_1'(A_52959, B_52958)), A_52959) | ~v1_relat_1('#skF_1'(A_52959, B_52958)) | ~v1_relat_1('#skF_1'(A_52959, B_52958)) | B_52958='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_27046, c_238])).
% 12.93/4.76  tff(c_27863, plain, (![A_59201, B_59202]: (r1_tarski(k1_relat_1('#skF_1'(A_59201, B_59202)), A_59201) | B_59202='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_27066])).
% 12.93/4.76  tff(c_329, plain, (![A_8, B_9]: (v1_xboole_0(A_8) | ~v1_xboole_0(B_9) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_18, c_306])).
% 12.93/4.76  tff(c_28501, plain, (![A_59224, B_59225]: (v1_xboole_0(k1_relat_1('#skF_1'(A_59224, B_59225))) | ~v1_xboole_0(A_59224) | B_59225='#skF_4')), inference(resolution, [status(thm)], [c_27863, c_329])).
% 12.93/4.76  tff(c_19439, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_4])).
% 12.93/4.76  tff(c_28655, plain, (![A_59236, B_59237]: (k1_relat_1('#skF_1'(A_59236, B_59237))='#skF_4' | ~v1_xboole_0(A_59236) | B_59237='#skF_4')), inference(resolution, [status(thm)], [c_28501, c_19439])).
% 12.93/4.76  tff(c_27063, plain, (![A_52959, B_52958]: (r1_tarski(A_52959, k1_relat_1('#skF_1'(A_52959, B_52958))) | ~v1_relat_1('#skF_1'(A_52959, B_52958)) | ~v1_relat_1('#skF_1'(A_52959, B_52958)) | B_52958='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_27046, c_238])).
% 12.93/4.76  tff(c_27098, plain, (![A_52959, B_52958]: (r1_tarski(A_52959, k1_relat_1('#skF_1'(A_52959, B_52958))) | B_52958='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_27063])).
% 12.93/4.76  tff(c_28677, plain, (![A_59236, B_59237]: (r1_tarski(A_59236, '#skF_4') | B_59237='#skF_4' | ~v1_xboole_0(A_59236) | B_59237='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28655, c_27098])).
% 12.93/4.76  tff(c_28930, plain, (![B_59237]: (B_59237='#skF_4' | B_59237='#skF_4')), inference(splitLeft, [status(thm)], [c_28677])).
% 12.93/4.76  tff(c_29331, plain, (![B_64731]: (B_64731='#skF_4')), inference(factorization, [status(thm), theory('equality')], [c_28930])).
% 12.93/4.76  tff(c_19440, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_19430, c_12])).
% 12.93/4.76  tff(c_19438, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_19430, c_10])).
% 12.93/4.76  tff(c_19431, plain, (![B_92]: ('#skF_1'('#skF_4', B_92)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_19430, c_335])).
% 12.93/4.76  tff(c_20428, plain, (![A_39324, B_39325, C_39326]: (k1_relset_1(A_39324, B_39325, C_39326)=k1_relat_1(C_39326) | ~m1_subset_1(C_39326, k1_zfmisc_1(k2_zfmisc_1(A_39324, B_39325))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.93/4.76  tff(c_20485, plain, (![A_39328, B_39329]: (k1_relset_1(A_39328, B_39329, '#skF_1'(A_39328, B_39329))=k1_relat_1('#skF_1'(A_39328, B_39329)))), inference(resolution, [status(thm)], [c_76, c_20428])).
% 12.93/4.76  tff(c_20497, plain, (![B_92]: (k1_relat_1('#skF_1'('#skF_4', B_92))=k1_relset_1('#skF_4', B_92, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_19431, c_20485])).
% 12.93/4.76  tff(c_20503, plain, (![B_92]: (k1_relset_1('#skF_4', B_92, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19431, c_20497])).
% 12.93/4.76  tff(c_62, plain, (![B_41, C_42]: (k1_relset_1(k1_xboole_0, B_41, C_42)=k1_xboole_0 | ~v1_funct_2(C_42, k1_xboole_0, B_41) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_41))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.93/4.76  tff(c_95, plain, (![B_41, C_42]: (k1_relset_1(k1_xboole_0, B_41, C_42)=k1_xboole_0 | ~v1_funct_2(C_42, k1_xboole_0, B_41) | ~m1_subset_1(C_42, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_62])).
% 12.93/4.76  tff(c_20569, plain, (![B_39340, C_39341]: (k1_relset_1('#skF_4', B_39340, C_39341)='#skF_4' | ~v1_funct_2(C_39341, '#skF_4', B_39340) | ~m1_subset_1(C_39341, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_19430, c_19430, c_19430, c_95])).
% 12.93/4.76  tff(c_20580, plain, (![B_44]: (k1_relset_1('#skF_4', B_44, '#skF_1'('#skF_4', B_44))='#skF_4' | ~m1_subset_1('#skF_1'('#skF_4', B_44), k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_66, c_20569])).
% 12.93/4.76  tff(c_20592, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19551, c_19431, c_20503, c_19431, c_20580])).
% 12.93/4.76  tff(c_38, plain, (![A_23]: (k2_relat_1(k2_funct_1(A_23))=k1_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.93/4.76  tff(c_20450, plain, (![A_43, B_44]: (k1_relset_1(A_43, B_44, '#skF_1'(A_43, B_44))=k1_relat_1('#skF_1'(A_43, B_44)))), inference(resolution, [status(thm)], [c_76, c_20428])).
% 12.93/4.76  tff(c_20883, plain, (![B_39365, A_39366, C_39367]: (B_39365='#skF_4' | k1_relset_1(A_39366, B_39365, C_39367)=A_39366 | ~v1_funct_2(C_39367, A_39366, B_39365) | ~m1_subset_1(C_39367, k1_zfmisc_1(k2_zfmisc_1(A_39366, B_39365))))), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_64])).
% 12.93/4.76  tff(c_20898, plain, (![B_44, A_43]: (B_44='#skF_4' | k1_relset_1(A_43, B_44, '#skF_1'(A_43, B_44))=A_43 | ~v1_funct_2('#skF_1'(A_43, B_44), A_43, B_44))), inference(resolution, [status(thm)], [c_76, c_20883])).
% 12.93/4.76  tff(c_20912, plain, (![B_39368, A_39369]: (B_39368='#skF_4' | k1_relat_1('#skF_1'(A_39369, B_39368))=A_39369)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_20450, c_20898])).
% 12.93/4.76  tff(c_20932, plain, (![A_39369, B_39368]: (r1_tarski(k1_relat_1('#skF_1'(A_39369, B_39368)), A_39369) | ~v1_relat_1('#skF_1'(A_39369, B_39368)) | ~v1_relat_1('#skF_1'(A_39369, B_39368)) | B_39368='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20912, c_238])).
% 12.93/4.76  tff(c_21702, plain, (![A_45416, B_45417]: (r1_tarski(k1_relat_1('#skF_1'(A_45416, B_45417)), A_45416) | B_45417='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_20932])).
% 12.93/4.76  tff(c_22465, plain, (![A_45447, B_45448]: (v1_xboole_0(k1_relat_1('#skF_1'(A_45447, B_45448))) | ~v1_xboole_0(A_45447) | B_45448='#skF_4')), inference(resolution, [status(thm)], [c_21702, c_329])).
% 12.93/4.76  tff(c_22593, plain, (![A_45457, B_45458]: (k1_relat_1('#skF_1'(A_45457, B_45458))='#skF_4' | ~v1_xboole_0(A_45457) | B_45458='#skF_4')), inference(resolution, [status(thm)], [c_22465, c_19439])).
% 12.93/4.76  tff(c_20929, plain, (![A_39369, B_39368]: (r1_tarski(A_39369, k1_relat_1('#skF_1'(A_39369, B_39368))) | ~v1_relat_1('#skF_1'(A_39369, B_39368)) | ~v1_relat_1('#skF_1'(A_39369, B_39368)) | B_39368='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20912, c_238])).
% 12.93/4.76  tff(c_20964, plain, (![A_39369, B_39368]: (r1_tarski(A_39369, k1_relat_1('#skF_1'(A_39369, B_39368))) | B_39368='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_20929])).
% 12.93/4.76  tff(c_22615, plain, (![A_45457, B_45458]: (r1_tarski(A_45457, '#skF_4') | B_45458='#skF_4' | ~v1_xboole_0(A_45457) | B_45458='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22593, c_20964])).
% 12.93/4.76  tff(c_22859, plain, (![B_45458]: (B_45458='#skF_4' | B_45458='#skF_4')), inference(splitLeft, [status(thm)], [c_22615])).
% 12.93/4.76  tff(c_23251, plain, (![B_50750]: (B_50750='#skF_4')), inference(factorization, [status(thm), theory('equality')], [c_22859])).
% 12.93/4.76  tff(c_19426, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_330])).
% 12.93/4.76  tff(c_19463, plain, (![A_39234]: (A_39234='#skF_4' | ~v1_xboole_0(A_39234))), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_4])).
% 12.93/4.76  tff(c_19470, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_19426, c_19463])).
% 12.93/4.76  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.93/4.76  tff(c_19449, plain, (![B_4, A_3]: (B_4='#skF_4' | A_3='#skF_4' | k2_zfmisc_1(A_3, B_4)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_19430, c_19430, c_8])).
% 12.93/4.76  tff(c_19620, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_19470, c_19449])).
% 12.93/4.76  tff(c_19691, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_19620])).
% 12.93/4.76  tff(c_19695, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_19691, c_195])).
% 12.93/4.76  tff(c_19701, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19438, c_19695])).
% 12.93/4.76  tff(c_23434, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_23251, c_19701])).
% 12.93/4.76  tff(c_23526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19551, c_23434])).
% 12.93/4.76  tff(c_23528, plain, (![A_52711]: (r1_tarski(A_52711, '#skF_4') | ~v1_xboole_0(A_52711))), inference(splitRight, [status(thm)], [c_22615])).
% 12.93/4.76  tff(c_19694, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19691, c_205])).
% 12.93/4.76  tff(c_19700, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19438, c_19694])).
% 12.93/4.76  tff(c_23561, plain, (~v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_23528, c_19700])).
% 12.93/4.76  tff(c_20158, plain, (![A_39305, B_39306, C_39307]: (k2_relset_1(A_39305, B_39306, C_39307)=k2_relat_1(C_39307) | ~m1_subset_1(C_39307, k1_zfmisc_1(k2_zfmisc_1(A_39305, B_39306))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.93/4.76  tff(c_20184, plain, (![A_39312, B_39313]: (k2_relset_1(A_39312, B_39313, '#skF_1'(A_39312, B_39313))=k2_relat_1('#skF_1'(A_39312, B_39313)))), inference(resolution, [status(thm)], [c_76, c_20158])).
% 12.93/4.76  tff(c_20196, plain, (![B_92]: (k2_relat_1('#skF_1'('#skF_4', B_92))=k2_relset_1('#skF_4', B_92, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_19431, c_20184])).
% 12.93/4.76  tff(c_20242, plain, (![B_39315]: (k2_relset_1('#skF_4', B_39315, '#skF_4')=k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19431, c_20196])).
% 12.93/4.76  tff(c_19696, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19691, c_86])).
% 12.93/4.76  tff(c_20246, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_20242, c_19696])).
% 12.93/4.76  tff(c_253, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_244])).
% 12.93/4.76  tff(c_312, plain, (![A_3]: (v1_xboole_0('#skF_1'(A_3, k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_253, c_306])).
% 12.93/4.76  tff(c_336, plain, (![A_93]: (v1_xboole_0('#skF_1'(A_93, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_312])).
% 12.93/4.76  tff(c_340, plain, (![A_93]: ('#skF_1'(A_93, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_336, c_4])).
% 12.93/4.76  tff(c_19566, plain, (![A_39241]: ('#skF_1'(A_39241, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_19430, c_340])).
% 12.93/4.76  tff(c_72, plain, (![A_43, B_44]: (v4_relat_1('#skF_1'(A_43, B_44), A_43))), inference(cnfTransformation, [status(thm)], [f_161])).
% 12.93/4.76  tff(c_19583, plain, (![A_39241]: (v4_relat_1('#skF_4', A_39241))), inference(superposition, [status(thm), theory('equality')], [c_19566, c_72])).
% 12.93/4.76  tff(c_19716, plain, (![B_39250, A_39251]: (k7_relat_1(B_39250, A_39251)=B_39250 | ~v4_relat_1(B_39250, A_39251) | ~v1_relat_1(B_39250))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.93/4.76  tff(c_19719, plain, (![A_39241]: (k7_relat_1('#skF_4', A_39241)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_19583, c_19716])).
% 12.93/4.76  tff(c_19725, plain, (![A_39241]: (k7_relat_1('#skF_4', A_39241)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_19719])).
% 12.93/4.76  tff(c_19747, plain, (![B_39253, A_39254]: (k2_relat_1(k7_relat_1(B_39253, A_39254))=k9_relat_1(B_39253, A_39254) | ~v1_relat_1(B_39253))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.93/4.76  tff(c_19759, plain, (![A_39241]: (k9_relat_1('#skF_4', A_39241)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_19725, c_19747])).
% 12.93/4.76  tff(c_19763, plain, (![A_39241]: (k9_relat_1('#skF_4', A_39241)=k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_19759])).
% 12.93/4.76  tff(c_20254, plain, (![A_39241]: (k9_relat_1('#skF_4', A_39241)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20246, c_19763])).
% 12.93/4.76  tff(c_20750, plain, (![B_39351, A_39352]: (k10_relat_1(k2_funct_1(B_39351), A_39352)=k9_relat_1(B_39351, A_39352) | ~v2_funct_1(B_39351) | ~v1_funct_1(B_39351) | ~v1_relat_1(B_39351))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.93/4.76  tff(c_24961, plain, (![B_52795, A_52796]: (r1_tarski(k9_relat_1(B_52795, A_52796), k1_relat_1(k2_funct_1(B_52795))) | ~v1_relat_1(k2_funct_1(B_52795)) | ~v2_funct_1(B_52795) | ~v1_funct_1(B_52795) | ~v1_relat_1(B_52795))), inference(superposition, [status(thm), theory('equality')], [c_20750, c_24])).
% 12.93/4.76  tff(c_24973, plain, (r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20254, c_24961])).
% 12.93/4.76  tff(c_24987, plain, (r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_88, c_24973])).
% 12.93/4.76  tff(c_24990, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_24987])).
% 12.93/4.76  tff(c_24993, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_24990])).
% 12.93/4.76  tff(c_24997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_24993])).
% 12.93/4.76  tff(c_24999, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_24987])).
% 12.93/4.76  tff(c_20067, plain, (![A_39293]: (k2_relat_1(k2_funct_1(A_39293))=k1_relat_1(A_39293) | ~v2_funct_1(A_39293) | ~v1_funct_1(A_39293) | ~v1_relat_1(A_39293))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.93/4.76  tff(c_25469, plain, (![A_52821]: (k10_relat_1(k2_funct_1(A_52821), k1_relat_1(A_52821))=k1_relat_1(k2_funct_1(A_52821)) | ~v1_relat_1(k2_funct_1(A_52821)) | ~v2_funct_1(A_52821) | ~v1_funct_1(A_52821) | ~v1_relat_1(A_52821))), inference(superposition, [status(thm), theory('equality')], [c_20067, c_26])).
% 12.93/4.76  tff(c_25513, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20592, c_25469])).
% 12.93/4.76  tff(c_25533, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_88, c_24999, c_25513])).
% 12.93/4.76  tff(c_25542, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k9_relat_1('#skF_4', '#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25533, c_34])).
% 12.93/4.76  tff(c_25558, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_88, c_20254, c_25542])).
% 12.93/4.76  tff(c_20204, plain, (![A_39314]: (m1_subset_1(A_39314, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_39314), k2_relat_1(A_39314)))) | ~v1_funct_1(A_39314) | ~v1_relat_1(A_39314))), inference(cnfTransformation, [status(thm)], [f_171])).
% 12.93/4.76  tff(c_14, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.93/4.76  tff(c_20239, plain, (![A_39314]: (v1_xboole_0(A_39314) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_39314), k2_relat_1(A_39314))) | ~v1_funct_1(A_39314) | ~v1_relat_1(A_39314))), inference(resolution, [status(thm)], [c_20204, c_14])).
% 12.93/4.76  tff(c_25587, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_25558, c_20239])).
% 12.93/4.76  tff(c_25631, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_24999, c_174, c_25587])).
% 12.93/4.76  tff(c_25632, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_23561, c_25631])).
% 12.93/4.76  tff(c_25662, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_25632])).
% 12.93/4.76  tff(c_25666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_88, c_19425, c_19438, c_20592, c_25662])).
% 12.93/4.76  tff(c_25667, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_19620])).
% 12.93/4.76  tff(c_25671, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_25667, c_195])).
% 12.93/4.76  tff(c_25676, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19440, c_25671])).
% 12.93/4.76  tff(c_29506, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_29331, c_25676])).
% 12.93/4.76  tff(c_29602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19551, c_29506])).
% 12.93/4.76  tff(c_29604, plain, (![A_66672]: (r1_tarski(A_66672, '#skF_4') | ~v1_xboole_0(A_66672))), inference(splitRight, [status(thm)], [c_28677])).
% 12.93/4.76  tff(c_25670, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_25667, c_205])).
% 12.93/4.76  tff(c_25675, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19440, c_25670])).
% 12.93/4.76  tff(c_29637, plain, (~v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_29604, c_25675])).
% 12.93/4.76  tff(c_19563, plain, (![A_93]: ('#skF_1'(A_93, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_19430, c_340])).
% 12.93/4.76  tff(c_26137, plain, (![A_52881, B_52882, C_52883]: (k2_relset_1(A_52881, B_52882, C_52883)=k2_relat_1(C_52883) | ~m1_subset_1(C_52883, k1_zfmisc_1(k2_zfmisc_1(A_52881, B_52882))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.93/4.76  tff(c_26160, plain, (![A_52886, B_52887]: (k2_relset_1(A_52886, B_52887, '#skF_1'(A_52886, B_52887))=k2_relat_1('#skF_1'(A_52886, B_52887)))), inference(resolution, [status(thm)], [c_76, c_26137])).
% 12.93/4.76  tff(c_26175, plain, (![A_93]: (k2_relat_1('#skF_1'(A_93, '#skF_4'))=k2_relset_1(A_93, '#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_19563, c_26160])).
% 12.93/4.76  tff(c_26187, plain, (![A_52889]: (k2_relset_1(A_52889, '#skF_4', '#skF_4')=k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19563, c_26175])).
% 12.93/4.76  tff(c_25672, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25667, c_25667, c_86])).
% 12.93/4.76  tff(c_26194, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_26187, c_25672])).
% 12.93/4.76  tff(c_26078, plain, (![A_52874]: (k1_relat_1(k2_funct_1(A_52874))=k2_relat_1(A_52874) | ~v2_funct_1(A_52874) | ~v1_funct_1(A_52874) | ~v1_relat_1(A_52874))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.93/4.76  tff(c_31741, plain, (![A_66784, A_66785]: (r1_tarski(k10_relat_1(k2_funct_1(A_66784), A_66785), k2_relat_1(A_66784)) | ~v1_relat_1(k2_funct_1(A_66784)) | ~v2_funct_1(A_66784) | ~v1_funct_1(A_66784) | ~v1_relat_1(A_66784))), inference(superposition, [status(thm), theory('equality')], [c_26078, c_24])).
% 12.93/4.76  tff(c_31762, plain, (![A_66785]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_4'), A_66785), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26194, c_31741])).
% 12.93/4.76  tff(c_31783, plain, (![A_66785]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_4'), A_66785), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_88, c_31762])).
% 12.93/4.76  tff(c_31784, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_31783])).
% 12.93/4.76  tff(c_31787, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_31784])).
% 12.93/4.76  tff(c_31791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_31787])).
% 12.93/4.76  tff(c_31793, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_31783])).
% 12.93/4.76  tff(c_31794, plain, (![A_66786]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_4'), A_66786), '#skF_4'))), inference(splitRight, [status(thm)], [c_31783])).
% 12.93/4.76  tff(c_25825, plain, (![C_52842, B_52843, A_52844]: (v1_xboole_0(C_52842) | ~m1_subset_1(C_52842, k1_zfmisc_1(k2_zfmisc_1(B_52843, A_52844))) | ~v1_xboole_0(A_52844))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.93/4.76  tff(c_25828, plain, (![C_52842]: (v1_xboole_0(C_52842) | ~m1_subset_1(C_52842, k1_zfmisc_1('#skF_4')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_19438, c_25825])).
% 12.93/4.76  tff(c_25857, plain, (![C_52847]: (v1_xboole_0(C_52847) | ~m1_subset_1(C_52847, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_19425, c_25828])).
% 12.93/4.76  tff(c_25867, plain, (![A_8]: (v1_xboole_0(A_8) | ~r1_tarski(A_8, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_25857])).
% 12.93/4.76  tff(c_31836, plain, (![A_66787]: (v1_xboole_0(k10_relat_1(k2_funct_1('#skF_4'), A_66787)))), inference(resolution, [status(thm)], [c_31794, c_25867])).
% 12.93/4.76  tff(c_31866, plain, (v1_xboole_0(k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_31836])).
% 12.93/4.76  tff(c_31880, plain, (v1_xboole_0(k1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_31793, c_31866])).
% 12.93/4.76  tff(c_31925, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_31880, c_19439])).
% 12.93/4.76  tff(c_26329, plain, (![A_52901]: (m1_subset_1(A_52901, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_52901), k2_relat_1(A_52901)))) | ~v1_funct_1(A_52901) | ~v1_relat_1(A_52901))), inference(cnfTransformation, [status(thm)], [f_171])).
% 12.93/4.76  tff(c_26367, plain, (![A_52901]: (v1_xboole_0(A_52901) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_52901), k2_relat_1(A_52901))) | ~v1_funct_1(A_52901) | ~v1_relat_1(A_52901))), inference(resolution, [status(thm)], [c_26329, c_14])).
% 12.93/4.76  tff(c_31949, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4')))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_31925, c_26367])).
% 12.93/4.76  tff(c_31990, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31793, c_174, c_19425, c_19440, c_31949])).
% 12.93/4.76  tff(c_31992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29637, c_31990])).
% 12.93/4.76  tff(c_31994, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_173])).
% 12.93/4.76  tff(c_32570, plain, (![C_66850, B_66851, A_66852]: (v1_xboole_0(C_66850) | ~m1_subset_1(C_66850, k1_zfmisc_1(k2_zfmisc_1(B_66851, A_66852))) | ~v1_xboole_0(A_66852))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.93/4.76  tff(c_32591, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_31994, c_32570])).
% 12.93/4.76  tff(c_32597, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_32591])).
% 12.93/4.76  tff(c_32936, plain, (![A_66890, B_66891, C_66892]: (k2_relset_1(A_66890, B_66891, C_66892)=k2_relat_1(C_66892) | ~m1_subset_1(C_66892, k1_zfmisc_1(k2_zfmisc_1(A_66890, B_66891))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 12.93/4.76  tff(c_32949, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_32936])).
% 12.93/4.76  tff(c_32960, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_32949])).
% 12.93/4.76  tff(c_40, plain, (![A_23]: (k1_relat_1(k2_funct_1(A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.93/4.76  tff(c_31993, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_173])).
% 12.93/4.76  tff(c_32823, plain, (![A_66875, B_66876, C_66877]: (k1_relset_1(A_66875, B_66876, C_66877)=k1_relat_1(C_66877) | ~m1_subset_1(C_66877, k1_zfmisc_1(k2_zfmisc_1(A_66875, B_66876))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 12.93/4.76  tff(c_32844, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_31994, c_32823])).
% 12.93/4.76  tff(c_33474, plain, (![B_66913, C_66914, A_66915]: (k1_xboole_0=B_66913 | v1_funct_2(C_66914, A_66915, B_66913) | k1_relset_1(A_66915, B_66913, C_66914)!=A_66915 | ~m1_subset_1(C_66914, k1_zfmisc_1(k2_zfmisc_1(A_66915, B_66913))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.93/4.76  tff(c_33486, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_31994, c_33474])).
% 12.93/4.76  tff(c_33507, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32844, c_33486])).
% 12.93/4.76  tff(c_33508, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_31993, c_33507])).
% 12.93/4.76  tff(c_33515, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_33508])).
% 12.93/4.76  tff(c_33518, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_33515])).
% 12.93/4.76  tff(c_33521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_94, c_88, c_32960, c_33518])).
% 12.93/4.76  tff(c_33522, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_33508])).
% 12.93/4.76  tff(c_33563, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33522, c_2])).
% 12.93/4.76  tff(c_33565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32597, c_33563])).
% 12.93/4.76  tff(c_33567, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_32591])).
% 12.93/4.76  tff(c_33571, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_33567, c_4])).
% 12.93/4.76  tff(c_33590, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33571, c_33571, c_10])).
% 12.93/4.76  tff(c_32101, plain, (![B_66801, A_66802]: (v1_xboole_0(B_66801) | ~m1_subset_1(B_66801, k1_zfmisc_1(A_66802)) | ~v1_xboole_0(A_66802))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.93/4.76  tff(c_32127, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_31994, c_32101])).
% 12.93/4.76  tff(c_32272, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_32127])).
% 12.93/4.76  tff(c_33717, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33590, c_32272])).
% 12.93/4.76  tff(c_33720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33567, c_33717])).
% 12.93/4.76  tff(c_33722, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_32127])).
% 12.93/4.76  tff(c_33730, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_33722, c_4])).
% 12.93/4.76  tff(c_33775, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_33730, c_8])).
% 12.93/4.76  tff(c_33777, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_33775])).
% 12.93/4.76  tff(c_33796, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33777, c_2])).
% 12.93/4.76  tff(c_33792, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33777, c_33777, c_10])).
% 12.93/4.76  tff(c_32129, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_32101])).
% 12.93/4.76  tff(c_32226, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_32129])).
% 12.93/4.76  tff(c_33914, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33792, c_32226])).
% 12.93/4.76  tff(c_33919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33796, c_33914])).
% 12.93/4.76  tff(c_33920, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_33775])).
% 12.93/4.76  tff(c_33940, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33920, c_2])).
% 12.93/4.76  tff(c_33938, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33920, c_33920, c_12])).
% 12.93/4.76  tff(c_34002, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33938, c_32226])).
% 12.93/4.76  tff(c_34007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33940, c_34002])).
% 12.93/4.76  tff(c_34008, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_32129])).
% 12.93/4.76  tff(c_34038, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34008, c_4])).
% 12.93/4.76  tff(c_34048, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34038, c_34038, c_10])).
% 12.93/4.76  tff(c_34050, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34038, c_34038, c_12])).
% 12.93/4.76  tff(c_34009, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_32129])).
% 12.93/4.76  tff(c_34125, plain, (![A_66945]: (A_66945='#skF_4' | ~v1_xboole_0(A_66945))), inference(demodulation, [status(thm), theory('equality')], [c_34038, c_4])).
% 12.93/4.76  tff(c_34132, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_34009, c_34125])).
% 12.93/4.76  tff(c_34713, plain, (![B_66997, A_66998]: (B_66997='#skF_4' | A_66998='#skF_4' | k2_zfmisc_1(A_66998, B_66997)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34038, c_34038, c_34038, c_8])).
% 12.93/4.76  tff(c_34723, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_34132, c_34713])).
% 12.93/4.76  tff(c_34728, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_34723])).
% 12.93/4.76  tff(c_34332, plain, (![C_66958, B_66959, A_66960]: (v1_xboole_0(C_66958) | ~m1_subset_1(C_66958, k1_zfmisc_1(k2_zfmisc_1(B_66959, A_66960))) | ~v1_xboole_0(A_66960))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.93/4.76  tff(c_34355, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_31994, c_34332])).
% 12.93/4.76  tff(c_34357, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_34355])).
% 12.93/4.76  tff(c_34730, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34728, c_34357])).
% 12.93/4.76  tff(c_34742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34008, c_34730])).
% 12.93/4.76  tff(c_34743, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_34723])).
% 12.93/4.76  tff(c_34253, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_32127])).
% 12.93/4.76  tff(c_34748, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34743, c_34253])).
% 12.93/4.76  tff(c_34759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34008, c_34050, c_34748])).
% 12.93/4.76  tff(c_34761, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_34355])).
% 12.93/4.76  tff(c_34049, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_34038, c_4])).
% 12.93/4.76  tff(c_34765, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_34761, c_34049])).
% 12.93/4.76  tff(c_34768, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34765, c_34253])).
% 12.93/4.76  tff(c_34778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34008, c_34048, c_34768])).
% 12.93/4.76  tff(c_34779, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_32127])).
% 12.93/4.76  tff(c_34784, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_34779, c_34049])).
% 12.93/4.76  tff(c_34814, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34784, c_31993])).
% 12.93/4.76  tff(c_34780, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_32127])).
% 12.93/4.76  tff(c_34838, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_34780, c_34049])).
% 12.93/4.76  tff(c_34851, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34838, c_76])).
% 12.93/4.76  tff(c_34863, plain, (![C_67002, B_67003, A_67004]: (v1_xboole_0(C_67002) | ~m1_subset_1(C_67002, k1_zfmisc_1(k2_zfmisc_1(B_67003, A_67004))) | ~v1_xboole_0(A_67004))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.93/4.76  tff(c_34872, plain, (![C_67002]: (v1_xboole_0(C_67002) | ~m1_subset_1(C_67002, k1_zfmisc_1('#skF_4')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34048, c_34863])).
% 12.93/4.76  tff(c_34884, plain, (![C_67002]: (v1_xboole_0(C_67002) | ~m1_subset_1(C_67002, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34008, c_34872])).
% 12.93/4.76  tff(c_35083, plain, (v1_xboole_0('#skF_1'('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_34851, c_34884])).
% 12.93/4.76  tff(c_35131, plain, ('#skF_1'('#skF_3', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_35083, c_34049])).
% 12.93/4.76  tff(c_35161, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35131, c_66])).
% 12.93/4.76  tff(c_35177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34814, c_35161])).
% 12.93/4.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.93/4.76  
% 12.93/4.76  Inference rules
% 12.93/4.76  ----------------------
% 12.93/4.76  #Ref     : 0
% 12.93/4.76  #Sup     : 7418
% 12.93/4.76  #Fact    : 32
% 12.93/4.76  #Define  : 0
% 12.93/4.76  #Split   : 32
% 12.93/4.76  #Chain   : 0
% 12.93/4.76  #Close   : 0
% 12.93/4.76  
% 12.93/4.76  Ordering : KBO
% 12.93/4.76  
% 12.93/4.76  Simplification rules
% 12.93/4.76  ----------------------
% 12.93/4.76  #Subsume      : 1615
% 12.93/4.76  #Demod        : 7089
% 12.93/4.76  #Tautology    : 3264
% 12.93/4.76  #SimpNegUnit  : 14
% 12.93/4.76  #BackRed      : 341
% 12.93/4.76  
% 12.93/4.76  #Partial instantiations: 5787
% 12.93/4.76  #Strategies tried      : 1
% 12.93/4.76  
% 12.93/4.76  Timing (in seconds)
% 12.93/4.76  ----------------------
% 12.93/4.77  Preprocessing        : 0.58
% 12.93/4.77  Parsing              : 0.34
% 12.93/4.77  CNF conversion       : 0.03
% 12.93/4.77  Main loop            : 3.34
% 12.93/4.77  Inferencing          : 1.19
% 12.93/4.77  Reduction            : 1.17
% 12.93/4.77  Demodulation         : 0.88
% 12.93/4.77  BG Simplification    : 0.10
% 12.93/4.77  Subsumption          : 0.67
% 12.93/4.77  Abstraction          : 0.14
% 12.93/4.77  MUC search           : 0.00
% 12.93/4.77  Cooper               : 0.00
% 12.93/4.77  Total                : 4.06
% 12.93/4.77  Index Insertion      : 0.00
% 12.93/4.77  Index Deletion       : 0.00
% 12.93/4.77  Index Matching       : 0.00
% 12.93/4.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
