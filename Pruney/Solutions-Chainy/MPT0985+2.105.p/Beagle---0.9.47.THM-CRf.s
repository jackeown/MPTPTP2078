%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:43 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.40s
% Verified   : 
% Statistics : Number of formulae       :  245 (2329 expanded)
%              Number of leaves         :   50 ( 803 expanded)
%              Depth                    :   19
%              Number of atoms          :  415 (7038 expanded)
%              Number of equality atoms :  138 (1783 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(f_148,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_206,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_124,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_166,axiom,(
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

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_189,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_113,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_179,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_56,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_1'(A_38),A_38)
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_98,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_314,plain,(
    ! [C_98,B_99,A_100] :
      ( v1_xboole_0(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(B_99,A_100)))
      | ~ v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_332,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_314])).

tff(c_337,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_193,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_205,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_193])).

tff(c_102,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_28,plain,(
    ! [A_14] :
      ( v1_funct_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_92,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_215,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_218,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_215])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_218])).

tff(c_223,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_274,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_30,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_224,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_96,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_639,plain,(
    ! [A_153,B_154,C_155] :
      ( k1_relset_1(A_153,B_154,C_155) = k1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_657,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_639])).

tff(c_1229,plain,(
    ! [B_201,A_202,C_203] :
      ( k1_xboole_0 = B_201
      | k1_relset_1(A_202,B_201,C_203) = A_202
      | ~ v1_funct_2(C_203,A_202,B_201)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1241,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_1229])).

tff(c_1261,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_657,c_1241])).

tff(c_1265,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1261])).

tff(c_94,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_587,plain,(
    ! [A_146,B_147,C_148] :
      ( k2_relset_1(A_146,B_147,C_148) = k2_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_593,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_587])).

tff(c_606,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_593])).

tff(c_22,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1299,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_22])).

tff(c_1315,plain,(
    k9_relat_1('#skF_5','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_606,c_1299])).

tff(c_40,plain,(
    ! [A_20,B_22] :
      ( k9_relat_1(k2_funct_1(A_20),k9_relat_1(A_20,B_22)) = B_22
      | ~ r1_tarski(B_22,k1_relat_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1333,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_40])).

tff(c_1337,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_96,c_8,c_1265,c_1333])).

tff(c_1400,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')),'#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1337,c_40])).

tff(c_1404,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')),'#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_1400])).

tff(c_1662,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1404])).

tff(c_1665,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_1662])).

tff(c_1669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_1665])).

tff(c_1671,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_44,plain,(
    ! [A_23] :
      ( k1_relat_1(k2_funct_1(A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1670,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')),'#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1404])).

tff(c_1672,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1670])).

tff(c_1675,plain,
    ( ~ r1_tarski('#skF_4',k2_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1672])).

tff(c_1678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_96,c_8,c_606,c_1675])).

tff(c_1680,plain,(
    r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1670])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1686,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1680,c_4])).

tff(c_1721,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1686])).

tff(c_1726,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1721])).

tff(c_1729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_96,c_8,c_606,c_1726])).

tff(c_1730,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1686])).

tff(c_1757,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_4') = k2_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1730,c_22])).

tff(c_1778,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_1337,c_1757])).

tff(c_86,plain,(
    ! [A_58] :
      ( m1_subset_1(A_58,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_58),k2_relat_1(A_58))))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1810,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1778,c_86])).

tff(c_1844,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1671,c_224,c_1730,c_1810])).

tff(c_1846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_1844])).

tff(c_1847,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1261])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1888,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_2])).

tff(c_1890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_1888])).

tff(c_1892,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_3940,plain,(
    ! [A_392,B_393,C_394] :
      ( k1_relset_1(A_392,B_393,C_394) = k1_relat_1(C_394)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3966,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_3940])).

tff(c_4431,plain,(
    ! [B_433,A_434,C_435] :
      ( k1_xboole_0 = B_433
      | k1_relset_1(A_434,B_433,C_435) = A_434
      | ~ v1_funct_2(C_435,A_434,B_433)
      | ~ m1_subset_1(C_435,k1_zfmisc_1(k2_zfmisc_1(A_434,B_433))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_4443,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_4431])).

tff(c_4463,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_3966,c_4443])).

tff(c_4467,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4463])).

tff(c_3853,plain,(
    ! [A_387,B_388,C_389] :
      ( k2_relset_1(A_387,B_388,C_389) = k2_relat_1(C_389)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_387,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3862,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_3853])).

tff(c_3876,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3862])).

tff(c_4495,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4467,c_22])).

tff(c_4507,plain,(
    k9_relat_1('#skF_5','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_3876,c_4495])).

tff(c_4530,plain,(
    ! [A_436,B_437] :
      ( k9_relat_1(k2_funct_1(A_436),k9_relat_1(A_436,B_437)) = B_437
      | ~ r1_tarski(B_437,k1_relat_1(A_436))
      | ~ v2_funct_1(A_436)
      | ~ v1_funct_1(A_436)
      | ~ v1_relat_1(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4545,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4507,c_4530])).

tff(c_4564,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_96,c_8,c_4467,c_4545])).

tff(c_4578,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')),'#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4564,c_40])).

tff(c_4582,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')),'#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_4578])).

tff(c_4950,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4582])).

tff(c_4953,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_4950])).

tff(c_4957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_4953])).

tff(c_4959,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4582])).

tff(c_4958,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')),'#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4582])).

tff(c_5065,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_4958])).

tff(c_5068,plain,
    ( ~ r1_tarski('#skF_4',k2_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_5065])).

tff(c_5071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_96,c_8,c_3876,c_5068])).

tff(c_5073,plain,(
    r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_4958])).

tff(c_5079,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5073,c_4])).

tff(c_5083,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5079])).

tff(c_5086,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_5083])).

tff(c_5089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_96,c_8,c_3876,c_5086])).

tff(c_5090,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5079])).

tff(c_5117,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_4') = k2_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5090,c_22])).

tff(c_5138,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4959,c_4564,c_5117])).

tff(c_5213,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5138,c_86])).

tff(c_5247,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4959,c_224,c_5090,c_5213])).

tff(c_5249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_5247])).

tff(c_5250,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4463])).

tff(c_12,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5288,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5250,c_12])).

tff(c_3885,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3876,c_86])).

tff(c_3897,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_3885])).

tff(c_20,plain,(
    ! [C_11,B_10,A_9] :
      ( ~ v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3933,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))
      | ~ r2_hidden(A_9,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3897,c_20])).

tff(c_3983,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3933])).

tff(c_5485,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5288,c_3983])).

tff(c_5492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1892,c_5485])).

tff(c_5495,plain,(
    ! [A_477] : ~ r2_hidden(A_477,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3933])).

tff(c_5500,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_5495])).

tff(c_16,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5525,plain,(
    ! [A_5] : m1_subset_1('#skF_5',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5500,c_16])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_151,plain,(
    ! [A_73] : k2_funct_1(k6_relat_1(A_73)) = k6_relat_1(A_73) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_160,plain,(
    k6_relat_1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_151])).

tff(c_163,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_160])).

tff(c_5523,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5500,c_5500,c_163])).

tff(c_5590,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5523,c_274])).

tff(c_5810,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5525,c_5590])).

tff(c_5812,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_6001,plain,(
    ! [C_517,B_518,A_519] :
      ( v1_xboole_0(C_517)
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(B_518,A_519)))
      | ~ v1_xboole_0(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6021,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5812,c_6001])).

tff(c_6029,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6021])).

tff(c_6829,plain,(
    ! [A_616,B_617,C_618] :
      ( k2_relset_1(A_616,B_617,C_618) = k2_relat_1(C_618)
      | ~ m1_subset_1(C_618,k1_zfmisc_1(k2_zfmisc_1(A_616,B_617))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6841,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_6829])).

tff(c_6856,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_6841])).

tff(c_5811,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_6733,plain,(
    ! [A_602,B_603,C_604] :
      ( k1_relset_1(A_602,B_603,C_604) = k1_relat_1(C_604)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(A_602,B_603))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6757,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5812,c_6733])).

tff(c_7346,plain,(
    ! [B_652,C_653,A_654] :
      ( k1_xboole_0 = B_652
      | v1_funct_2(C_653,A_654,B_652)
      | k1_relset_1(A_654,B_652,C_653) != A_654
      | ~ m1_subset_1(C_653,k1_zfmisc_1(k2_zfmisc_1(A_654,B_652))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_7355,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_5812,c_7346])).

tff(c_7377,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6757,c_7355])).

tff(c_7378,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5811,c_7377])).

tff(c_7386,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7378])).

tff(c_7389,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_7386])).

tff(c_7392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_96,c_6856,c_7389])).

tff(c_7393,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7378])).

tff(c_7433,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7393,c_2])).

tff(c_7435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6029,c_7433])).

tff(c_7437,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6021])).

tff(c_8022,plain,(
    ! [A_723,B_724,C_725] :
      ( k2_relset_1(A_723,B_724,C_725) = k2_relat_1(C_725)
      | ~ m1_subset_1(C_725,k1_zfmisc_1(k2_zfmisc_1(A_723,B_724))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8034,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_8022])).

tff(c_8049,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_8034])).

tff(c_7905,plain,(
    ! [A_708,B_709,C_710] :
      ( k1_relset_1(A_708,B_709,C_710) = k1_relat_1(C_710)
      | ~ m1_subset_1(C_710,k1_zfmisc_1(k2_zfmisc_1(A_708,B_709))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_7925,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5812,c_7905])).

tff(c_8487,plain,(
    ! [B_757,C_758,A_759] :
      ( k1_xboole_0 = B_757
      | v1_funct_2(C_758,A_759,B_757)
      | k1_relset_1(A_759,B_757,C_758) != A_759
      | ~ m1_subset_1(C_758,k1_zfmisc_1(k2_zfmisc_1(A_759,B_757))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_8493,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_5812,c_8487])).

tff(c_8512,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7925,c_8493])).

tff(c_8513,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5811,c_8512])).

tff(c_8522,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8513])).

tff(c_8525,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_8522])).

tff(c_8528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_96,c_8049,c_8525])).

tff(c_8529,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8513])).

tff(c_14,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8565,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8529,c_8529,c_14])).

tff(c_5828,plain,(
    ! [C_492,B_493,A_494] :
      ( ~ v1_xboole_0(C_492)
      | ~ m1_subset_1(B_493,k1_zfmisc_1(C_492))
      | ~ r2_hidden(A_494,B_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5849,plain,(
    ! [A_494] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_494,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_98,c_5828])).

tff(c_5851,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5849])).

tff(c_8690,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8565,c_5851])).

tff(c_8694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7437,c_8690])).

tff(c_8697,plain,(
    ! [A_763] : ~ r2_hidden(A_763,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5849])).

tff(c_8702,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_8697])).

tff(c_8711,plain,(
    ! [A_5] : m1_subset_1('#skF_5',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8702,c_16])).

tff(c_8871,plain,(
    ! [A_784] :
      ( r2_hidden('#skF_1'(A_784),A_784)
      | A_784 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8702,c_56])).

tff(c_241,plain,(
    ! [A_87,B_88] : m1_subset_1('#skF_2'(A_87,B_88),k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_247,plain,(
    ! [B_4] : m1_subset_1('#skF_2'(k1_xboole_0,B_4),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_241])).

tff(c_5834,plain,(
    ! [A_494,B_4] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_494,'#skF_2'(k1_xboole_0,B_4)) ) ),
    inference(resolution,[status(thm)],[c_247,c_5828])).

tff(c_5847,plain,(
    ! [A_494,B_4] : ~ r2_hidden(A_494,'#skF_2'(k1_xboole_0,B_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5834])).

tff(c_8822,plain,(
    ! [A_494,B_4] : ~ r2_hidden(A_494,'#skF_2'('#skF_5',B_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8702,c_5847])).

tff(c_8885,plain,(
    ! [B_4] : '#skF_2'('#skF_5',B_4) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8871,c_8822])).

tff(c_8709,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8702,c_8702,c_163])).

tff(c_8991,plain,(
    ! [A_796] :
      ( k2_relat_1(k2_funct_1(A_796)) = k1_relat_1(A_796)
      | ~ v2_funct_1(A_796)
      | ~ v1_funct_1(A_796)
      | ~ v1_relat_1(A_796) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_9006,plain,
    ( k2_relat_1('#skF_5') = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8709,c_8991])).

tff(c_9013,plain,(
    k2_relat_1('#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_102,c_96,c_9006])).

tff(c_9202,plain,(
    ! [A_821,B_822,C_823] :
      ( k2_relset_1(A_821,B_822,C_823) = k2_relat_1(C_823)
      | ~ m1_subset_1(C_823,k1_zfmisc_1(k2_zfmisc_1(A_821,B_822))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_9212,plain,(
    ! [A_821,B_822] : k2_relset_1(A_821,B_822,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8711,c_9202])).

tff(c_9243,plain,(
    ! [A_827,B_828] : k2_relset_1(A_827,B_828,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9013,c_9212])).

tff(c_9247,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9243,c_94])).

tff(c_9223,plain,(
    ! [A_824,B_825,C_826] :
      ( k1_relset_1(A_824,B_825,C_826) = k1_relat_1(C_826)
      | ~ m1_subset_1(C_826,k1_zfmisc_1(k2_zfmisc_1(A_824,B_825))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_9241,plain,(
    ! [A_824,B_825] : k1_relset_1(A_824,B_825,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8711,c_9223])).

tff(c_9343,plain,(
    ! [A_824,B_825] : k1_relset_1(A_824,B_825,'#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9247,c_9241])).

tff(c_74,plain,(
    ! [A_55,B_56] : v1_funct_2('#skF_2'(A_55,B_56),A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_70,plain,(
    ! [B_53,C_54] :
      ( k1_relset_1(k1_xboole_0,B_53,C_54) = k1_xboole_0
      | ~ v1_funct_2(C_54,k1_xboole_0,B_53)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_105,plain,(
    ! [B_53,C_54] :
      ( k1_relset_1(k1_xboole_0,B_53,C_54) = k1_xboole_0
      | ~ v1_funct_2(C_54,k1_xboole_0,B_53)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_70])).

tff(c_9560,plain,(
    ! [B_856,C_857] :
      ( k1_relset_1('#skF_5',B_856,C_857) = '#skF_5'
      | ~ v1_funct_2(C_857,'#skF_5',B_856)
      | ~ m1_subset_1(C_857,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8702,c_8702,c_8702,c_8702,c_105])).

tff(c_9568,plain,(
    ! [B_56] :
      ( k1_relset_1('#skF_5',B_56,'#skF_2'('#skF_5',B_56)) = '#skF_5'
      | ~ m1_subset_1('#skF_2'('#skF_5',B_56),k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_74,c_9560])).

tff(c_9577,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8711,c_8885,c_9343,c_8885,c_9568])).

tff(c_8934,plain,(
    ! [B_787] : '#skF_2'('#skF_5',B_787) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8871,c_8822])).

tff(c_8948,plain,(
    ! [B_787] : v1_funct_2('#skF_5','#skF_5',B_787) ),
    inference(superposition,[status(thm),theory(equality)],[c_8934,c_74])).

tff(c_9601,plain,(
    ! [B_787] : v1_funct_2('#skF_4','#skF_4',B_787) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9577,c_9577,c_8948])).

tff(c_8740,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8709,c_5811])).

tff(c_9611,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9577,c_8740])).

tff(c_10015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9601,c_9611])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.16/2.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.63  
% 7.40/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 7.40/2.63  
% 7.40/2.63  %Foreground sorts:
% 7.40/2.63  
% 7.40/2.63  
% 7.40/2.63  %Background operators:
% 7.40/2.63  
% 7.40/2.63  
% 7.40/2.63  %Foreground operators:
% 7.40/2.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.40/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.40/2.63  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.40/2.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.40/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.40/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.40/2.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.40/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.40/2.63  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.40/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.40/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.40/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.40/2.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.40/2.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.40/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.40/2.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.40/2.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.40/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.40/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.40/2.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.40/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.40/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.40/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.40/2.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.40/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.40/2.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.40/2.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.40/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.40/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.40/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.40/2.63  
% 7.40/2.66  tff(f_148, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 7.40/2.66  tff(f_206, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 7.40/2.66  tff(f_124, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.40/2.66  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.40/2.66  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.40/2.66  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.40/2.66  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.40/2.66  tff(f_166, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.40/2.66  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.40/2.66  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 7.40/2.66  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 7.40/2.66  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.40/2.66  tff(f_189, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 7.40/2.66  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.40/2.66  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.40/2.66  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.40/2.66  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.40/2.66  tff(f_62, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 7.40/2.66  tff(f_113, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 7.40/2.66  tff(f_179, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 7.40/2.66  tff(c_56, plain, (![A_38]: (r2_hidden('#skF_1'(A_38), A_38) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.40/2.66  tff(c_98, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.40/2.66  tff(c_314, plain, (![C_98, B_99, A_100]: (v1_xboole_0(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(B_99, A_100))) | ~v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.40/2.66  tff(c_332, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_98, c_314])).
% 7.40/2.66  tff(c_337, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_332])).
% 7.40/2.66  tff(c_193, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.40/2.66  tff(c_205, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_193])).
% 7.40/2.66  tff(c_102, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.40/2.66  tff(c_28, plain, (![A_14]: (v1_funct_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.40/2.66  tff(c_92, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.40/2.66  tff(c_215, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_92])).
% 7.40/2.66  tff(c_218, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_215])).
% 7.40/2.66  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_218])).
% 7.40/2.66  tff(c_223, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_92])).
% 7.40/2.66  tff(c_274, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_223])).
% 7.40/2.66  tff(c_30, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.40/2.66  tff(c_224, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_92])).
% 7.40/2.66  tff(c_96, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.40/2.66  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.40/2.66  tff(c_100, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.40/2.66  tff(c_639, plain, (![A_153, B_154, C_155]: (k1_relset_1(A_153, B_154, C_155)=k1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.40/2.66  tff(c_657, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_639])).
% 7.40/2.66  tff(c_1229, plain, (![B_201, A_202, C_203]: (k1_xboole_0=B_201 | k1_relset_1(A_202, B_201, C_203)=A_202 | ~v1_funct_2(C_203, A_202, B_201) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.40/2.66  tff(c_1241, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_98, c_1229])).
% 7.40/2.66  tff(c_1261, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_657, c_1241])).
% 7.40/2.66  tff(c_1265, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1261])).
% 7.40/2.66  tff(c_94, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.40/2.66  tff(c_587, plain, (![A_146, B_147, C_148]: (k2_relset_1(A_146, B_147, C_148)=k2_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.40/2.66  tff(c_593, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_587])).
% 7.40/2.66  tff(c_606, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_593])).
% 7.40/2.66  tff(c_22, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.40/2.66  tff(c_1299, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1265, c_22])).
% 7.40/2.66  tff(c_1315, plain, (k9_relat_1('#skF_5', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_205, c_606, c_1299])).
% 7.40/2.66  tff(c_40, plain, (![A_20, B_22]: (k9_relat_1(k2_funct_1(A_20), k9_relat_1(A_20, B_22))=B_22 | ~r1_tarski(B_22, k1_relat_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.40/2.66  tff(c_1333, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1315, c_40])).
% 7.40/2.66  tff(c_1337, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_96, c_8, c_1265, c_1333])).
% 7.40/2.66  tff(c_1400, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')), '#skF_3')='#skF_4' | ~r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5'))) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1337, c_40])).
% 7.40/2.66  tff(c_1404, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')), '#skF_3')='#skF_4' | ~r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5'))) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_1400])).
% 7.40/2.66  tff(c_1662, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1404])).
% 7.40/2.66  tff(c_1665, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_1662])).
% 7.40/2.66  tff(c_1669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_1665])).
% 7.40/2.66  tff(c_1671, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1404])).
% 7.40/2.66  tff(c_44, plain, (![A_23]: (k1_relat_1(k2_funct_1(A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.40/2.66  tff(c_1670, plain, (~v2_funct_1(k2_funct_1('#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')), '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1404])).
% 7.40/2.66  tff(c_1672, plain, (~r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_1670])).
% 7.40/2.66  tff(c_1675, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_44, c_1672])).
% 7.40/2.66  tff(c_1678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_96, c_8, c_606, c_1675])).
% 7.40/2.66  tff(c_1680, plain, (r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5')))), inference(splitRight, [status(thm)], [c_1670])).
% 7.40/2.66  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.40/2.66  tff(c_1686, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_1680, c_4])).
% 7.40/2.66  tff(c_1721, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_1686])).
% 7.40/2.66  tff(c_1726, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_44, c_1721])).
% 7.40/2.66  tff(c_1729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_96, c_8, c_606, c_1726])).
% 7.40/2.66  tff(c_1730, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4'), inference(splitRight, [status(thm)], [c_1686])).
% 7.40/2.66  tff(c_1757, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_4')=k2_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1730, c_22])).
% 7.40/2.66  tff(c_1778, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_1337, c_1757])).
% 7.40/2.66  tff(c_86, plain, (![A_58]: (m1_subset_1(A_58, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_58), k2_relat_1(A_58)))) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.40/2.66  tff(c_1810, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1778, c_86])).
% 7.40/2.66  tff(c_1844, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1671, c_224, c_1730, c_1810])).
% 7.40/2.66  tff(c_1846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_1844])).
% 7.40/2.66  tff(c_1847, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1261])).
% 7.40/2.66  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.40/2.66  tff(c_1888, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_2])).
% 7.40/2.66  tff(c_1890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_337, c_1888])).
% 7.40/2.66  tff(c_1892, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_332])).
% 7.40/2.66  tff(c_3940, plain, (![A_392, B_393, C_394]: (k1_relset_1(A_392, B_393, C_394)=k1_relat_1(C_394) | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.40/2.66  tff(c_3966, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_3940])).
% 7.40/2.66  tff(c_4431, plain, (![B_433, A_434, C_435]: (k1_xboole_0=B_433 | k1_relset_1(A_434, B_433, C_435)=A_434 | ~v1_funct_2(C_435, A_434, B_433) | ~m1_subset_1(C_435, k1_zfmisc_1(k2_zfmisc_1(A_434, B_433))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.40/2.66  tff(c_4443, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_98, c_4431])).
% 7.40/2.66  tff(c_4463, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_3966, c_4443])).
% 7.40/2.66  tff(c_4467, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_4463])).
% 7.40/2.66  tff(c_3853, plain, (![A_387, B_388, C_389]: (k2_relset_1(A_387, B_388, C_389)=k2_relat_1(C_389) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_387, B_388))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.40/2.66  tff(c_3862, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_3853])).
% 7.40/2.66  tff(c_3876, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_3862])).
% 7.40/2.66  tff(c_4495, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4467, c_22])).
% 7.40/2.66  tff(c_4507, plain, (k9_relat_1('#skF_5', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_205, c_3876, c_4495])).
% 7.40/2.66  tff(c_4530, plain, (![A_436, B_437]: (k9_relat_1(k2_funct_1(A_436), k9_relat_1(A_436, B_437))=B_437 | ~r1_tarski(B_437, k1_relat_1(A_436)) | ~v2_funct_1(A_436) | ~v1_funct_1(A_436) | ~v1_relat_1(A_436))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.40/2.66  tff(c_4545, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4507, c_4530])).
% 7.40/2.66  tff(c_4564, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_96, c_8, c_4467, c_4545])).
% 7.40/2.66  tff(c_4578, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')), '#skF_3')='#skF_4' | ~r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5'))) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4564, c_40])).
% 7.40/2.66  tff(c_4582, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')), '#skF_3')='#skF_4' | ~r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5'))) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_4578])).
% 7.40/2.66  tff(c_4950, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4582])).
% 7.40/2.66  tff(c_4953, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_4950])).
% 7.40/2.66  tff(c_4957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_4953])).
% 7.40/2.66  tff(c_4959, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_4582])).
% 7.40/2.66  tff(c_4958, plain, (~v2_funct_1(k2_funct_1('#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_5')), '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_4582])).
% 7.40/2.66  tff(c_5065, plain, (~r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_4958])).
% 7.40/2.66  tff(c_5068, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_44, c_5065])).
% 7.40/2.66  tff(c_5071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_96, c_8, c_3876, c_5068])).
% 7.40/2.66  tff(c_5073, plain, (r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5')))), inference(splitRight, [status(thm)], [c_4958])).
% 7.40/2.66  tff(c_5079, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_5073, c_4])).
% 7.40/2.66  tff(c_5083, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_5079])).
% 7.40/2.66  tff(c_5086, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_44, c_5083])).
% 7.40/2.66  tff(c_5089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_96, c_8, c_3876, c_5086])).
% 7.40/2.66  tff(c_5090, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4'), inference(splitRight, [status(thm)], [c_5079])).
% 7.40/2.66  tff(c_5117, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_4')=k2_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5090, c_22])).
% 7.40/2.66  tff(c_5138, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4959, c_4564, c_5117])).
% 7.40/2.66  tff(c_5213, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5138, c_86])).
% 7.40/2.66  tff(c_5247, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4959, c_224, c_5090, c_5213])).
% 7.40/2.66  tff(c_5249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_5247])).
% 7.40/2.66  tff(c_5250, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4463])).
% 7.40/2.66  tff(c_12, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.40/2.66  tff(c_5288, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5250, c_12])).
% 7.40/2.66  tff(c_3885, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3876, c_86])).
% 7.40/2.66  tff(c_3897, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_3885])).
% 7.40/2.66  tff(c_20, plain, (![C_11, B_10, A_9]: (~v1_xboole_0(C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.40/2.66  tff(c_3933, plain, (![A_9]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')) | ~r2_hidden(A_9, '#skF_5'))), inference(resolution, [status(thm)], [c_3897, c_20])).
% 7.40/2.66  tff(c_3983, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_3933])).
% 7.40/2.66  tff(c_5485, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5288, c_3983])).
% 7.40/2.66  tff(c_5492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1892, c_5485])).
% 7.40/2.66  tff(c_5495, plain, (![A_477]: (~r2_hidden(A_477, '#skF_5'))), inference(splitRight, [status(thm)], [c_3933])).
% 7.40/2.66  tff(c_5500, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_56, c_5495])).
% 7.40/2.66  tff(c_16, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.40/2.66  tff(c_5525, plain, (![A_5]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_5500, c_16])).
% 7.40/2.66  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.40/2.66  tff(c_151, plain, (![A_73]: (k2_funct_1(k6_relat_1(A_73))=k6_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.40/2.66  tff(c_160, plain, (k6_relat_1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_151])).
% 7.40/2.66  tff(c_163, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_160])).
% 7.40/2.66  tff(c_5523, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5500, c_5500, c_163])).
% 7.40/2.66  tff(c_5590, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5523, c_274])).
% 7.40/2.66  tff(c_5810, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5525, c_5590])).
% 7.40/2.66  tff(c_5812, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_223])).
% 7.40/2.66  tff(c_6001, plain, (![C_517, B_518, A_519]: (v1_xboole_0(C_517) | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(B_518, A_519))) | ~v1_xboole_0(A_519))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.40/2.66  tff(c_6021, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_5812, c_6001])).
% 7.40/2.66  tff(c_6029, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_6021])).
% 7.40/2.66  tff(c_6829, plain, (![A_616, B_617, C_618]: (k2_relset_1(A_616, B_617, C_618)=k2_relat_1(C_618) | ~m1_subset_1(C_618, k1_zfmisc_1(k2_zfmisc_1(A_616, B_617))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.40/2.66  tff(c_6841, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_6829])).
% 7.40/2.66  tff(c_6856, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_6841])).
% 7.40/2.66  tff(c_5811, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_223])).
% 7.40/2.66  tff(c_6733, plain, (![A_602, B_603, C_604]: (k1_relset_1(A_602, B_603, C_604)=k1_relat_1(C_604) | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(A_602, B_603))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.40/2.66  tff(c_6757, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_5812, c_6733])).
% 7.40/2.66  tff(c_7346, plain, (![B_652, C_653, A_654]: (k1_xboole_0=B_652 | v1_funct_2(C_653, A_654, B_652) | k1_relset_1(A_654, B_652, C_653)!=A_654 | ~m1_subset_1(C_653, k1_zfmisc_1(k2_zfmisc_1(A_654, B_652))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.40/2.66  tff(c_7355, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_5812, c_7346])).
% 7.40/2.66  tff(c_7377, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6757, c_7355])).
% 7.40/2.66  tff(c_7378, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5811, c_7377])).
% 7.40/2.66  tff(c_7386, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_7378])).
% 7.40/2.66  tff(c_7389, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_44, c_7386])).
% 7.40/2.66  tff(c_7392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_96, c_6856, c_7389])).
% 7.40/2.66  tff(c_7393, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_7378])).
% 7.40/2.66  tff(c_7433, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7393, c_2])).
% 7.40/2.66  tff(c_7435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6029, c_7433])).
% 7.40/2.66  tff(c_7437, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_6021])).
% 7.40/2.66  tff(c_8022, plain, (![A_723, B_724, C_725]: (k2_relset_1(A_723, B_724, C_725)=k2_relat_1(C_725) | ~m1_subset_1(C_725, k1_zfmisc_1(k2_zfmisc_1(A_723, B_724))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.40/2.66  tff(c_8034, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_8022])).
% 7.40/2.66  tff(c_8049, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_8034])).
% 7.40/2.66  tff(c_7905, plain, (![A_708, B_709, C_710]: (k1_relset_1(A_708, B_709, C_710)=k1_relat_1(C_710) | ~m1_subset_1(C_710, k1_zfmisc_1(k2_zfmisc_1(A_708, B_709))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.40/2.66  tff(c_7925, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_5812, c_7905])).
% 7.40/2.66  tff(c_8487, plain, (![B_757, C_758, A_759]: (k1_xboole_0=B_757 | v1_funct_2(C_758, A_759, B_757) | k1_relset_1(A_759, B_757, C_758)!=A_759 | ~m1_subset_1(C_758, k1_zfmisc_1(k2_zfmisc_1(A_759, B_757))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.40/2.66  tff(c_8493, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_5812, c_8487])).
% 7.40/2.66  tff(c_8512, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7925, c_8493])).
% 7.40/2.66  tff(c_8513, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5811, c_8512])).
% 7.40/2.66  tff(c_8522, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_8513])).
% 7.40/2.66  tff(c_8525, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_44, c_8522])).
% 7.40/2.66  tff(c_8528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_96, c_8049, c_8525])).
% 7.40/2.66  tff(c_8529, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_8513])).
% 7.40/2.66  tff(c_14, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.40/2.66  tff(c_8565, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8529, c_8529, c_14])).
% 7.40/2.66  tff(c_5828, plain, (![C_492, B_493, A_494]: (~v1_xboole_0(C_492) | ~m1_subset_1(B_493, k1_zfmisc_1(C_492)) | ~r2_hidden(A_494, B_493))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.40/2.66  tff(c_5849, plain, (![A_494]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_494, '#skF_5'))), inference(resolution, [status(thm)], [c_98, c_5828])).
% 7.40/2.66  tff(c_5851, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_5849])).
% 7.40/2.66  tff(c_8690, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8565, c_5851])).
% 7.40/2.66  tff(c_8694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7437, c_8690])).
% 7.40/2.66  tff(c_8697, plain, (![A_763]: (~r2_hidden(A_763, '#skF_5'))), inference(splitRight, [status(thm)], [c_5849])).
% 7.40/2.66  tff(c_8702, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_56, c_8697])).
% 7.40/2.66  tff(c_8711, plain, (![A_5]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_8702, c_16])).
% 7.40/2.66  tff(c_8871, plain, (![A_784]: (r2_hidden('#skF_1'(A_784), A_784) | A_784='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8702, c_56])).
% 7.40/2.66  tff(c_241, plain, (![A_87, B_88]: (m1_subset_1('#skF_2'(A_87, B_88), k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.40/2.66  tff(c_247, plain, (![B_4]: (m1_subset_1('#skF_2'(k1_xboole_0, B_4), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_241])).
% 7.40/2.66  tff(c_5834, plain, (![A_494, B_4]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_494, '#skF_2'(k1_xboole_0, B_4)))), inference(resolution, [status(thm)], [c_247, c_5828])).
% 7.40/2.66  tff(c_5847, plain, (![A_494, B_4]: (~r2_hidden(A_494, '#skF_2'(k1_xboole_0, B_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_5834])).
% 7.40/2.66  tff(c_8822, plain, (![A_494, B_4]: (~r2_hidden(A_494, '#skF_2'('#skF_5', B_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8702, c_5847])).
% 7.40/2.66  tff(c_8885, plain, (![B_4]: ('#skF_2'('#skF_5', B_4)='#skF_5')), inference(resolution, [status(thm)], [c_8871, c_8822])).
% 7.40/2.66  tff(c_8709, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8702, c_8702, c_163])).
% 7.40/2.66  tff(c_8991, plain, (![A_796]: (k2_relat_1(k2_funct_1(A_796))=k1_relat_1(A_796) | ~v2_funct_1(A_796) | ~v1_funct_1(A_796) | ~v1_relat_1(A_796))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.40/2.66  tff(c_9006, plain, (k2_relat_1('#skF_5')=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8709, c_8991])).
% 7.40/2.66  tff(c_9013, plain, (k2_relat_1('#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_102, c_96, c_9006])).
% 7.40/2.66  tff(c_9202, plain, (![A_821, B_822, C_823]: (k2_relset_1(A_821, B_822, C_823)=k2_relat_1(C_823) | ~m1_subset_1(C_823, k1_zfmisc_1(k2_zfmisc_1(A_821, B_822))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.40/2.66  tff(c_9212, plain, (![A_821, B_822]: (k2_relset_1(A_821, B_822, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_8711, c_9202])).
% 7.40/2.66  tff(c_9243, plain, (![A_827, B_828]: (k2_relset_1(A_827, B_828, '#skF_5')=k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_9013, c_9212])).
% 7.40/2.66  tff(c_9247, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_9243, c_94])).
% 7.40/2.66  tff(c_9223, plain, (![A_824, B_825, C_826]: (k1_relset_1(A_824, B_825, C_826)=k1_relat_1(C_826) | ~m1_subset_1(C_826, k1_zfmisc_1(k2_zfmisc_1(A_824, B_825))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.40/2.66  tff(c_9241, plain, (![A_824, B_825]: (k1_relset_1(A_824, B_825, '#skF_5')=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_8711, c_9223])).
% 7.40/2.66  tff(c_9343, plain, (![A_824, B_825]: (k1_relset_1(A_824, B_825, '#skF_5')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9247, c_9241])).
% 7.40/2.66  tff(c_74, plain, (![A_55, B_56]: (v1_funct_2('#skF_2'(A_55, B_56), A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.40/2.66  tff(c_70, plain, (![B_53, C_54]: (k1_relset_1(k1_xboole_0, B_53, C_54)=k1_xboole_0 | ~v1_funct_2(C_54, k1_xboole_0, B_53) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_53))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.40/2.66  tff(c_105, plain, (![B_53, C_54]: (k1_relset_1(k1_xboole_0, B_53, C_54)=k1_xboole_0 | ~v1_funct_2(C_54, k1_xboole_0, B_53) | ~m1_subset_1(C_54, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_70])).
% 7.40/2.66  tff(c_9560, plain, (![B_856, C_857]: (k1_relset_1('#skF_5', B_856, C_857)='#skF_5' | ~v1_funct_2(C_857, '#skF_5', B_856) | ~m1_subset_1(C_857, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8702, c_8702, c_8702, c_8702, c_105])).
% 7.40/2.66  tff(c_9568, plain, (![B_56]: (k1_relset_1('#skF_5', B_56, '#skF_2'('#skF_5', B_56))='#skF_5' | ~m1_subset_1('#skF_2'('#skF_5', B_56), k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_74, c_9560])).
% 7.40/2.66  tff(c_9577, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8711, c_8885, c_9343, c_8885, c_9568])).
% 7.40/2.66  tff(c_8934, plain, (![B_787]: ('#skF_2'('#skF_5', B_787)='#skF_5')), inference(resolution, [status(thm)], [c_8871, c_8822])).
% 7.40/2.66  tff(c_8948, plain, (![B_787]: (v1_funct_2('#skF_5', '#skF_5', B_787))), inference(superposition, [status(thm), theory('equality')], [c_8934, c_74])).
% 7.40/2.66  tff(c_9601, plain, (![B_787]: (v1_funct_2('#skF_4', '#skF_4', B_787))), inference(demodulation, [status(thm), theory('equality')], [c_9577, c_9577, c_8948])).
% 7.40/2.66  tff(c_8740, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8709, c_5811])).
% 7.40/2.66  tff(c_9611, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9577, c_8740])).
% 7.40/2.66  tff(c_10015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9601, c_9611])).
% 7.40/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.66  
% 7.40/2.66  Inference rules
% 7.40/2.66  ----------------------
% 7.40/2.66  #Ref     : 0
% 7.40/2.66  #Sup     : 2175
% 7.40/2.66  #Fact    : 0
% 7.40/2.66  #Define  : 0
% 7.40/2.66  #Split   : 41
% 7.40/2.66  #Chain   : 0
% 7.40/2.66  #Close   : 0
% 7.40/2.66  
% 7.40/2.66  Ordering : KBO
% 7.40/2.66  
% 7.40/2.66  Simplification rules
% 7.40/2.66  ----------------------
% 7.40/2.66  #Subsume      : 242
% 7.40/2.66  #Demod        : 3450
% 7.40/2.66  #Tautology    : 1263
% 7.40/2.66  #SimpNegUnit  : 9
% 7.40/2.66  #BackRed      : 520
% 7.40/2.66  
% 7.40/2.66  #Partial instantiations: 0
% 7.40/2.66  #Strategies tried      : 1
% 7.40/2.66  
% 7.40/2.66  Timing (in seconds)
% 7.40/2.66  ----------------------
% 7.40/2.67  Preprocessing        : 0.37
% 7.40/2.67  Parsing              : 0.19
% 7.40/2.67  CNF conversion       : 0.02
% 7.40/2.67  Main loop            : 1.47
% 7.40/2.67  Inferencing          : 0.51
% 7.40/2.67  Reduction            : 0.55
% 7.40/2.67  Demodulation         : 0.40
% 7.40/2.67  BG Simplification    : 0.06
% 7.40/2.67  Subsumption          : 0.23
% 7.40/2.67  Abstraction          : 0.06
% 7.40/2.67  MUC search           : 0.00
% 7.40/2.67  Cooper               : 0.00
% 7.40/2.67  Total                : 1.91
% 7.40/2.67  Index Insertion      : 0.00
% 7.40/2.67  Index Deletion       : 0.00
% 7.40/2.67  Index Matching       : 0.00
% 7.40/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
