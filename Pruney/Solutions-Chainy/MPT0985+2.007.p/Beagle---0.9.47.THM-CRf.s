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
% DateTime   : Thu Dec  3 10:12:26 EST 2020

% Result     : Theorem 15.27s
% Output     : CNFRefutation 15.50s
% Verified   : 
% Statistics : Number of formulae       :  248 (2124 expanded)
%              Number of leaves         :   53 ( 723 expanded)
%              Depth                    :   22
%              Number of atoms          :  445 (5545 expanded)
%              Number of equality atoms :  148 (1219 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_227,negated_conjecture,(
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

tff(f_156,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_170,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_152,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_127,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_166,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_188,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_198,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_162,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_36215,plain,(
    ! [C_739,A_740,B_741] :
      ( v1_relat_1(C_739)
      | ~ m1_subset_1(C_739,k1_zfmisc_1(k2_zfmisc_1(A_740,B_741))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_36228,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_36215])).

tff(c_116,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_110,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_108,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_37546,plain,(
    ! [A_831,B_832,C_833] :
      ( k2_relset_1(A_831,B_832,C_833) = k2_relat_1(C_833)
      | ~ m1_subset_1(C_833,k1_zfmisc_1(k2_zfmisc_1(A_831,B_832))) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_37556,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_37546])).

tff(c_37560,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_37556])).

tff(c_70,plain,(
    ! [A_33] :
      ( k1_relat_1(k2_funct_1(A_33)) = k2_relat_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_644,plain,(
    ! [C_126,A_127,B_128] :
      ( v1_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_653,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_644])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,(
    ! [A_28] :
      ( v1_funct_1(k2_funct_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_106,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_201,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_204,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_201])).

tff(c_207,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_204])).

tff(c_265,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_272,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_265])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_272])).

tff(c_278,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_335,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_633,plain,(
    ~ r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_335])).

tff(c_1909,plain,(
    ! [A_213,B_214,C_215] :
      ( k2_relset_1(A_213,B_214,C_215) = k2_relat_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1922,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_1909])).

tff(c_1928,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1922])).

tff(c_60,plain,(
    ! [A_28] :
      ( v1_relat_1(k2_funct_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_712,plain,(
    ! [A_138,B_139] :
      ( r2_hidden('#skF_2'(A_138,B_139),A_138)
      | r1_tarski(A_138,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_755,plain,(
    ! [A_142,B_143] :
      ( ~ v1_xboole_0(A_142)
      | r1_tarski(A_142,B_143) ) ),
    inference(resolution,[status(thm)],[c_712,c_2])).

tff(c_771,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_755,c_633])).

tff(c_1462,plain,(
    ! [A_175] :
      ( k4_relat_1(A_175) = k2_funct_1(A_175)
      | ~ v2_funct_1(A_175)
      | ~ v1_funct_1(A_175)
      | ~ v1_relat_1(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1474,plain,
    ( k4_relat_1('#skF_5') = k2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_1462])).

tff(c_1484,plain,(
    k4_relat_1('#skF_5') = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_116,c_1474])).

tff(c_30,plain,(
    ! [A_16] :
      ( v1_xboole_0(k4_relat_1(A_16))
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1514,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1484,c_30])).

tff(c_1521,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_771,c_1514])).

tff(c_42,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) = k1_xboole_0
      | k1_relat_1(A_23) != k1_xboole_0
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_657,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_653,c_42])).

tff(c_658,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_676,plain,(
    ! [A_134] :
      ( k1_relat_1(A_134) = k1_xboole_0
      | k2_relat_1(A_134) != k1_xboole_0
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_682,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_653,c_676])).

tff(c_701,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_682])).

tff(c_1930,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_701])).

tff(c_114,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_1728,plain,(
    ! [A_203,B_204,C_205] :
      ( k1_relset_1(A_203,B_204,C_205) = k1_relat_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1737,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_1728])).

tff(c_2769,plain,(
    ! [B_260,A_261,C_262] :
      ( k1_xboole_0 = B_260
      | k1_relset_1(A_261,B_260,C_262) = A_261
      | ~ v1_funct_2(C_262,A_261,B_260)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_261,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_2788,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_2769])).

tff(c_2802,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_1737,c_2788])).

tff(c_2803,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1930,c_2802])).

tff(c_32,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(k1_relat_1(A_17))
      | ~ v1_relat_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2848,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2803,c_32])).

tff(c_2866,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_2848])).

tff(c_2867,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1521,c_2866])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [A_49] :
      ( m1_subset_1(A_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_49),k2_relat_1(A_49))))
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1934,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1928,c_94])).

tff(c_1959,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_116,c_1934])).

tff(c_76,plain,(
    ! [C_39,A_37,B_38] :
      ( v4_relat_1(C_39,A_37)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2033,plain,(
    v4_relat_1('#skF_5',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1959,c_76])).

tff(c_38,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2041,plain,
    ( k7_relat_1('#skF_5',k1_relat_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2033,c_38])).

tff(c_2044,plain,(
    k7_relat_1('#skF_5',k1_relat_1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_2041])).

tff(c_36,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2048,plain,
    ( k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2044,c_36])).

tff(c_2052,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_1928,c_2048])).

tff(c_2595,plain,(
    ! [A_255,B_256] :
      ( k9_relat_1(k2_funct_1(A_255),k9_relat_1(A_255,B_256)) = B_256
      | ~ r1_tarski(B_256,k1_relat_1(A_255))
      | ~ v2_funct_1(A_255)
      | ~ v1_funct_1(A_255)
      | ~ v1_relat_1(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2616,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_4') = k1_relat_1('#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2052,c_2595])).

tff(c_2639,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_4') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_116,c_110,c_18,c_2616])).

tff(c_2804,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2803,c_2639])).

tff(c_824,plain,(
    ! [B_152,A_153] :
      ( k2_relat_1(k7_relat_1(B_152,A_153)) = k9_relat_1(B_152,A_153)
      | ~ v1_relat_1(B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_15] :
      ( v1_xboole_0(k2_relat_1(A_15))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2929,plain,(
    ! [B_266,A_267] :
      ( v1_xboole_0(k9_relat_1(B_266,A_267))
      | ~ v1_xboole_0(k7_relat_1(B_266,A_267))
      | ~ v1_relat_1(B_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_824,c_26])).

tff(c_2972,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k7_relat_1(k2_funct_1('#skF_5'),'#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2804,c_2929])).

tff(c_3011,plain,
    ( ~ v1_xboole_0(k7_relat_1(k2_funct_1('#skF_5'),'#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_2867,c_2972])).

tff(c_3104,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3011])).

tff(c_3107,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_3104])).

tff(c_3111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_116,c_3107])).

tff(c_3113,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3011])).

tff(c_279,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_1638,plain,(
    ! [A_187] :
      ( k1_relat_1(k2_funct_1(A_187)) = k2_relat_1(A_187)
      | ~ v2_funct_1(A_187)
      | ~ v1_funct_1(A_187)
      | ~ v1_relat_1(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_34,plain,(
    ! [A_18] :
      ( k9_relat_1(A_18,k1_relat_1(A_18)) = k2_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34365,plain,(
    ! [A_653] :
      ( k9_relat_1(k2_funct_1(A_653),k2_relat_1(A_653)) = k2_relat_1(k2_funct_1(A_653))
      | ~ v1_relat_1(k2_funct_1(A_653))
      | ~ v2_funct_1(A_653)
      | ~ v1_funct_1(A_653)
      | ~ v1_relat_1(A_653) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1638,c_34])).

tff(c_34488,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),'#skF_4') = k2_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1928,c_34365])).

tff(c_34529,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_116,c_110,c_3113,c_2804,c_34488])).

tff(c_1819,plain,(
    ! [A_212] :
      ( m1_subset_1(A_212,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_212),k2_relat_1(A_212))))
      | ~ v1_funct_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1866,plain,(
    ! [A_212] :
      ( r1_tarski(A_212,k2_zfmisc_1(k1_relat_1(A_212),k2_relat_1(A_212)))
      | ~ v1_funct_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(resolution,[status(thm)],[c_1819,c_20])).

tff(c_34696,plain,
    ( r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34529,c_1866])).

tff(c_34768,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3113,c_279,c_34696])).

tff(c_34904,plain,
    ( r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_34768])).

tff(c_34927,plain,(
    r1_tarski(k2_funct_1('#skF_5'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_116,c_110,c_1928,c_34904])).

tff(c_34929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_633,c_34927])).

tff(c_34931,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_34951,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_34931,c_32])).

tff(c_34955,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_12,c_34951])).

tff(c_35020,plain,(
    ! [A_665,B_666] :
      ( r2_hidden('#skF_2'(A_665,B_666),A_665)
      | r1_tarski(A_665,B_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35030,plain,(
    ! [A_665,B_666] :
      ( ~ v1_xboole_0(A_665)
      | r1_tarski(A_665,B_666) ) ),
    inference(resolution,[status(thm)],[c_35020,c_2])).

tff(c_35031,plain,(
    ! [A_667,B_668] :
      ( ~ v1_xboole_0(A_667)
      | r1_tarski(A_667,B_668) ) ),
    inference(resolution,[status(thm)],[c_35020,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35048,plain,(
    ! [B_669,A_670] :
      ( B_669 = A_670
      | ~ r1_tarski(B_669,A_670)
      | ~ v1_xboole_0(A_670) ) ),
    inference(resolution,[status(thm)],[c_35031,c_14])).

tff(c_35062,plain,(
    ! [B_671,A_672] :
      ( B_671 = A_672
      | ~ v1_xboole_0(B_671)
      | ~ v1_xboole_0(A_672) ) ),
    inference(resolution,[status(thm)],[c_35030,c_35048])).

tff(c_35078,plain,(
    ! [A_673] :
      ( k1_xboole_0 = A_673
      | ~ v1_xboole_0(A_673) ) ),
    inference(resolution,[status(thm)],[c_12,c_35062])).

tff(c_35094,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34955,c_35078])).

tff(c_35097,plain,(
    ! [A_16] :
      ( k4_relat_1(A_16) = k1_xboole_0
      | ~ v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_30,c_35078])).

tff(c_35214,plain,(
    ! [A_678] :
      ( k4_relat_1(A_678) = '#skF_5'
      | ~ v1_xboole_0(A_678) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35094,c_35097])).

tff(c_35227,plain,(
    k4_relat_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34955,c_35214])).

tff(c_35880,plain,(
    ! [A_709] :
      ( k4_relat_1(A_709) = k2_funct_1(A_709)
      | ~ v2_funct_1(A_709)
      | ~ v1_funct_1(A_709)
      | ~ v1_relat_1(A_709) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_35889,plain,
    ( k4_relat_1('#skF_5') = k2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_35880])).

tff(c_35896,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_116,c_35227,c_35889])).

tff(c_35047,plain,(
    ~ v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_35031,c_633])).

tff(c_35897,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35896,c_35047])).

tff(c_35903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34955,c_35897])).

tff(c_35904,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_35905,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_37603,plain,(
    ! [A_835,B_836,C_837] :
      ( k1_relset_1(A_835,B_836,C_837) = k1_relat_1(C_837)
      | ~ m1_subset_1(C_837,k1_zfmisc_1(k2_zfmisc_1(A_835,B_836))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_37614,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_35905,c_37603])).

tff(c_38466,plain,(
    ! [B_876,C_877,A_878] :
      ( k1_xboole_0 = B_876
      | v1_funct_2(C_877,A_878,B_876)
      | k1_relset_1(A_878,B_876,C_877) != A_878
      | ~ m1_subset_1(C_877,k1_zfmisc_1(k2_zfmisc_1(A_878,B_876))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_38484,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_35905,c_38466])).

tff(c_38506,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37614,c_38484])).

tff(c_38507,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_35904,c_38506])).

tff(c_38512,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38507])).

tff(c_38515,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_38512])).

tff(c_38518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36228,c_116,c_110,c_37560,c_38515])).

tff(c_38519,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38507])).

tff(c_36232,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36228,c_42])).

tff(c_36233,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36232])).

tff(c_38562,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38519,c_36233])).

tff(c_36294,plain,(
    ! [A_752] :
      ( k1_relat_1(A_752) = k1_xboole_0
      | k2_relat_1(A_752) != k1_xboole_0
      | ~ v1_relat_1(A_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36303,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36228,c_36294])).

tff(c_36325,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36233,c_36303])).

tff(c_37562,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37560,c_36325])).

tff(c_38537,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38519,c_37562])).

tff(c_37616,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_37603])).

tff(c_92,plain,(
    ! [B_47,A_46,C_48] :
      ( k1_xboole_0 = B_47
      | k1_relset_1(A_46,B_47,C_48) = A_46
      | ~ v1_funct_2(C_48,A_46,B_47)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_38809,plain,(
    ! [B_881,A_882,C_883] :
      ( B_881 = '#skF_3'
      | k1_relset_1(A_882,B_881,C_883) = A_882
      | ~ v1_funct_2(C_883,A_882,B_881)
      | ~ m1_subset_1(C_883,k1_zfmisc_1(k2_zfmisc_1(A_882,B_881))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38519,c_92])).

tff(c_38828,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_38809])).

tff(c_38839,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_37616,c_38828])).

tff(c_38841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38562,c_38537,c_38839])).

tff(c_38843,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36232])).

tff(c_38867,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38843,c_32])).

tff(c_38871,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36228,c_12,c_38867])).

tff(c_39932,plain,(
    ! [A_941,B_942] :
      ( r2_hidden('#skF_2'(A_941,B_942),A_941)
      | r1_tarski(A_941,B_942) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_39936,plain,(
    ! [A_941,B_942] :
      ( ~ v1_xboole_0(A_941)
      | r1_tarski(A_941,B_942) ) ),
    inference(resolution,[status(thm)],[c_39932,c_2])).

tff(c_39937,plain,(
    ! [A_943,B_944] :
      ( ~ v1_xboole_0(A_943)
      | r1_tarski(A_943,B_944) ) ),
    inference(resolution,[status(thm)],[c_39932,c_2])).

tff(c_39946,plain,(
    ! [B_945,A_946] :
      ( B_945 = A_946
      | ~ r1_tarski(B_945,A_946)
      | ~ v1_xboole_0(A_946) ) ),
    inference(resolution,[status(thm)],[c_39937,c_14])).

tff(c_39964,plain,(
    ! [B_947,A_948] :
      ( B_947 = A_948
      | ~ v1_xboole_0(B_947)
      | ~ v1_xboole_0(A_948) ) ),
    inference(resolution,[status(thm)],[c_39936,c_39946])).

tff(c_39984,plain,(
    ! [A_949] :
      ( A_949 = '#skF_5'
      | ~ v1_xboole_0(A_949) ) ),
    inference(resolution,[status(thm)],[c_38871,c_39964])).

tff(c_40009,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12,c_39984])).

tff(c_38842,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36232])).

tff(c_40013,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40009,c_38842])).

tff(c_42792,plain,(
    ! [A_1108,B_1109,C_1110] :
      ( k2_relset_1(A_1108,B_1109,C_1110) = k2_relat_1(C_1110)
      | ~ m1_subset_1(C_1110,k1_zfmisc_1(k2_zfmisc_1(A_1108,B_1109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_42808,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_112,c_42792])).

tff(c_42816,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40013,c_108,c_42808])).

tff(c_36226,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_35905,c_36215])).

tff(c_38907,plain,(
    ! [A_892,B_893] :
      ( r2_hidden('#skF_2'(A_892,B_893),A_892)
      | r1_tarski(A_892,B_893) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38917,plain,(
    ! [A_892,B_893] :
      ( ~ v1_xboole_0(A_892)
      | r1_tarski(A_892,B_893) ) ),
    inference(resolution,[status(thm)],[c_38907,c_2])).

tff(c_39005,plain,(
    ! [B_899,A_900] :
      ( B_899 = A_900
      | ~ r1_tarski(B_899,A_900)
      | ~ r1_tarski(A_900,B_899) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_39028,plain,(
    ! [B_904,A_905] :
      ( B_904 = A_905
      | ~ r1_tarski(B_904,A_905)
      | ~ v1_xboole_0(A_905) ) ),
    inference(resolution,[status(thm)],[c_38917,c_39005])).

tff(c_39046,plain,(
    ! [B_906,A_907] :
      ( B_906 = A_907
      | ~ v1_xboole_0(B_906)
      | ~ v1_xboole_0(A_907) ) ),
    inference(resolution,[status(thm)],[c_38917,c_39028])).

tff(c_39062,plain,(
    ! [A_908] :
      ( A_908 = '#skF_5'
      | ~ v1_xboole_0(A_908) ) ),
    inference(resolution,[status(thm)],[c_38871,c_39046])).

tff(c_39083,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12,c_39062])).

tff(c_39089,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39083,c_38843])).

tff(c_39168,plain,(
    ! [A_911] :
      ( k4_relat_1(A_911) = '#skF_5'
      | ~ v1_xboole_0(A_911) ) ),
    inference(resolution,[status(thm)],[c_30,c_39062])).

tff(c_39181,plain,(
    k4_relat_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38871,c_39168])).

tff(c_39817,plain,(
    ! [A_932] :
      ( k4_relat_1(A_932) = k2_funct_1(A_932)
      | ~ v2_funct_1(A_932)
      | ~ v1_funct_1(A_932)
      | ~ v1_relat_1(A_932) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_39826,plain,
    ( k4_relat_1('#skF_5') = k2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_39817])).

tff(c_39833,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36228,c_116,c_39181,c_39826])).

tff(c_38847,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = k1_xboole_0
    | k1_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36226,c_42])).

tff(c_38873,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38847])).

tff(c_39088,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39083,c_38873])).

tff(c_39839,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39833,c_39088])).

tff(c_39849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39089,c_39839])).

tff(c_39851,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38847])).

tff(c_39881,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_39851,c_32])).

tff(c_39885,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36226,c_12,c_39881])).

tff(c_40003,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_39885,c_39984])).

tff(c_40031,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40003,c_35904])).

tff(c_42862,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42816,c_40031])).

tff(c_40012,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40009,c_38843])).

tff(c_40030,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40003,c_35905])).

tff(c_42380,plain,(
    ! [A_1088,B_1089,C_1090] :
      ( k1_relset_1(A_1088,B_1089,C_1090) = k1_relat_1(C_1090)
      | ~ m1_subset_1(C_1090,k1_zfmisc_1(k2_zfmisc_1(A_1088,B_1089))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_42383,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40030,c_42380])).

tff(c_42392,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40012,c_42383])).

tff(c_42823,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42816,c_42816,c_42392])).

tff(c_42859,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42816,c_40030])).

tff(c_42866,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42816,c_40009])).

tff(c_86,plain,(
    ! [C_48,B_47] :
      ( v1_funct_2(C_48,k1_xboole_0,B_47)
      | k1_relset_1(k1_xboole_0,B_47,C_48) != k1_xboole_0
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_43287,plain,(
    ! [C_48,B_47] :
      ( v1_funct_2(C_48,'#skF_4',B_47)
      | k1_relset_1('#skF_4',B_47,C_48) != '#skF_4'
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_47))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42866,c_42866,c_42866,c_42866,c_86])).

tff(c_43672,plain,
    ( v1_funct_2('#skF_4','#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_42859,c_43287])).

tff(c_43697,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42823,c_43672])).

tff(c_43699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42862,c_43697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:06:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.27/7.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.27/7.27  
% 15.27/7.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.27/7.27  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 15.27/7.27  
% 15.27/7.27  %Foreground sorts:
% 15.27/7.27  
% 15.27/7.27  
% 15.27/7.27  %Background operators:
% 15.27/7.27  
% 15.27/7.27  
% 15.27/7.27  %Foreground operators:
% 15.27/7.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 15.27/7.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.27/7.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 15.27/7.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 15.27/7.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.27/7.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.27/7.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.27/7.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 15.27/7.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.27/7.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.27/7.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.27/7.27  tff('#skF_5', type, '#skF_5': $i).
% 15.27/7.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.27/7.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 15.27/7.27  tff('#skF_3', type, '#skF_3': $i).
% 15.27/7.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.27/7.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 15.27/7.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.27/7.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.27/7.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.27/7.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.27/7.27  tff('#skF_4', type, '#skF_4': $i).
% 15.27/7.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 15.27/7.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.27/7.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.27/7.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.27/7.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.27/7.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.27/7.27  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 15.27/7.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.27/7.27  
% 15.50/7.31  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 15.50/7.31  tff(f_227, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 15.50/7.31  tff(f_156, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.50/7.31  tff(f_170, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 15.50/7.31  tff(f_152, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 15.50/7.31  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 15.50/7.31  tff(f_127, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 15.50/7.31  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.50/7.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 15.50/7.31  tff(f_119, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 15.50/7.31  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_relat_1)).
% 15.50/7.31  tff(f_91, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 15.50/7.31  tff(f_166, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.50/7.31  tff(f_188, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 15.50/7.31  tff(f_71, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 15.50/7.31  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.50/7.31  tff(f_198, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 15.50/7.31  tff(f_162, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 15.50/7.31  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 15.50/7.31  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 15.50/7.31  tff(f_142, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 15.50/7.31  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 15.50/7.31  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 15.50/7.31  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.50/7.31  tff(c_112, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_227])).
% 15.50/7.31  tff(c_36215, plain, (![C_739, A_740, B_741]: (v1_relat_1(C_739) | ~m1_subset_1(C_739, k1_zfmisc_1(k2_zfmisc_1(A_740, B_741))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 15.50/7.31  tff(c_36228, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_36215])).
% 15.50/7.31  tff(c_116, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_227])).
% 15.50/7.31  tff(c_110, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_227])).
% 15.50/7.31  tff(c_108, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_227])).
% 15.50/7.31  tff(c_37546, plain, (![A_831, B_832, C_833]: (k2_relset_1(A_831, B_832, C_833)=k2_relat_1(C_833) | ~m1_subset_1(C_833, k1_zfmisc_1(k2_zfmisc_1(A_831, B_832))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 15.50/7.31  tff(c_37556, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_37546])).
% 15.50/7.31  tff(c_37560, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_37556])).
% 15.50/7.31  tff(c_70, plain, (![A_33]: (k1_relat_1(k2_funct_1(A_33))=k2_relat_1(A_33) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.50/7.31  tff(c_644, plain, (![C_126, A_127, B_128]: (v1_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 15.50/7.31  tff(c_653, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_644])).
% 15.50/7.31  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.50/7.31  tff(c_58, plain, (![A_28]: (v1_funct_1(k2_funct_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_127])).
% 15.50/7.31  tff(c_106, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 15.50/7.31  tff(c_201, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_106])).
% 15.50/7.31  tff(c_204, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_201])).
% 15.50/7.31  tff(c_207, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_204])).
% 15.50/7.31  tff(c_265, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 15.50/7.31  tff(c_272, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_265])).
% 15.50/7.31  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_272])).
% 15.50/7.31  tff(c_278, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_106])).
% 15.50/7.31  tff(c_335, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_278])).
% 15.50/7.31  tff(c_633, plain, (~r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_335])).
% 15.50/7.31  tff(c_1909, plain, (![A_213, B_214, C_215]: (k2_relset_1(A_213, B_214, C_215)=k2_relat_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 15.50/7.31  tff(c_1922, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_1909])).
% 15.50/7.31  tff(c_1928, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1922])).
% 15.50/7.31  tff(c_60, plain, (![A_28]: (v1_relat_1(k2_funct_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_127])).
% 15.50/7.31  tff(c_712, plain, (![A_138, B_139]: (r2_hidden('#skF_2'(A_138, B_139), A_138) | r1_tarski(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.50/7.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.50/7.31  tff(c_755, plain, (![A_142, B_143]: (~v1_xboole_0(A_142) | r1_tarski(A_142, B_143))), inference(resolution, [status(thm)], [c_712, c_2])).
% 15.50/7.31  tff(c_771, plain, (~v1_xboole_0(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_755, c_633])).
% 15.50/7.31  tff(c_1462, plain, (![A_175]: (k4_relat_1(A_175)=k2_funct_1(A_175) | ~v2_funct_1(A_175) | ~v1_funct_1(A_175) | ~v1_relat_1(A_175))), inference(cnfTransformation, [status(thm)], [f_119])).
% 15.50/7.31  tff(c_1474, plain, (k4_relat_1('#skF_5')=k2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_110, c_1462])).
% 15.50/7.31  tff(c_1484, plain, (k4_relat_1('#skF_5')=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_653, c_116, c_1474])).
% 15.50/7.31  tff(c_30, plain, (![A_16]: (v1_xboole_0(k4_relat_1(A_16)) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.50/7.31  tff(c_1514, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1484, c_30])).
% 15.50/7.31  tff(c_1521, plain, (~v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_771, c_1514])).
% 15.50/7.31  tff(c_42, plain, (![A_23]: (k2_relat_1(A_23)=k1_xboole_0 | k1_relat_1(A_23)!=k1_xboole_0 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.50/7.31  tff(c_657, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_653, c_42])).
% 15.50/7.31  tff(c_658, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_657])).
% 15.50/7.31  tff(c_676, plain, (![A_134]: (k1_relat_1(A_134)=k1_xboole_0 | k2_relat_1(A_134)!=k1_xboole_0 | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.50/7.31  tff(c_682, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_653, c_676])).
% 15.50/7.31  tff(c_701, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_658, c_682])).
% 15.50/7.31  tff(c_1930, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1928, c_701])).
% 15.50/7.31  tff(c_114, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 15.50/7.31  tff(c_1728, plain, (![A_203, B_204, C_205]: (k1_relset_1(A_203, B_204, C_205)=k1_relat_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 15.50/7.31  tff(c_1737, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_1728])).
% 15.50/7.31  tff(c_2769, plain, (![B_260, A_261, C_262]: (k1_xboole_0=B_260 | k1_relset_1(A_261, B_260, C_262)=A_261 | ~v1_funct_2(C_262, A_261, B_260) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_261, B_260))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 15.50/7.31  tff(c_2788, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_112, c_2769])).
% 15.50/7.31  tff(c_2802, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_1737, c_2788])).
% 15.50/7.31  tff(c_2803, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1930, c_2802])).
% 15.50/7.31  tff(c_32, plain, (![A_17]: (~v1_xboole_0(k1_relat_1(A_17)) | ~v1_relat_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.50/7.31  tff(c_2848, plain, (~v1_xboole_0('#skF_3') | ~v1_relat_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2803, c_32])).
% 15.50/7.31  tff(c_2866, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_653, c_2848])).
% 15.50/7.31  tff(c_2867, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1521, c_2866])).
% 15.50/7.31  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.50/7.31  tff(c_94, plain, (![A_49]: (m1_subset_1(A_49, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_49), k2_relat_1(A_49)))) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_198])).
% 15.50/7.31  tff(c_1934, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1928, c_94])).
% 15.50/7.31  tff(c_1959, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_653, c_116, c_1934])).
% 15.50/7.31  tff(c_76, plain, (![C_39, A_37, B_38]: (v4_relat_1(C_39, A_37) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 15.50/7.31  tff(c_2033, plain, (v4_relat_1('#skF_5', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1959, c_76])).
% 15.50/7.31  tff(c_38, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.50/7.31  tff(c_2041, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_5'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2033, c_38])).
% 15.50/7.31  tff(c_2044, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_653, c_2041])).
% 15.50/7.31  tff(c_36, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.50/7.31  tff(c_2048, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2044, c_36])).
% 15.50/7.31  tff(c_2052, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_653, c_1928, c_2048])).
% 15.50/7.31  tff(c_2595, plain, (![A_255, B_256]: (k9_relat_1(k2_funct_1(A_255), k9_relat_1(A_255, B_256))=B_256 | ~r1_tarski(B_256, k1_relat_1(A_255)) | ~v2_funct_1(A_255) | ~v1_funct_1(A_255) | ~v1_relat_1(A_255))), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.50/7.31  tff(c_2616, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_4')=k1_relat_1('#skF_5') | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2052, c_2595])).
% 15.50/7.31  tff(c_2639, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_4')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_653, c_116, c_110, c_18, c_2616])).
% 15.50/7.31  tff(c_2804, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2803, c_2639])).
% 15.50/7.31  tff(c_824, plain, (![B_152, A_153]: (k2_relat_1(k7_relat_1(B_152, A_153))=k9_relat_1(B_152, A_153) | ~v1_relat_1(B_152))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.50/7.31  tff(c_26, plain, (![A_15]: (v1_xboole_0(k2_relat_1(A_15)) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.50/7.31  tff(c_2929, plain, (![B_266, A_267]: (v1_xboole_0(k9_relat_1(B_266, A_267)) | ~v1_xboole_0(k7_relat_1(B_266, A_267)) | ~v1_relat_1(B_266))), inference(superposition, [status(thm), theory('equality')], [c_824, c_26])).
% 15.50/7.31  tff(c_2972, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k7_relat_1(k2_funct_1('#skF_5'), '#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2804, c_2929])).
% 15.50/7.31  tff(c_3011, plain, (~v1_xboole_0(k7_relat_1(k2_funct_1('#skF_5'), '#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2867, c_2972])).
% 15.50/7.31  tff(c_3104, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_3011])).
% 15.50/7.31  tff(c_3107, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_3104])).
% 15.50/7.31  tff(c_3111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_653, c_116, c_3107])).
% 15.50/7.31  tff(c_3113, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_3011])).
% 15.50/7.31  tff(c_279, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_106])).
% 15.50/7.31  tff(c_1638, plain, (![A_187]: (k1_relat_1(k2_funct_1(A_187))=k2_relat_1(A_187) | ~v2_funct_1(A_187) | ~v1_funct_1(A_187) | ~v1_relat_1(A_187))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.50/7.31  tff(c_34, plain, (![A_18]: (k9_relat_1(A_18, k1_relat_1(A_18))=k2_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.50/7.31  tff(c_34365, plain, (![A_653]: (k9_relat_1(k2_funct_1(A_653), k2_relat_1(A_653))=k2_relat_1(k2_funct_1(A_653)) | ~v1_relat_1(k2_funct_1(A_653)) | ~v2_funct_1(A_653) | ~v1_funct_1(A_653) | ~v1_relat_1(A_653))), inference(superposition, [status(thm), theory('equality')], [c_1638, c_34])).
% 15.50/7.31  tff(c_34488, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_4')=k2_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1928, c_34365])).
% 15.50/7.31  tff(c_34529, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_653, c_116, c_110, c_3113, c_2804, c_34488])).
% 15.50/7.31  tff(c_1819, plain, (![A_212]: (m1_subset_1(A_212, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_212), k2_relat_1(A_212)))) | ~v1_funct_1(A_212) | ~v1_relat_1(A_212))), inference(cnfTransformation, [status(thm)], [f_198])).
% 15.50/7.31  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.50/7.31  tff(c_1866, plain, (![A_212]: (r1_tarski(A_212, k2_zfmisc_1(k1_relat_1(A_212), k2_relat_1(A_212))) | ~v1_funct_1(A_212) | ~v1_relat_1(A_212))), inference(resolution, [status(thm)], [c_1819, c_20])).
% 15.50/7.31  tff(c_34696, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34529, c_1866])).
% 15.50/7.31  tff(c_34768, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3113, c_279, c_34696])).
% 15.50/7.31  tff(c_34904, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_70, c_34768])).
% 15.50/7.31  tff(c_34927, plain, (r1_tarski(k2_funct_1('#skF_5'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_653, c_116, c_110, c_1928, c_34904])).
% 15.50/7.31  tff(c_34929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_633, c_34927])).
% 15.50/7.31  tff(c_34931, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_657])).
% 15.50/7.31  tff(c_34951, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_34931, c_32])).
% 15.50/7.31  tff(c_34955, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_653, c_12, c_34951])).
% 15.50/7.31  tff(c_35020, plain, (![A_665, B_666]: (r2_hidden('#skF_2'(A_665, B_666), A_665) | r1_tarski(A_665, B_666))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.50/7.31  tff(c_35030, plain, (![A_665, B_666]: (~v1_xboole_0(A_665) | r1_tarski(A_665, B_666))), inference(resolution, [status(thm)], [c_35020, c_2])).
% 15.50/7.31  tff(c_35031, plain, (![A_667, B_668]: (~v1_xboole_0(A_667) | r1_tarski(A_667, B_668))), inference(resolution, [status(thm)], [c_35020, c_2])).
% 15.50/7.31  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.50/7.31  tff(c_35048, plain, (![B_669, A_670]: (B_669=A_670 | ~r1_tarski(B_669, A_670) | ~v1_xboole_0(A_670))), inference(resolution, [status(thm)], [c_35031, c_14])).
% 15.50/7.31  tff(c_35062, plain, (![B_671, A_672]: (B_671=A_672 | ~v1_xboole_0(B_671) | ~v1_xboole_0(A_672))), inference(resolution, [status(thm)], [c_35030, c_35048])).
% 15.50/7.31  tff(c_35078, plain, (![A_673]: (k1_xboole_0=A_673 | ~v1_xboole_0(A_673))), inference(resolution, [status(thm)], [c_12, c_35062])).
% 15.50/7.31  tff(c_35094, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_34955, c_35078])).
% 15.50/7.31  tff(c_35097, plain, (![A_16]: (k4_relat_1(A_16)=k1_xboole_0 | ~v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_30, c_35078])).
% 15.50/7.31  tff(c_35214, plain, (![A_678]: (k4_relat_1(A_678)='#skF_5' | ~v1_xboole_0(A_678))), inference(demodulation, [status(thm), theory('equality')], [c_35094, c_35097])).
% 15.50/7.31  tff(c_35227, plain, (k4_relat_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_34955, c_35214])).
% 15.50/7.31  tff(c_35880, plain, (![A_709]: (k4_relat_1(A_709)=k2_funct_1(A_709) | ~v2_funct_1(A_709) | ~v1_funct_1(A_709) | ~v1_relat_1(A_709))), inference(cnfTransformation, [status(thm)], [f_119])).
% 15.50/7.31  tff(c_35889, plain, (k4_relat_1('#skF_5')=k2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_110, c_35880])).
% 15.50/7.31  tff(c_35896, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_653, c_116, c_35227, c_35889])).
% 15.50/7.31  tff(c_35047, plain, (~v1_xboole_0(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_35031, c_633])).
% 15.50/7.31  tff(c_35897, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_35896, c_35047])).
% 15.50/7.31  tff(c_35903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34955, c_35897])).
% 15.50/7.31  tff(c_35904, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_278])).
% 15.50/7.31  tff(c_35905, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_278])).
% 15.50/7.31  tff(c_37603, plain, (![A_835, B_836, C_837]: (k1_relset_1(A_835, B_836, C_837)=k1_relat_1(C_837) | ~m1_subset_1(C_837, k1_zfmisc_1(k2_zfmisc_1(A_835, B_836))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 15.50/7.31  tff(c_37614, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_35905, c_37603])).
% 15.50/7.31  tff(c_38466, plain, (![B_876, C_877, A_878]: (k1_xboole_0=B_876 | v1_funct_2(C_877, A_878, B_876) | k1_relset_1(A_878, B_876, C_877)!=A_878 | ~m1_subset_1(C_877, k1_zfmisc_1(k2_zfmisc_1(A_878, B_876))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 15.50/7.31  tff(c_38484, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_35905, c_38466])).
% 15.50/7.31  tff(c_38506, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_37614, c_38484])).
% 15.50/7.31  tff(c_38507, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_35904, c_38506])).
% 15.50/7.31  tff(c_38512, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_38507])).
% 15.50/7.31  tff(c_38515, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_70, c_38512])).
% 15.50/7.31  tff(c_38518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36228, c_116, c_110, c_37560, c_38515])).
% 15.50/7.31  tff(c_38519, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_38507])).
% 15.50/7.31  tff(c_36232, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_36228, c_42])).
% 15.50/7.31  tff(c_36233, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36232])).
% 15.50/7.31  tff(c_38562, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38519, c_36233])).
% 15.50/7.31  tff(c_36294, plain, (![A_752]: (k1_relat_1(A_752)=k1_xboole_0 | k2_relat_1(A_752)!=k1_xboole_0 | ~v1_relat_1(A_752))), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.50/7.31  tff(c_36303, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_36228, c_36294])).
% 15.50/7.31  tff(c_36325, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36233, c_36303])).
% 15.50/7.31  tff(c_37562, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_37560, c_36325])).
% 15.50/7.31  tff(c_38537, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38519, c_37562])).
% 15.50/7.31  tff(c_37616, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_37603])).
% 15.50/7.31  tff(c_92, plain, (![B_47, A_46, C_48]: (k1_xboole_0=B_47 | k1_relset_1(A_46, B_47, C_48)=A_46 | ~v1_funct_2(C_48, A_46, B_47) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 15.50/7.31  tff(c_38809, plain, (![B_881, A_882, C_883]: (B_881='#skF_3' | k1_relset_1(A_882, B_881, C_883)=A_882 | ~v1_funct_2(C_883, A_882, B_881) | ~m1_subset_1(C_883, k1_zfmisc_1(k2_zfmisc_1(A_882, B_881))))), inference(demodulation, [status(thm), theory('equality')], [c_38519, c_92])).
% 15.50/7.31  tff(c_38828, plain, ('#skF_3'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_112, c_38809])).
% 15.50/7.31  tff(c_38839, plain, ('#skF_3'='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_37616, c_38828])).
% 15.50/7.31  tff(c_38841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38562, c_38537, c_38839])).
% 15.50/7.31  tff(c_38843, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36232])).
% 15.50/7.31  tff(c_38867, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38843, c_32])).
% 15.50/7.31  tff(c_38871, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36228, c_12, c_38867])).
% 15.50/7.31  tff(c_39932, plain, (![A_941, B_942]: (r2_hidden('#skF_2'(A_941, B_942), A_941) | r1_tarski(A_941, B_942))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.50/7.31  tff(c_39936, plain, (![A_941, B_942]: (~v1_xboole_0(A_941) | r1_tarski(A_941, B_942))), inference(resolution, [status(thm)], [c_39932, c_2])).
% 15.50/7.31  tff(c_39937, plain, (![A_943, B_944]: (~v1_xboole_0(A_943) | r1_tarski(A_943, B_944))), inference(resolution, [status(thm)], [c_39932, c_2])).
% 15.50/7.31  tff(c_39946, plain, (![B_945, A_946]: (B_945=A_946 | ~r1_tarski(B_945, A_946) | ~v1_xboole_0(A_946))), inference(resolution, [status(thm)], [c_39937, c_14])).
% 15.50/7.31  tff(c_39964, plain, (![B_947, A_948]: (B_947=A_948 | ~v1_xboole_0(B_947) | ~v1_xboole_0(A_948))), inference(resolution, [status(thm)], [c_39936, c_39946])).
% 15.50/7.31  tff(c_39984, plain, (![A_949]: (A_949='#skF_5' | ~v1_xboole_0(A_949))), inference(resolution, [status(thm)], [c_38871, c_39964])).
% 15.50/7.31  tff(c_40009, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_12, c_39984])).
% 15.50/7.31  tff(c_38842, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36232])).
% 15.50/7.31  tff(c_40013, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40009, c_38842])).
% 15.50/7.31  tff(c_42792, plain, (![A_1108, B_1109, C_1110]: (k2_relset_1(A_1108, B_1109, C_1110)=k2_relat_1(C_1110) | ~m1_subset_1(C_1110, k1_zfmisc_1(k2_zfmisc_1(A_1108, B_1109))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 15.50/7.31  tff(c_42808, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_112, c_42792])).
% 15.50/7.31  tff(c_42816, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40013, c_108, c_42808])).
% 15.50/7.31  tff(c_36226, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_35905, c_36215])).
% 15.50/7.31  tff(c_38907, plain, (![A_892, B_893]: (r2_hidden('#skF_2'(A_892, B_893), A_892) | r1_tarski(A_892, B_893))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.50/7.31  tff(c_38917, plain, (![A_892, B_893]: (~v1_xboole_0(A_892) | r1_tarski(A_892, B_893))), inference(resolution, [status(thm)], [c_38907, c_2])).
% 15.50/7.31  tff(c_39005, plain, (![B_899, A_900]: (B_899=A_900 | ~r1_tarski(B_899, A_900) | ~r1_tarski(A_900, B_899))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.50/7.31  tff(c_39028, plain, (![B_904, A_905]: (B_904=A_905 | ~r1_tarski(B_904, A_905) | ~v1_xboole_0(A_905))), inference(resolution, [status(thm)], [c_38917, c_39005])).
% 15.50/7.31  tff(c_39046, plain, (![B_906, A_907]: (B_906=A_907 | ~v1_xboole_0(B_906) | ~v1_xboole_0(A_907))), inference(resolution, [status(thm)], [c_38917, c_39028])).
% 15.50/7.31  tff(c_39062, plain, (![A_908]: (A_908='#skF_5' | ~v1_xboole_0(A_908))), inference(resolution, [status(thm)], [c_38871, c_39046])).
% 15.50/7.31  tff(c_39083, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_12, c_39062])).
% 15.50/7.31  tff(c_39089, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_39083, c_38843])).
% 15.50/7.31  tff(c_39168, plain, (![A_911]: (k4_relat_1(A_911)='#skF_5' | ~v1_xboole_0(A_911))), inference(resolution, [status(thm)], [c_30, c_39062])).
% 15.50/7.31  tff(c_39181, plain, (k4_relat_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_38871, c_39168])).
% 15.50/7.31  tff(c_39817, plain, (![A_932]: (k4_relat_1(A_932)=k2_funct_1(A_932) | ~v2_funct_1(A_932) | ~v1_funct_1(A_932) | ~v1_relat_1(A_932))), inference(cnfTransformation, [status(thm)], [f_119])).
% 15.50/7.31  tff(c_39826, plain, (k4_relat_1('#skF_5')=k2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_110, c_39817])).
% 15.50/7.31  tff(c_39833, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36228, c_116, c_39181, c_39826])).
% 15.50/7.31  tff(c_38847, plain, (k2_relat_1(k2_funct_1('#skF_5'))=k1_xboole_0 | k1_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_36226, c_42])).
% 15.50/7.31  tff(c_38873, plain, (k1_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38847])).
% 15.50/7.31  tff(c_39088, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_39083, c_38873])).
% 15.50/7.31  tff(c_39839, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_39833, c_39088])).
% 15.50/7.31  tff(c_39849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39089, c_39839])).
% 15.50/7.31  tff(c_39851, plain, (k1_relat_1(k2_funct_1('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_38847])).
% 15.50/7.31  tff(c_39881, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k2_funct_1('#skF_5')) | v1_xboole_0(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_39851, c_32])).
% 15.50/7.31  tff(c_39885, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36226, c_12, c_39881])).
% 15.50/7.31  tff(c_40003, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_39885, c_39984])).
% 15.50/7.31  tff(c_40031, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40003, c_35904])).
% 15.50/7.31  tff(c_42862, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42816, c_40031])).
% 15.50/7.31  tff(c_40012, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40009, c_38843])).
% 15.50/7.31  tff(c_40030, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40003, c_35905])).
% 15.50/7.31  tff(c_42380, plain, (![A_1088, B_1089, C_1090]: (k1_relset_1(A_1088, B_1089, C_1090)=k1_relat_1(C_1090) | ~m1_subset_1(C_1090, k1_zfmisc_1(k2_zfmisc_1(A_1088, B_1089))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 15.50/7.31  tff(c_42383, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40030, c_42380])).
% 15.50/7.31  tff(c_42392, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40012, c_42383])).
% 15.50/7.31  tff(c_42823, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42816, c_42816, c_42392])).
% 15.50/7.31  tff(c_42859, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42816, c_40030])).
% 15.50/7.31  tff(c_42866, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42816, c_40009])).
% 15.50/7.31  tff(c_86, plain, (![C_48, B_47]: (v1_funct_2(C_48, k1_xboole_0, B_47) | k1_relset_1(k1_xboole_0, B_47, C_48)!=k1_xboole_0 | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_47))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 15.50/7.31  tff(c_43287, plain, (![C_48, B_47]: (v1_funct_2(C_48, '#skF_4', B_47) | k1_relset_1('#skF_4', B_47, C_48)!='#skF_4' | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_47))))), inference(demodulation, [status(thm), theory('equality')], [c_42866, c_42866, c_42866, c_42866, c_86])).
% 15.50/7.31  tff(c_43672, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_42859, c_43287])).
% 15.50/7.31  tff(c_43697, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42823, c_43672])).
% 15.50/7.31  tff(c_43699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42862, c_43697])).
% 15.50/7.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.50/7.31  
% 15.50/7.31  Inference rules
% 15.50/7.31  ----------------------
% 15.50/7.31  #Ref     : 0
% 15.50/7.31  #Sup     : 12360
% 15.50/7.31  #Fact    : 0
% 15.50/7.31  #Define  : 0
% 15.50/7.31  #Split   : 48
% 15.50/7.31  #Chain   : 0
% 15.50/7.31  #Close   : 0
% 15.50/7.31  
% 15.50/7.31  Ordering : KBO
% 15.50/7.31  
% 15.50/7.31  Simplification rules
% 15.50/7.31  ----------------------
% 15.50/7.31  #Subsume      : 4447
% 15.50/7.31  #Demod        : 5648
% 15.50/7.31  #Tautology    : 2345
% 15.50/7.31  #SimpNegUnit  : 149
% 15.50/7.31  #BackRed      : 207
% 15.50/7.31  
% 15.50/7.31  #Partial instantiations: 0
% 15.50/7.31  #Strategies tried      : 1
% 15.50/7.31  
% 15.50/7.31  Timing (in seconds)
% 15.50/7.31  ----------------------
% 15.50/7.31  Preprocessing        : 0.38
% 15.50/7.31  Parsing              : 0.20
% 15.50/7.31  CNF conversion       : 0.03
% 15.50/7.31  Main loop            : 6.12
% 15.50/7.31  Inferencing          : 1.15
% 15.50/7.31  Reduction            : 1.82
% 15.50/7.31  Demodulation         : 1.33
% 15.50/7.31  BG Simplification    : 0.14
% 15.50/7.31  Subsumption          : 2.67
% 15.50/7.31  Abstraction          : 0.17
% 15.50/7.31  MUC search           : 0.00
% 15.50/7.31  Cooper               : 0.00
% 15.50/7.31  Total                : 6.58
% 15.50/7.31  Index Insertion      : 0.00
% 15.50/7.31  Index Deletion       : 0.00
% 15.50/7.31  Index Matching       : 0.00
% 15.50/7.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
