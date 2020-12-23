%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:15 EST 2020

% Result     : Theorem 10.79s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :  189 (1678 expanded)
%              Number of leaves         :   34 ( 556 expanded)
%              Depth                    :   13
%              Number of atoms          :  353 (5167 expanded)
%              Number of equality atoms :   79 (1626 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_126,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_143,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_126])).

tff(c_17456,plain,(
    ! [C_662,B_663,A_664] :
      ( v5_relat_1(C_662,B_663)
      | ~ m1_subset_1(C_662,k1_zfmisc_1(k2_zfmisc_1(A_664,B_663))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_17475,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_17456])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_17382,plain,(
    ! [A_647,C_648,B_649] :
      ( r1_tarski(A_647,C_648)
      | ~ r1_tarski(B_649,C_648)
      | ~ r1_tarski(A_647,B_649) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17395,plain,(
    ! [A_650] :
      ( r1_tarski(A_650,'#skF_3')
      | ~ r1_tarski(A_650,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_17382])).

tff(c_17404,plain,(
    ! [B_16] :
      ( r1_tarski(k2_relat_1(B_16),'#skF_3')
      | ~ v5_relat_1(B_16,'#skF_2')
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_26,c_17395])).

tff(c_17662,plain,(
    ! [C_685,A_686,B_687] :
      ( v4_relat_1(C_685,A_686)
      | ~ m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1(A_686,B_687))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_17681,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_17662])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18832,plain,(
    ! [C_796,A_797,B_798] :
      ( m1_subset_1(C_796,k1_zfmisc_1(k2_zfmisc_1(A_797,B_798)))
      | ~ r1_tarski(k2_relat_1(C_796),B_798)
      | ~ r1_tarski(k1_relat_1(C_796),A_797)
      | ~ v1_relat_1(C_796) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_780,plain,(
    ! [A_124,B_125,C_126] :
      ( k1_relset_1(A_124,B_125,C_126) = k1_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_799,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_780])).

tff(c_1585,plain,(
    ! [B_202,A_203,C_204] :
      ( k1_xboole_0 = B_202
      | k1_relset_1(A_203,B_202,C_204) = A_203
      | ~ v1_funct_2(C_204,A_203,B_202)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_203,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1595,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1585])).

tff(c_1610,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_799,c_1595])).

tff(c_1611,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1610])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_205,plain,(
    ! [C_60,A_61,B_62] :
      ( v4_relat_1(C_60,A_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_227,plain,(
    ! [C_64,A_65] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_205])).

tff(c_234,plain,(
    ! [A_8,A_65] :
      ( v4_relat_1(A_8,A_65)
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_227])).

tff(c_286,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k1_relat_1(B_72),A_73)
      | ~ v4_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_142,plain,(
    ! [A_8,A_45,B_46] :
      ( v1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_45,B_46)) ) ),
    inference(resolution,[status(thm)],[c_16,c_126])).

tff(c_1011,plain,(
    ! [B_151,A_152,B_153] :
      ( v1_relat_1(k1_relat_1(B_151))
      | ~ v4_relat_1(B_151,k2_zfmisc_1(A_152,B_153))
      | ~ v1_relat_1(B_151) ) ),
    inference(resolution,[status(thm)],[c_286,c_142])).

tff(c_1038,plain,(
    ! [A_8] :
      ( v1_relat_1(k1_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_234,c_1011])).

tff(c_1630,plain,
    ( v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_1038])).

tff(c_1666,plain,
    ( v1_relat_1('#skF_1')
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_1630])).

tff(c_1688,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1666])).

tff(c_238,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_257,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_238])).

tff(c_335,plain,(
    ! [A_79,C_80,B_81] :
      ( r1_tarski(A_79,C_80)
      | ~ r1_tarski(B_81,C_80)
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_365,plain,(
    ! [A_82] :
      ( r1_tarski(A_82,'#skF_3')
      | ~ r1_tarski(A_82,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_335])).

tff(c_527,plain,(
    ! [B_102] :
      ( r1_tarski(k2_relat_1(B_102),'#skF_3')
      | ~ v5_relat_1(B_102,'#skF_2')
      | ~ v1_relat_1(B_102) ) ),
    inference(resolution,[status(thm)],[c_26,c_365])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( v5_relat_1(B_16,A_15)
      | ~ r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_564,plain,(
    ! [B_105] :
      ( v5_relat_1(B_105,'#skF_3')
      | ~ v5_relat_1(B_105,'#skF_2')
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_527,c_24])).

tff(c_578,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_257,c_564])).

tff(c_586,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_578])).

tff(c_379,plain,(
    ! [B_16] :
      ( r1_tarski(k2_relat_1(B_16),'#skF_3')
      | ~ v5_relat_1(B_16,'#skF_2')
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_26,c_365])).

tff(c_36,plain,(
    ! [C_28,A_26,B_27] :
      ( m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ r1_tarski(k2_relat_1(C_28),B_27)
      | ~ r1_tarski(k1_relat_1(C_28),A_26)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1699,plain,(
    ! [B_205,C_206,A_207] :
      ( k1_xboole_0 = B_205
      | v1_funct_2(C_206,A_207,B_205)
      | k1_relset_1(A_207,B_205,C_206) != A_207
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_207,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4244,plain,(
    ! [B_295,C_296,A_297] :
      ( k1_xboole_0 = B_295
      | v1_funct_2(C_296,A_297,B_295)
      | k1_relset_1(A_297,B_295,C_296) != A_297
      | ~ r1_tarski(k2_relat_1(C_296),B_295)
      | ~ r1_tarski(k1_relat_1(C_296),A_297)
      | ~ v1_relat_1(C_296) ) ),
    inference(resolution,[status(thm)],[c_36,c_1699])).

tff(c_4280,plain,(
    ! [B_16,A_297] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(B_16,A_297,'#skF_3')
      | k1_relset_1(A_297,'#skF_3',B_16) != A_297
      | ~ r1_tarski(k1_relat_1(B_16),A_297)
      | ~ v5_relat_1(B_16,'#skF_2')
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_379,c_4244])).

tff(c_6564,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4280])).

tff(c_1316,plain,(
    ! [C_179,A_180,B_181] :
      ( m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ r1_tarski(k2_relat_1(C_179),B_181)
      | ~ r1_tarski(k1_relat_1(C_179),A_180)
      | ~ v1_relat_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1818,plain,(
    ! [C_210,A_211] :
      ( m1_subset_1(C_210,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_210),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_210),A_211)
      | ~ v1_relat_1(C_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1316])).

tff(c_4932,plain,(
    ! [B_316,A_317] :
      ( m1_subset_1(B_316,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(B_316),A_317)
      | ~ v5_relat_1(B_316,k1_xboole_0)
      | ~ v1_relat_1(B_316) ) ),
    inference(resolution,[status(thm)],[c_26,c_1818])).

tff(c_4966,plain,(
    ! [A_317] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',A_317)
      | ~ v5_relat_1('#skF_4',k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_4932])).

tff(c_4997,plain,(
    ! [A_317] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',A_317)
      | ~ v5_relat_1('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_4966])).

tff(c_5004,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4997])).

tff(c_6583,plain,(
    ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6564,c_5004])).

tff(c_6676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_6583])).

tff(c_6678,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4280])).

tff(c_224,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_205])).

tff(c_1651,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_1',A_13)
      | ~ v4_relat_1('#skF_4',A_13)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_22])).

tff(c_1777,plain,(
    ! [A_209] :
      ( r1_tarski('#skF_1',A_209)
      | ~ v4_relat_1('#skF_4',A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_1651])).

tff(c_1802,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_224,c_1777])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2256,plain,(
    ! [C_230,A_231,B_232] :
      ( r1_tarski(C_230,k2_zfmisc_1(A_231,B_232))
      | ~ r1_tarski(k2_relat_1(C_230),B_232)
      | ~ r1_tarski(k1_relat_1(C_230),A_231)
      | ~ v1_relat_1(C_230) ) ),
    inference(resolution,[status(thm)],[c_1316,c_14])).

tff(c_2437,plain,(
    ! [B_238,A_239] :
      ( r1_tarski(B_238,k2_zfmisc_1(A_239,'#skF_3'))
      | ~ r1_tarski(k1_relat_1(B_238),A_239)
      | ~ v5_relat_1(B_238,'#skF_2')
      | ~ v1_relat_1(B_238) ) ),
    inference(resolution,[status(thm)],[c_379,c_2256])).

tff(c_2446,plain,(
    ! [A_239] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_239,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_239)
      | ~ v5_relat_1('#skF_4','#skF_2')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_2437])).

tff(c_2474,plain,(
    ! [A_240] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_240,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_257,c_2446])).

tff(c_798,plain,(
    ! [A_124,B_125,A_8] :
      ( k1_relset_1(A_124,B_125,A_8) = k1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_124,B_125)) ) ),
    inference(resolution,[status(thm)],[c_16,c_780])).

tff(c_2477,plain,(
    ! [A_240] :
      ( k1_relset_1(A_240,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_240) ) ),
    inference(resolution,[status(thm)],[c_2474,c_798])).

tff(c_2506,plain,(
    ! [A_241] :
      ( k1_relset_1(A_241,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_2477])).

tff(c_2514,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1802,c_2506])).

tff(c_11593,plain,(
    ! [A_498,B_499,A_500] :
      ( k1_xboole_0 = A_498
      | v1_funct_2(B_499,A_500,A_498)
      | k1_relset_1(A_500,A_498,B_499) != A_500
      | ~ r1_tarski(k1_relat_1(B_499),A_500)
      | ~ v5_relat_1(B_499,A_498)
      | ~ v1_relat_1(B_499) ) ),
    inference(resolution,[status(thm)],[c_26,c_4244])).

tff(c_11651,plain,(
    ! [A_498,A_500] :
      ( k1_xboole_0 = A_498
      | v1_funct_2('#skF_4',A_500,A_498)
      | k1_relset_1(A_500,A_498,'#skF_4') != A_500
      | ~ r1_tarski('#skF_1',A_500)
      | ~ v5_relat_1('#skF_4',A_498)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_11593])).

tff(c_16426,plain,(
    ! [A_620,A_621] :
      ( k1_xboole_0 = A_620
      | v1_funct_2('#skF_4',A_621,A_620)
      | k1_relset_1(A_621,A_620,'#skF_4') != A_621
      | ~ r1_tarski('#skF_1',A_621)
      | ~ v5_relat_1('#skF_4',A_620) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_11651])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50])).

tff(c_145,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_16445,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_16426,c_145])).

tff(c_16458,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_1802,c_2514,c_16445])).

tff(c_16460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6678,c_16458])).

tff(c_16461,plain,(
    ! [A_317] :
      ( ~ r1_tarski('#skF_1',A_317)
      | m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_4997])).

tff(c_16721,plain,(
    ! [A_317] : ~ r1_tarski('#skF_1',A_317) ),
    inference(splitLeft,[status(thm)],[c_16461])).

tff(c_16724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16721,c_1802])).

tff(c_16725,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_16461])).

tff(c_16743,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16725,c_14])).

tff(c_16758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1688,c_16743])).

tff(c_16760,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1666])).

tff(c_4,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16830,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16760,c_4])).

tff(c_322,plain,(
    ! [B_78] :
      ( k1_relat_1(B_78) = k1_xboole_0
      | ~ v4_relat_1(B_78,k1_xboole_0)
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_286,c_4])).

tff(c_331,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) = k1_xboole_0
      | ~ v1_relat_1(A_8)
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_234,c_322])).

tff(c_16799,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16760,c_331])).

tff(c_16822,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_1611,c_16799])).

tff(c_16891,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16830,c_16822])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_144,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_126])).

tff(c_225,plain,(
    ! [A_61] : v4_relat_1(k1_xboole_0,A_61) ),
    inference(resolution,[status(thm)],[c_12,c_205])).

tff(c_330,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_225,c_322])).

tff(c_334,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_330])).

tff(c_797,plain,(
    ! [A_124,B_125] : k1_relset_1(A_124,B_125,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_780])).

tff(c_801,plain,(
    ! [A_124,B_125] : k1_relset_1(A_124,B_125,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_797])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_927,plain,(
    ! [C_139,B_140] :
      ( v1_funct_2(C_139,k1_xboole_0,B_140)
      | k1_relset_1(k1_xboole_0,B_140,C_139) != k1_xboole_0
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_933,plain,(
    ! [B_140] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_140)
      | k1_relset_1(k1_xboole_0,B_140,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_927])).

tff(c_937,plain,(
    ! [B_140] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_801,c_933])).

tff(c_16847,plain,(
    ! [B_140] : v1_funct_2('#skF_1','#skF_1',B_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16822,c_16822,c_937])).

tff(c_17320,plain,(
    ! [B_140] : v1_funct_2('#skF_4','#skF_4',B_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16891,c_16891,c_16847])).

tff(c_16908,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16891,c_145])).

tff(c_17324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17320,c_16908])).

tff(c_17325,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_18846,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18832,c_17325])).

tff(c_18865,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_18846])).

tff(c_18868,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18865])).

tff(c_18874,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_18868])).

tff(c_18881,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_17681,c_18874])).

tff(c_18882,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_18865])).

tff(c_18901,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_17404,c_18882])).

tff(c_18911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_17475,c_18901])).

tff(c_18912,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_18925,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18912,c_18912,c_10])).

tff(c_18913,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_18918,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18912,c_18913])).

tff(c_18953,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18925,c_18918,c_56])).

tff(c_18957,plain,(
    ! [A_806,B_807] :
      ( r1_tarski(A_806,B_807)
      | ~ m1_subset_1(A_806,k1_zfmisc_1(B_807)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18968,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_18953,c_18957])).

tff(c_18951,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18912,c_18912,c_4])).

tff(c_18973,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18968,c_18951])).

tff(c_18933,plain,(
    ! [A_7] : m1_subset_1('#skF_1',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18912,c_12])).

tff(c_18979,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18973,c_18933])).

tff(c_19024,plain,(
    ! [A_813] : m1_subset_1('#skF_4',k1_zfmisc_1(A_813)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18973,c_18933])).

tff(c_28,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_19032,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_19024,c_28])).

tff(c_19281,plain,(
    ! [C_853,A_854,B_855] :
      ( v4_relat_1(C_853,A_854)
      | ~ m1_subset_1(C_853,k1_zfmisc_1(k2_zfmisc_1(A_854,B_855))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_19303,plain,(
    ! [A_858] : v4_relat_1('#skF_4',A_858) ),
    inference(resolution,[status(thm)],[c_18979,c_19281])).

tff(c_19132,plain,(
    ! [B_829,A_830] :
      ( r1_tarski(k1_relat_1(B_829),A_830)
      | ~ v4_relat_1(B_829,A_830)
      | ~ v1_relat_1(B_829) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18977,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18973,c_18973,c_18951])).

tff(c_19147,plain,(
    ! [B_829] :
      ( k1_relat_1(B_829) = '#skF_4'
      | ~ v4_relat_1(B_829,'#skF_4')
      | ~ v1_relat_1(B_829) ) ),
    inference(resolution,[status(thm)],[c_19132,c_18977])).

tff(c_19307,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_19303,c_19147])).

tff(c_19310,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19032,c_19307])).

tff(c_19427,plain,(
    ! [A_879,B_880,C_881] :
      ( k1_relset_1(A_879,B_880,C_881) = k1_relat_1(C_881)
      | ~ m1_subset_1(C_881,k1_zfmisc_1(k2_zfmisc_1(A_879,B_880))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_19434,plain,(
    ! [A_879,B_880] : k1_relset_1(A_879,B_880,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18979,c_19427])).

tff(c_19443,plain,(
    ! [A_879,B_880] : k1_relset_1(A_879,B_880,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19310,c_19434])).

tff(c_18984,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18973,c_18912])).

tff(c_66,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_19579,plain,(
    ! [C_892,B_893] :
      ( v1_funct_2(C_892,'#skF_4',B_893)
      | k1_relset_1('#skF_4',B_893,C_892) != '#skF_4'
      | ~ m1_subset_1(C_892,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18984,c_18984,c_18984,c_18984,c_66])).

tff(c_19582,plain,(
    ! [B_893] :
      ( v1_funct_2('#skF_4','#skF_4',B_893)
      | k1_relset_1('#skF_4',B_893,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_18979,c_19579])).

tff(c_19588,plain,(
    ! [B_893] : v1_funct_2('#skF_4','#skF_4',B_893) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19443,c_19582])).

tff(c_19005,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18973,c_18973,c_62])).

tff(c_19006,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_19005])).

tff(c_19593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19588,c_19006])).

tff(c_19594,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_19005])).

tff(c_19662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18979,c_19594])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:37:57 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.79/3.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.06/3.98  
% 11.06/3.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.06/3.98  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.06/3.98  
% 11.06/3.98  %Foreground sorts:
% 11.06/3.98  
% 11.06/3.98  
% 11.06/3.98  %Background operators:
% 11.06/3.98  
% 11.06/3.98  
% 11.06/3.98  %Foreground operators:
% 11.06/3.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.06/3.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.06/3.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.06/3.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.06/3.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.06/3.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.06/3.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.06/3.98  tff('#skF_2', type, '#skF_2': $i).
% 11.06/3.98  tff('#skF_3', type, '#skF_3': $i).
% 11.06/3.98  tff('#skF_1', type, '#skF_1': $i).
% 11.06/3.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.06/3.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.06/3.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.06/3.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.06/3.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.06/3.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.06/3.98  tff('#skF_4', type, '#skF_4': $i).
% 11.06/3.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.06/3.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.06/3.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.06/3.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.06/3.98  
% 11.21/4.01  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 11.21/4.01  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.21/4.01  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.21/4.01  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 11.21/4.01  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.21/4.01  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 11.21/4.01  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 11.21/4.01  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.21/4.01  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.21/4.01  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.21/4.01  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.21/4.01  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 11.21/4.01  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 11.21/4.01  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.21/4.01  tff(c_126, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.21/4.01  tff(c_143, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_126])).
% 11.21/4.01  tff(c_17456, plain, (![C_662, B_663, A_664]: (v5_relat_1(C_662, B_663) | ~m1_subset_1(C_662, k1_zfmisc_1(k2_zfmisc_1(A_664, B_663))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.21/4.01  tff(c_17475, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_17456])).
% 11.21/4.01  tff(c_26, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.01  tff(c_54, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.21/4.01  tff(c_17382, plain, (![A_647, C_648, B_649]: (r1_tarski(A_647, C_648) | ~r1_tarski(B_649, C_648) | ~r1_tarski(A_647, B_649))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.01  tff(c_17395, plain, (![A_650]: (r1_tarski(A_650, '#skF_3') | ~r1_tarski(A_650, '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_17382])).
% 11.21/4.01  tff(c_17404, plain, (![B_16]: (r1_tarski(k2_relat_1(B_16), '#skF_3') | ~v5_relat_1(B_16, '#skF_2') | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_26, c_17395])).
% 11.21/4.01  tff(c_17662, plain, (![C_685, A_686, B_687]: (v4_relat_1(C_685, A_686) | ~m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1(A_686, B_687))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.21/4.01  tff(c_17681, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_17662])).
% 11.21/4.01  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.21/4.01  tff(c_18832, plain, (![C_796, A_797, B_798]: (m1_subset_1(C_796, k1_zfmisc_1(k2_zfmisc_1(A_797, B_798))) | ~r1_tarski(k2_relat_1(C_796), B_798) | ~r1_tarski(k1_relat_1(C_796), A_797) | ~v1_relat_1(C_796))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.21/4.01  tff(c_52, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.21/4.01  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 11.21/4.01  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.21/4.01  tff(c_780, plain, (![A_124, B_125, C_126]: (k1_relset_1(A_124, B_125, C_126)=k1_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.21/4.01  tff(c_799, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_780])).
% 11.21/4.01  tff(c_1585, plain, (![B_202, A_203, C_204]: (k1_xboole_0=B_202 | k1_relset_1(A_203, B_202, C_204)=A_203 | ~v1_funct_2(C_204, A_203, B_202) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_203, B_202))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.21/4.01  tff(c_1595, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_1585])).
% 11.21/4.01  tff(c_1610, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_799, c_1595])).
% 11.21/4.01  tff(c_1611, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_1610])).
% 11.21/4.01  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.21/4.01  tff(c_8, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.21/4.01  tff(c_205, plain, (![C_60, A_61, B_62]: (v4_relat_1(C_60, A_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.21/4.01  tff(c_227, plain, (![C_64, A_65]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_205])).
% 11.21/4.01  tff(c_234, plain, (![A_8, A_65]: (v4_relat_1(A_8, A_65) | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_227])).
% 11.21/4.01  tff(c_286, plain, (![B_72, A_73]: (r1_tarski(k1_relat_1(B_72), A_73) | ~v4_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.21/4.01  tff(c_142, plain, (![A_8, A_45, B_46]: (v1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_45, B_46)))), inference(resolution, [status(thm)], [c_16, c_126])).
% 11.21/4.01  tff(c_1011, plain, (![B_151, A_152, B_153]: (v1_relat_1(k1_relat_1(B_151)) | ~v4_relat_1(B_151, k2_zfmisc_1(A_152, B_153)) | ~v1_relat_1(B_151))), inference(resolution, [status(thm)], [c_286, c_142])).
% 11.21/4.01  tff(c_1038, plain, (![A_8]: (v1_relat_1(k1_relat_1(A_8)) | ~v1_relat_1(A_8) | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_234, c_1011])).
% 11.21/4.01  tff(c_1630, plain, (v1_relat_1('#skF_1') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1611, c_1038])).
% 11.21/4.01  tff(c_1666, plain, (v1_relat_1('#skF_1') | ~r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_1630])).
% 11.21/4.01  tff(c_1688, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1666])).
% 11.21/4.01  tff(c_238, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.21/4.01  tff(c_257, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_238])).
% 11.21/4.01  tff(c_335, plain, (![A_79, C_80, B_81]: (r1_tarski(A_79, C_80) | ~r1_tarski(B_81, C_80) | ~r1_tarski(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.01  tff(c_365, plain, (![A_82]: (r1_tarski(A_82, '#skF_3') | ~r1_tarski(A_82, '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_335])).
% 11.21/4.01  tff(c_527, plain, (![B_102]: (r1_tarski(k2_relat_1(B_102), '#skF_3') | ~v5_relat_1(B_102, '#skF_2') | ~v1_relat_1(B_102))), inference(resolution, [status(thm)], [c_26, c_365])).
% 11.21/4.01  tff(c_24, plain, (![B_16, A_15]: (v5_relat_1(B_16, A_15) | ~r1_tarski(k2_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.01  tff(c_564, plain, (![B_105]: (v5_relat_1(B_105, '#skF_3') | ~v5_relat_1(B_105, '#skF_2') | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_527, c_24])).
% 11.21/4.01  tff(c_578, plain, (v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_257, c_564])).
% 11.21/4.01  tff(c_586, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_578])).
% 11.21/4.01  tff(c_379, plain, (![B_16]: (r1_tarski(k2_relat_1(B_16), '#skF_3') | ~v5_relat_1(B_16, '#skF_2') | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_26, c_365])).
% 11.21/4.01  tff(c_36, plain, (![C_28, A_26, B_27]: (m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~r1_tarski(k2_relat_1(C_28), B_27) | ~r1_tarski(k1_relat_1(C_28), A_26) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.21/4.01  tff(c_1699, plain, (![B_205, C_206, A_207]: (k1_xboole_0=B_205 | v1_funct_2(C_206, A_207, B_205) | k1_relset_1(A_207, B_205, C_206)!=A_207 | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_207, B_205))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.21/4.01  tff(c_4244, plain, (![B_295, C_296, A_297]: (k1_xboole_0=B_295 | v1_funct_2(C_296, A_297, B_295) | k1_relset_1(A_297, B_295, C_296)!=A_297 | ~r1_tarski(k2_relat_1(C_296), B_295) | ~r1_tarski(k1_relat_1(C_296), A_297) | ~v1_relat_1(C_296))), inference(resolution, [status(thm)], [c_36, c_1699])).
% 11.21/4.01  tff(c_4280, plain, (![B_16, A_297]: (k1_xboole_0='#skF_3' | v1_funct_2(B_16, A_297, '#skF_3') | k1_relset_1(A_297, '#skF_3', B_16)!=A_297 | ~r1_tarski(k1_relat_1(B_16), A_297) | ~v5_relat_1(B_16, '#skF_2') | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_379, c_4244])).
% 11.21/4.01  tff(c_6564, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4280])).
% 11.21/4.01  tff(c_1316, plain, (![C_179, A_180, B_181]: (m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~r1_tarski(k2_relat_1(C_179), B_181) | ~r1_tarski(k1_relat_1(C_179), A_180) | ~v1_relat_1(C_179))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.21/4.01  tff(c_1818, plain, (![C_210, A_211]: (m1_subset_1(C_210, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_210), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_210), A_211) | ~v1_relat_1(C_210))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1316])).
% 11.21/4.01  tff(c_4932, plain, (![B_316, A_317]: (m1_subset_1(B_316, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(B_316), A_317) | ~v5_relat_1(B_316, k1_xboole_0) | ~v1_relat_1(B_316))), inference(resolution, [status(thm)], [c_26, c_1818])).
% 11.21/4.01  tff(c_4966, plain, (![A_317]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', A_317) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1611, c_4932])).
% 11.21/4.01  tff(c_4997, plain, (![A_317]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', A_317) | ~v5_relat_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_4966])).
% 11.21/4.01  tff(c_5004, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4997])).
% 11.21/4.01  tff(c_6583, plain, (~v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6564, c_5004])).
% 11.21/4.01  tff(c_6676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_586, c_6583])).
% 11.21/4.01  tff(c_6678, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4280])).
% 11.21/4.01  tff(c_224, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_205])).
% 11.21/4.01  tff(c_1651, plain, (![A_13]: (r1_tarski('#skF_1', A_13) | ~v4_relat_1('#skF_4', A_13) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1611, c_22])).
% 11.21/4.01  tff(c_1777, plain, (![A_209]: (r1_tarski('#skF_1', A_209) | ~v4_relat_1('#skF_4', A_209))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_1651])).
% 11.21/4.01  tff(c_1802, plain, (r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_224, c_1777])).
% 11.21/4.01  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.21/4.01  tff(c_2256, plain, (![C_230, A_231, B_232]: (r1_tarski(C_230, k2_zfmisc_1(A_231, B_232)) | ~r1_tarski(k2_relat_1(C_230), B_232) | ~r1_tarski(k1_relat_1(C_230), A_231) | ~v1_relat_1(C_230))), inference(resolution, [status(thm)], [c_1316, c_14])).
% 11.21/4.01  tff(c_2437, plain, (![B_238, A_239]: (r1_tarski(B_238, k2_zfmisc_1(A_239, '#skF_3')) | ~r1_tarski(k1_relat_1(B_238), A_239) | ~v5_relat_1(B_238, '#skF_2') | ~v1_relat_1(B_238))), inference(resolution, [status(thm)], [c_379, c_2256])).
% 11.21/4.01  tff(c_2446, plain, (![A_239]: (r1_tarski('#skF_4', k2_zfmisc_1(A_239, '#skF_3')) | ~r1_tarski('#skF_1', A_239) | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1611, c_2437])).
% 11.21/4.01  tff(c_2474, plain, (![A_240]: (r1_tarski('#skF_4', k2_zfmisc_1(A_240, '#skF_3')) | ~r1_tarski('#skF_1', A_240))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_257, c_2446])).
% 11.21/4.01  tff(c_798, plain, (![A_124, B_125, A_8]: (k1_relset_1(A_124, B_125, A_8)=k1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_124, B_125)))), inference(resolution, [status(thm)], [c_16, c_780])).
% 11.21/4.01  tff(c_2477, plain, (![A_240]: (k1_relset_1(A_240, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_240))), inference(resolution, [status(thm)], [c_2474, c_798])).
% 11.21/4.01  tff(c_2506, plain, (![A_241]: (k1_relset_1(A_241, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_241))), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_2477])).
% 11.21/4.01  tff(c_2514, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_1802, c_2506])).
% 11.21/4.01  tff(c_11593, plain, (![A_498, B_499, A_500]: (k1_xboole_0=A_498 | v1_funct_2(B_499, A_500, A_498) | k1_relset_1(A_500, A_498, B_499)!=A_500 | ~r1_tarski(k1_relat_1(B_499), A_500) | ~v5_relat_1(B_499, A_498) | ~v1_relat_1(B_499))), inference(resolution, [status(thm)], [c_26, c_4244])).
% 11.21/4.01  tff(c_11651, plain, (![A_498, A_500]: (k1_xboole_0=A_498 | v1_funct_2('#skF_4', A_500, A_498) | k1_relset_1(A_500, A_498, '#skF_4')!=A_500 | ~r1_tarski('#skF_1', A_500) | ~v5_relat_1('#skF_4', A_498) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1611, c_11593])).
% 11.21/4.01  tff(c_16426, plain, (![A_620, A_621]: (k1_xboole_0=A_620 | v1_funct_2('#skF_4', A_621, A_620) | k1_relset_1(A_621, A_620, '#skF_4')!=A_621 | ~r1_tarski('#skF_1', A_621) | ~v5_relat_1('#skF_4', A_620))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_11651])).
% 11.21/4.01  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.21/4.01  tff(c_50, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.21/4.01  tff(c_62, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50])).
% 11.21/4.01  tff(c_145, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 11.21/4.01  tff(c_16445, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1') | ~v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_16426, c_145])).
% 11.21/4.01  tff(c_16458, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_586, c_1802, c_2514, c_16445])).
% 11.21/4.01  tff(c_16460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6678, c_16458])).
% 11.21/4.01  tff(c_16461, plain, (![A_317]: (~r1_tarski('#skF_1', A_317) | m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_4997])).
% 11.21/4.01  tff(c_16721, plain, (![A_317]: (~r1_tarski('#skF_1', A_317))), inference(splitLeft, [status(thm)], [c_16461])).
% 11.21/4.01  tff(c_16724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16721, c_1802])).
% 11.21/4.01  tff(c_16725, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_16461])).
% 11.21/4.01  tff(c_16743, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_16725, c_14])).
% 11.21/4.01  tff(c_16758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1688, c_16743])).
% 11.21/4.01  tff(c_16760, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1666])).
% 11.21/4.01  tff(c_4, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.21/4.01  tff(c_16830, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_16760, c_4])).
% 11.21/4.01  tff(c_322, plain, (![B_78]: (k1_relat_1(B_78)=k1_xboole_0 | ~v4_relat_1(B_78, k1_xboole_0) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_286, c_4])).
% 11.21/4.01  tff(c_331, plain, (![A_8]: (k1_relat_1(A_8)=k1_xboole_0 | ~v1_relat_1(A_8) | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_234, c_322])).
% 11.21/4.01  tff(c_16799, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16760, c_331])).
% 11.21/4.01  tff(c_16822, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_1611, c_16799])).
% 11.21/4.01  tff(c_16891, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16830, c_16822])).
% 11.21/4.01  tff(c_12, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.21/4.01  tff(c_144, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_126])).
% 11.21/4.01  tff(c_225, plain, (![A_61]: (v4_relat_1(k1_xboole_0, A_61))), inference(resolution, [status(thm)], [c_12, c_205])).
% 11.21/4.01  tff(c_330, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_225, c_322])).
% 11.21/4.01  tff(c_334, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_144, c_330])).
% 11.21/4.01  tff(c_797, plain, (![A_124, B_125]: (k1_relset_1(A_124, B_125, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_780])).
% 11.21/4.01  tff(c_801, plain, (![A_124, B_125]: (k1_relset_1(A_124, B_125, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_334, c_797])).
% 11.21/4.01  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.21/4.01  tff(c_42, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.21/4.01  tff(c_927, plain, (![C_139, B_140]: (v1_funct_2(C_139, k1_xboole_0, B_140) | k1_relset_1(k1_xboole_0, B_140, C_139)!=k1_xboole_0 | ~m1_subset_1(C_139, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_42])).
% 11.21/4.01  tff(c_933, plain, (![B_140]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_140) | k1_relset_1(k1_xboole_0, B_140, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_927])).
% 11.21/4.01  tff(c_937, plain, (![B_140]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_140))), inference(demodulation, [status(thm), theory('equality')], [c_801, c_933])).
% 11.21/4.01  tff(c_16847, plain, (![B_140]: (v1_funct_2('#skF_1', '#skF_1', B_140))), inference(demodulation, [status(thm), theory('equality')], [c_16822, c_16822, c_937])).
% 11.21/4.01  tff(c_17320, plain, (![B_140]: (v1_funct_2('#skF_4', '#skF_4', B_140))), inference(demodulation, [status(thm), theory('equality')], [c_16891, c_16891, c_16847])).
% 11.21/4.01  tff(c_16908, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16891, c_145])).
% 11.21/4.01  tff(c_17324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17320, c_16908])).
% 11.21/4.01  tff(c_17325, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_62])).
% 11.21/4.01  tff(c_18846, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18832, c_17325])).
% 11.21/4.01  tff(c_18865, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_18846])).
% 11.21/4.01  tff(c_18868, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_18865])).
% 11.21/4.01  tff(c_18874, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_18868])).
% 11.21/4.01  tff(c_18881, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_17681, c_18874])).
% 11.21/4.01  tff(c_18882, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_18865])).
% 11.21/4.01  tff(c_18901, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_17404, c_18882])).
% 11.21/4.01  tff(c_18911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_17475, c_18901])).
% 11.21/4.01  tff(c_18912, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_52])).
% 11.21/4.01  tff(c_18925, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18912, c_18912, c_10])).
% 11.21/4.01  tff(c_18913, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 11.21/4.01  tff(c_18918, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18912, c_18913])).
% 11.21/4.01  tff(c_18953, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18925, c_18918, c_56])).
% 11.21/4.01  tff(c_18957, plain, (![A_806, B_807]: (r1_tarski(A_806, B_807) | ~m1_subset_1(A_806, k1_zfmisc_1(B_807)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.21/4.01  tff(c_18968, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_18953, c_18957])).
% 11.21/4.01  tff(c_18951, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18912, c_18912, c_4])).
% 11.21/4.01  tff(c_18973, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_18968, c_18951])).
% 11.21/4.01  tff(c_18933, plain, (![A_7]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_18912, c_12])).
% 11.21/4.01  tff(c_18979, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_18973, c_18933])).
% 11.21/4.01  tff(c_19024, plain, (![A_813]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_813)))), inference(demodulation, [status(thm), theory('equality')], [c_18973, c_18933])).
% 11.21/4.01  tff(c_28, plain, (![C_19, A_17, B_18]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.21/4.01  tff(c_19032, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_19024, c_28])).
% 11.21/4.01  tff(c_19281, plain, (![C_853, A_854, B_855]: (v4_relat_1(C_853, A_854) | ~m1_subset_1(C_853, k1_zfmisc_1(k2_zfmisc_1(A_854, B_855))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.21/4.01  tff(c_19303, plain, (![A_858]: (v4_relat_1('#skF_4', A_858))), inference(resolution, [status(thm)], [c_18979, c_19281])).
% 11.21/4.01  tff(c_19132, plain, (![B_829, A_830]: (r1_tarski(k1_relat_1(B_829), A_830) | ~v4_relat_1(B_829, A_830) | ~v1_relat_1(B_829))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.21/4.01  tff(c_18977, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18973, c_18973, c_18951])).
% 11.21/4.01  tff(c_19147, plain, (![B_829]: (k1_relat_1(B_829)='#skF_4' | ~v4_relat_1(B_829, '#skF_4') | ~v1_relat_1(B_829))), inference(resolution, [status(thm)], [c_19132, c_18977])).
% 11.21/4.01  tff(c_19307, plain, (k1_relat_1('#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_19303, c_19147])).
% 11.21/4.01  tff(c_19310, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19032, c_19307])).
% 11.21/4.01  tff(c_19427, plain, (![A_879, B_880, C_881]: (k1_relset_1(A_879, B_880, C_881)=k1_relat_1(C_881) | ~m1_subset_1(C_881, k1_zfmisc_1(k2_zfmisc_1(A_879, B_880))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.21/4.01  tff(c_19434, plain, (![A_879, B_880]: (k1_relset_1(A_879, B_880, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18979, c_19427])).
% 11.21/4.01  tff(c_19443, plain, (![A_879, B_880]: (k1_relset_1(A_879, B_880, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19310, c_19434])).
% 11.21/4.01  tff(c_18984, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18973, c_18912])).
% 11.21/4.01  tff(c_66, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_42])).
% 11.21/4.01  tff(c_19579, plain, (![C_892, B_893]: (v1_funct_2(C_892, '#skF_4', B_893) | k1_relset_1('#skF_4', B_893, C_892)!='#skF_4' | ~m1_subset_1(C_892, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_18984, c_18984, c_18984, c_18984, c_66])).
% 11.21/4.01  tff(c_19582, plain, (![B_893]: (v1_funct_2('#skF_4', '#skF_4', B_893) | k1_relset_1('#skF_4', B_893, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_18979, c_19579])).
% 11.21/4.01  tff(c_19588, plain, (![B_893]: (v1_funct_2('#skF_4', '#skF_4', B_893))), inference(demodulation, [status(thm), theory('equality')], [c_19443, c_19582])).
% 11.21/4.01  tff(c_19005, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18973, c_18973, c_62])).
% 11.21/4.01  tff(c_19006, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_19005])).
% 11.21/4.01  tff(c_19593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19588, c_19006])).
% 11.21/4.01  tff(c_19594, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_19005])).
% 11.21/4.01  tff(c_19662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18979, c_19594])).
% 11.21/4.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/4.01  
% 11.21/4.01  Inference rules
% 11.21/4.01  ----------------------
% 11.21/4.01  #Ref     : 0
% 11.21/4.01  #Sup     : 4399
% 11.21/4.01  #Fact    : 0
% 11.21/4.01  #Define  : 0
% 11.21/4.01  #Split   : 23
% 11.21/4.01  #Chain   : 0
% 11.21/4.01  #Close   : 0
% 11.21/4.01  
% 11.21/4.01  Ordering : KBO
% 11.21/4.01  
% 11.21/4.01  Simplification rules
% 11.21/4.01  ----------------------
% 11.21/4.01  #Subsume      : 1483
% 11.21/4.01  #Demod        : 2888
% 11.21/4.01  #Tautology    : 1111
% 11.21/4.01  #SimpNegUnit  : 71
% 11.21/4.01  #BackRed      : 204
% 11.21/4.01  
% 11.21/4.01  #Partial instantiations: 0
% 11.21/4.01  #Strategies tried      : 1
% 11.21/4.01  
% 11.21/4.01  Timing (in seconds)
% 11.21/4.01  ----------------------
% 11.21/4.01  Preprocessing        : 0.33
% 11.21/4.01  Parsing              : 0.17
% 11.21/4.01  CNF conversion       : 0.02
% 11.21/4.02  Main loop            : 2.91
% 11.21/4.02  Inferencing          : 0.77
% 11.21/4.02  Reduction            : 0.84
% 11.21/4.02  Demodulation         : 0.55
% 11.21/4.02  BG Simplification    : 0.08
% 11.21/4.02  Subsumption          : 1.00
% 11.21/4.02  Abstraction          : 0.11
% 11.21/4.02  MUC search           : 0.00
% 11.21/4.02  Cooper               : 0.00
% 11.21/4.02  Total                : 3.30
% 11.21/4.02  Index Insertion      : 0.00
% 11.21/4.02  Index Deletion       : 0.00
% 11.21/4.02  Index Matching       : 0.00
% 11.21/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
