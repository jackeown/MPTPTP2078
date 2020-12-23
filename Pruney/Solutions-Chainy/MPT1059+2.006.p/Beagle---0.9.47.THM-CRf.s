%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:33 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 134 expanded)
%              Number of leaves         :   40 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  152 ( 331 expanded)
%              Number of equality atoms :   41 (  79 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_191,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_135,axiom,(
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

tff(f_146,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_159,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_76,plain,(
    m1_subset_1('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_162,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_175,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_162])).

tff(c_294,plain,(
    ! [C_109,B_110,A_111] :
      ( v5_relat_1(C_109,B_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_309,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_294])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_401,plain,(
    ! [C_125,A_126,B_127] :
      ( v5_relat_1(C_125,A_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(B_127))
      | ~ v5_relat_1(B_127,A_126)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1362,plain,(
    ! [A_211,A_212,B_213] :
      ( v5_relat_1(A_211,A_212)
      | ~ v5_relat_1(B_213,A_212)
      | ~ v1_relat_1(B_213)
      | ~ r1_tarski(A_211,B_213) ) ),
    inference(resolution,[status(thm)],[c_26,c_401])).

tff(c_1376,plain,(
    ! [A_211] :
      ( v5_relat_1(A_211,'#skF_4')
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski(A_211,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_309,c_1362])).

tff(c_1397,plain,(
    ! [A_211] :
      ( v5_relat_1(A_211,'#skF_4')
      | ~ r1_tarski(A_211,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_1376])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_82,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_80,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_526,plain,(
    ! [A_148,B_149,C_150] :
      ( k1_relset_1(A_148,B_149,C_150) = k1_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_541,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_526])).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_100])).

tff(c_62,plain,(
    ! [B_39,A_38,C_40] :
      ( k1_xboole_0 = B_39
      | k1_relset_1(A_38,B_39,C_40) = A_38
      | ~ v1_funct_2(C_40,A_38,B_39)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_964,plain,(
    ! [B_185,A_186,C_187] :
      ( B_185 = '#skF_2'
      | k1_relset_1(A_186,B_185,C_187) = A_186
      | ~ v1_funct_2(C_187,A_186,B_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_62])).

tff(c_974,plain,
    ( '#skF_2' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_964])).

tff(c_985,plain,
    ( '#skF_2' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_541,c_974])).

tff(c_987,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_985])).

tff(c_1178,plain,(
    ! [A_197,B_198,C_199] :
      ( k7_partfun1(A_197,B_198,C_199) = k1_funct_1(B_198,C_199)
      | ~ r2_hidden(C_199,k1_relat_1(B_198))
      | ~ v1_funct_1(B_198)
      | ~ v5_relat_1(B_198,A_197)
      | ~ v1_relat_1(B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1180,plain,(
    ! [A_197,C_199] :
      ( k7_partfun1(A_197,'#skF_5',C_199) = k1_funct_1('#skF_5',C_199)
      | ~ r2_hidden(C_199,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_197)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_987,c_1178])).

tff(c_1235,plain,(
    ! [A_202,C_203] :
      ( k7_partfun1(A_202,'#skF_5',C_203) = k1_funct_1('#skF_5',C_203)
      | ~ r2_hidden(C_203,'#skF_3')
      | ~ v5_relat_1('#skF_5',A_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_82,c_1180])).

tff(c_1238,plain,(
    ! [A_202,A_10] :
      ( k7_partfun1(A_202,'#skF_5',A_10) = k1_funct_1('#skF_5',A_10)
      | ~ v5_relat_1('#skF_5',A_202)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_10,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_1235])).

tff(c_1741,plain,(
    ! [A_239,A_240] :
      ( k7_partfun1(A_239,'#skF_5',A_240) = k1_funct_1('#skF_5',A_240)
      | ~ v5_relat_1('#skF_5',A_239)
      | ~ m1_subset_1(A_240,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1238])).

tff(c_1753,plain,(
    ! [A_240] :
      ( k7_partfun1('#skF_4','#skF_5',A_240) = k1_funct_1('#skF_5',A_240)
      | ~ m1_subset_1(A_240,'#skF_3')
      | ~ r1_tarski('#skF_5','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1397,c_1741])).

tff(c_1783,plain,(
    ! [A_241] :
      ( k7_partfun1('#skF_4','#skF_5',A_241) = k1_funct_1('#skF_5',A_241)
      | ~ m1_subset_1(A_241,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1753])).

tff(c_1787,plain,(
    k7_partfun1('#skF_4','#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_1783])).

tff(c_74,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_6') != k7_partfun1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1788,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_6') != k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_74])).

tff(c_1684,plain,(
    ! [A_230,B_231,C_232,D_233] :
      ( k3_funct_2(A_230,B_231,C_232,D_233) = k1_funct_1(C_232,D_233)
      | ~ m1_subset_1(D_233,A_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231)))
      | ~ v1_funct_2(C_232,A_230,B_231)
      | ~ v1_funct_1(C_232)
      | v1_xboole_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1696,plain,(
    ! [B_231,C_232] :
      ( k3_funct_2('#skF_3',B_231,C_232,'#skF_6') = k1_funct_1(C_232,'#skF_6')
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_231)))
      | ~ v1_funct_2(C_232,'#skF_3',B_231)
      | ~ v1_funct_1(C_232)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_76,c_1684])).

tff(c_1916,plain,(
    ! [B_254,C_255] :
      ( k3_funct_2('#skF_3',B_254,C_255,'#skF_6') = k1_funct_1(C_255,'#skF_6')
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_254)))
      | ~ v1_funct_2(C_255,'#skF_3',B_254)
      | ~ v1_funct_1(C_255) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1696])).

tff(c_1926,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_1916])).

tff(c_1937,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_1926])).

tff(c_1939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1788,c_1937])).

tff(c_1940,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_985])).

tff(c_1978,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1940,c_8])).

tff(c_1980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1978])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:29:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.72  
% 4.13/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.73  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.13/1.73  
% 4.13/1.73  %Foreground sorts:
% 4.13/1.73  
% 4.13/1.73  
% 4.13/1.73  %Background operators:
% 4.13/1.73  
% 4.13/1.73  
% 4.13/1.73  %Foreground operators:
% 4.13/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.13/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.13/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.13/1.73  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.13/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.13/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.13/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.13/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.13/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.13/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.13/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.13/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.13/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.13/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.13/1.73  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.13/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.13/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.73  
% 4.13/1.75  tff(f_191, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 4.13/1.75  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.13/1.75  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.13/1.75  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.13/1.75  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.13/1.75  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_relat_1)).
% 4.13/1.75  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.13/1.75  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.13/1.75  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 4.13/1.75  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.13/1.75  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.13/1.75  tff(f_146, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 4.13/1.75  tff(f_159, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.13/1.75  tff(c_84, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.13/1.75  tff(c_76, plain, (m1_subset_1('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.13/1.75  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.13/1.75  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.13/1.75  tff(c_162, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.13/1.75  tff(c_175, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_162])).
% 4.13/1.75  tff(c_294, plain, (![C_109, B_110, A_111]: (v5_relat_1(C_109, B_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.13/1.75  tff(c_309, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_294])).
% 4.13/1.75  tff(c_26, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.13/1.75  tff(c_401, plain, (![C_125, A_126, B_127]: (v5_relat_1(C_125, A_126) | ~m1_subset_1(C_125, k1_zfmisc_1(B_127)) | ~v5_relat_1(B_127, A_126) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.13/1.75  tff(c_1362, plain, (![A_211, A_212, B_213]: (v5_relat_1(A_211, A_212) | ~v5_relat_1(B_213, A_212) | ~v1_relat_1(B_213) | ~r1_tarski(A_211, B_213))), inference(resolution, [status(thm)], [c_26, c_401])).
% 4.13/1.75  tff(c_1376, plain, (![A_211]: (v5_relat_1(A_211, '#skF_4') | ~v1_relat_1('#skF_5') | ~r1_tarski(A_211, '#skF_5'))), inference(resolution, [status(thm)], [c_309, c_1362])).
% 4.13/1.75  tff(c_1397, plain, (![A_211]: (v5_relat_1(A_211, '#skF_4') | ~r1_tarski(A_211, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_1376])).
% 4.13/1.75  tff(c_86, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.13/1.75  tff(c_22, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.13/1.75  tff(c_82, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.13/1.75  tff(c_80, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.13/1.75  tff(c_526, plain, (![A_148, B_149, C_150]: (k1_relset_1(A_148, B_149, C_150)=k1_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.13/1.75  tff(c_541, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_526])).
% 4.13/1.75  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.13/1.75  tff(c_100, plain, (![A_64]: (k1_xboole_0=A_64 | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.13/1.75  tff(c_104, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_100])).
% 4.13/1.75  tff(c_62, plain, (![B_39, A_38, C_40]: (k1_xboole_0=B_39 | k1_relset_1(A_38, B_39, C_40)=A_38 | ~v1_funct_2(C_40, A_38, B_39) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.13/1.75  tff(c_964, plain, (![B_185, A_186, C_187]: (B_185='#skF_2' | k1_relset_1(A_186, B_185, C_187)=A_186 | ~v1_funct_2(C_187, A_186, B_185) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_62])).
% 4.13/1.75  tff(c_974, plain, ('#skF_2'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_964])).
% 4.13/1.75  tff(c_985, plain, ('#skF_2'='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_541, c_974])).
% 4.13/1.75  tff(c_987, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_985])).
% 4.13/1.75  tff(c_1178, plain, (![A_197, B_198, C_199]: (k7_partfun1(A_197, B_198, C_199)=k1_funct_1(B_198, C_199) | ~r2_hidden(C_199, k1_relat_1(B_198)) | ~v1_funct_1(B_198) | ~v5_relat_1(B_198, A_197) | ~v1_relat_1(B_198))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.13/1.75  tff(c_1180, plain, (![A_197, C_199]: (k7_partfun1(A_197, '#skF_5', C_199)=k1_funct_1('#skF_5', C_199) | ~r2_hidden(C_199, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_197) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_987, c_1178])).
% 4.13/1.75  tff(c_1235, plain, (![A_202, C_203]: (k7_partfun1(A_202, '#skF_5', C_203)=k1_funct_1('#skF_5', C_203) | ~r2_hidden(C_203, '#skF_3') | ~v5_relat_1('#skF_5', A_202))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_82, c_1180])).
% 4.13/1.75  tff(c_1238, plain, (![A_202, A_10]: (k7_partfun1(A_202, '#skF_5', A_10)=k1_funct_1('#skF_5', A_10) | ~v5_relat_1('#skF_5', A_202) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_10, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1235])).
% 4.13/1.75  tff(c_1741, plain, (![A_239, A_240]: (k7_partfun1(A_239, '#skF_5', A_240)=k1_funct_1('#skF_5', A_240) | ~v5_relat_1('#skF_5', A_239) | ~m1_subset_1(A_240, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_86, c_1238])).
% 4.13/1.75  tff(c_1753, plain, (![A_240]: (k7_partfun1('#skF_4', '#skF_5', A_240)=k1_funct_1('#skF_5', A_240) | ~m1_subset_1(A_240, '#skF_3') | ~r1_tarski('#skF_5', '#skF_5'))), inference(resolution, [status(thm)], [c_1397, c_1741])).
% 4.13/1.75  tff(c_1783, plain, (![A_241]: (k7_partfun1('#skF_4', '#skF_5', A_241)=k1_funct_1('#skF_5', A_241) | ~m1_subset_1(A_241, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1753])).
% 4.13/1.75  tff(c_1787, plain, (k7_partfun1('#skF_4', '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_76, c_1783])).
% 4.13/1.75  tff(c_74, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k7_partfun1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.13/1.75  tff(c_1788, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_74])).
% 4.13/1.75  tff(c_1684, plain, (![A_230, B_231, C_232, D_233]: (k3_funct_2(A_230, B_231, C_232, D_233)=k1_funct_1(C_232, D_233) | ~m1_subset_1(D_233, A_230) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))) | ~v1_funct_2(C_232, A_230, B_231) | ~v1_funct_1(C_232) | v1_xboole_0(A_230))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.13/1.75  tff(c_1696, plain, (![B_231, C_232]: (k3_funct_2('#skF_3', B_231, C_232, '#skF_6')=k1_funct_1(C_232, '#skF_6') | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_231))) | ~v1_funct_2(C_232, '#skF_3', B_231) | ~v1_funct_1(C_232) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_76, c_1684])).
% 4.13/1.75  tff(c_1916, plain, (![B_254, C_255]: (k3_funct_2('#skF_3', B_254, C_255, '#skF_6')=k1_funct_1(C_255, '#skF_6') | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_254))) | ~v1_funct_2(C_255, '#skF_3', B_254) | ~v1_funct_1(C_255))), inference(negUnitSimplification, [status(thm)], [c_86, c_1696])).
% 4.13/1.75  tff(c_1926, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_1916])).
% 4.13/1.75  tff(c_1937, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_1926])).
% 4.13/1.75  tff(c_1939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1788, c_1937])).
% 4.13/1.75  tff(c_1940, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_985])).
% 4.13/1.75  tff(c_1978, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1940, c_8])).
% 4.13/1.75  tff(c_1980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1978])).
% 4.13/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.75  
% 4.13/1.75  Inference rules
% 4.13/1.75  ----------------------
% 4.13/1.75  #Ref     : 0
% 4.13/1.75  #Sup     : 382
% 4.13/1.75  #Fact    : 0
% 4.13/1.75  #Define  : 0
% 4.13/1.75  #Split   : 12
% 4.13/1.75  #Chain   : 0
% 4.13/1.75  #Close   : 0
% 4.13/1.75  
% 4.13/1.75  Ordering : KBO
% 4.13/1.75  
% 4.13/1.75  Simplification rules
% 4.13/1.75  ----------------------
% 4.13/1.75  #Subsume      : 109
% 4.13/1.75  #Demod        : 318
% 4.13/1.75  #Tautology    : 146
% 4.13/1.75  #SimpNegUnit  : 26
% 4.13/1.75  #BackRed      : 49
% 4.13/1.75  
% 4.13/1.75  #Partial instantiations: 0
% 4.13/1.75  #Strategies tried      : 1
% 4.13/1.75  
% 4.13/1.75  Timing (in seconds)
% 4.13/1.75  ----------------------
% 4.13/1.76  Preprocessing        : 0.37
% 4.13/1.76  Parsing              : 0.20
% 4.13/1.76  CNF conversion       : 0.03
% 4.13/1.76  Main loop            : 0.60
% 4.13/1.76  Inferencing          : 0.20
% 4.13/1.76  Reduction            : 0.21
% 4.13/1.76  Demodulation         : 0.15
% 4.13/1.76  BG Simplification    : 0.03
% 4.13/1.76  Subsumption          : 0.11
% 4.13/1.76  Abstraction          : 0.02
% 4.13/1.76  MUC search           : 0.00
% 4.13/1.76  Cooper               : 0.00
% 4.44/1.76  Total                : 1.02
% 4.44/1.76  Index Insertion      : 0.00
% 4.44/1.76  Index Deletion       : 0.00
% 4.44/1.76  Index Matching       : 0.00
% 4.44/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
