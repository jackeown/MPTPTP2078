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
% DateTime   : Thu Dec  3 10:15:07 EST 2020

% Result     : Theorem 34.50s
% Output     : CNFRefutation 34.77s
% Verified   : 
% Statistics : Number of formulae       :  228 (6147 expanded)
%              Number of leaves         :   44 (2079 expanded)
%              Depth                    :   39
%              Number of atoms          :  427 (14682 expanded)
%              Number of equality atoms :  119 (4027 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_146,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_1'(A_93,B_94),A_93)
      | r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_154,plain,(
    ! [A_93] : r1_tarski(A_93,A_93) ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_82,plain,(
    v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_80,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_390,plain,(
    ! [A_138,B_139,C_140] :
      ( k1_relset_1(A_138,B_139,C_140) = k1_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_394,plain,(
    k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_80,c_390])).

tff(c_173796,plain,(
    ! [B_256476,A_256477,C_256478] :
      ( k1_xboole_0 = B_256476
      | k1_relset_1(A_256477,B_256476,C_256478) = A_256477
      | ~ v1_funct_2(C_256478,A_256477,B_256476)
      | ~ m1_subset_1(C_256478,k1_zfmisc_1(k2_zfmisc_1(A_256477,B_256476))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_173799,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_80,c_173796])).

tff(c_173802,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_394,c_173799])).

tff(c_173803,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_173802])).

tff(c_78,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_188,plain,(
    ! [C_104,B_105,A_106] :
      ( r2_hidden(C_104,B_105)
      | ~ r2_hidden(C_104,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [B_105] :
      ( r2_hidden('#skF_10',B_105)
      | ~ r1_tarski('#skF_8',B_105) ) ),
    inference(resolution,[status(thm)],[c_78,c_188])).

tff(c_140,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_144,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_80,c_140])).

tff(c_84,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_172850,plain,(
    ! [B_256443,A_256444,C_256445] :
      ( k1_xboole_0 = B_256443
      | k1_relset_1(A_256444,B_256443,C_256445) = A_256444
      | ~ v1_funct_2(C_256445,A_256444,B_256443)
      | ~ m1_subset_1(C_256445,k1_zfmisc_1(k2_zfmisc_1(A_256444,B_256443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_172853,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_80,c_172850])).

tff(c_172856,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_394,c_172853])).

tff(c_172857,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_172856])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_402,plain,(
    ! [A_145,B_146,B_147] :
      ( r2_hidden('#skF_1'(A_145,B_146),B_147)
      | ~ r1_tarski(A_145,B_147)
      | r1_tarski(A_145,B_146) ) ),
    inference(resolution,[status(thm)],[c_6,c_188])).

tff(c_54,plain,(
    ! [B_59,A_58] :
      ( ~ r1_tarski(B_59,A_58)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_455,plain,(
    ! [B_151,A_152,B_153] :
      ( ~ r1_tarski(B_151,'#skF_1'(A_152,B_153))
      | ~ r1_tarski(A_152,B_151)
      | r1_tarski(A_152,B_153) ) ),
    inference(resolution,[status(thm)],[c_402,c_54])).

tff(c_483,plain,(
    ! [A_154,B_155] :
      ( ~ r1_tarski(A_154,k1_xboole_0)
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_8,c_455])).

tff(c_497,plain,(
    ! [B_17,B_155] :
      ( r1_tarski(k2_relat_1(B_17),B_155)
      | ~ v5_relat_1(B_17,k1_xboole_0)
      | ~ v1_relat_1(B_17) ) ),
    inference(resolution,[status(thm)],[c_34,c_483])).

tff(c_164,plain,(
    ! [C_98,B_99,A_100] :
      ( v5_relat_1(C_98,B_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_168,plain,(
    v5_relat_1('#skF_11',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_80,c_164])).

tff(c_28,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,(
    ! [D_101,B_102,A_103] :
      ( D_101 = B_102
      | D_101 = A_103
      | ~ r2_hidden(D_101,k2_tarski(A_103,B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_179,plain,(
    ! [D_101,A_13] :
      ( D_101 = A_13
      | D_101 = A_13
      | ~ r2_hidden(D_101,k1_tarski(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_169])).

tff(c_437,plain,(
    ! [A_148,A_149,B_150] :
      ( A_148 = '#skF_1'(A_149,B_150)
      | ~ r1_tarski(A_149,k1_tarski(A_148))
      | r1_tarski(A_149,B_150) ) ),
    inference(resolution,[status(thm)],[c_402,c_179])).

tff(c_1292,plain,(
    ! [A_232,B_233,B_234] :
      ( A_232 = '#skF_1'(k2_relat_1(B_233),B_234)
      | r1_tarski(k2_relat_1(B_233),B_234)
      | ~ v5_relat_1(B_233,k1_tarski(A_232))
      | ~ v1_relat_1(B_233) ) ),
    inference(resolution,[status(thm)],[c_34,c_437])).

tff(c_1294,plain,(
    ! [B_234] :
      ( '#skF_1'(k2_relat_1('#skF_11'),B_234) = '#skF_9'
      | r1_tarski(k2_relat_1('#skF_11'),B_234)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_168,c_1292])).

tff(c_1299,plain,(
    ! [B_238] :
      ( '#skF_1'(k2_relat_1('#skF_11'),B_238) = '#skF_9'
      | r1_tarski(k2_relat_1('#skF_11'),B_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_1294])).

tff(c_482,plain,(
    ! [A_152,B_153] :
      ( ~ r1_tarski(A_152,k1_xboole_0)
      | r1_tarski(A_152,B_153) ) ),
    inference(resolution,[status(thm)],[c_8,c_455])).

tff(c_1340,plain,(
    ! [B_153] :
      ( r1_tarski(k2_relat_1('#skF_11'),B_153)
      | '#skF_1'(k2_relat_1('#skF_11'),k1_xboole_0) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1299,c_482])).

tff(c_1384,plain,(
    '#skF_1'(k2_relat_1('#skF_11'),k1_xboole_0) = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1340])).

tff(c_1410,plain,
    ( r2_hidden('#skF_9',k2_relat_1('#skF_11'))
    | r1_tarski(k2_relat_1('#skF_11'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1384,c_6])).

tff(c_1425,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1410])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( v5_relat_1(B_17,A_16)
      | ~ r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1444,plain,
    ( v5_relat_1('#skF_11',k1_xboole_0)
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_1425,c_32])).

tff(c_1453,plain,(
    v5_relat_1('#skF_11',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_1444])).

tff(c_699,plain,(
    ! [B_168,B_169] :
      ( r1_tarski(k2_relat_1(B_168),B_169)
      | ~ v5_relat_1(B_168,k1_xboole_0)
      | ~ v1_relat_1(B_168) ) ),
    inference(resolution,[status(thm)],[c_34,c_483])).

tff(c_725,plain,(
    ! [B_168,B_169] :
      ( v5_relat_1(B_168,B_169)
      | ~ v5_relat_1(B_168,k1_xboole_0)
      | ~ v1_relat_1(B_168) ) ),
    inference(resolution,[status(thm)],[c_699,c_32])).

tff(c_1457,plain,(
    ! [B_169] :
      ( v5_relat_1('#skF_11',B_169)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_1453,c_725])).

tff(c_1460,plain,(
    ! [B_169] : v5_relat_1('#skF_11',B_169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_1457])).

tff(c_277,plain,(
    ! [B_122,A_123] :
      ( r1_tarski(k2_relat_1(B_122),A_123)
      | ~ v5_relat_1(B_122,A_123)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_155,plain,(
    ! [A_93,B_94] :
      ( ~ r1_tarski(A_93,'#skF_1'(A_93,B_94))
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_146,c_54])).

tff(c_289,plain,(
    ! [B_122,B_94] :
      ( r1_tarski(k2_relat_1(B_122),B_94)
      | ~ v5_relat_1(B_122,'#skF_1'(k2_relat_1(B_122),B_94))
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_277,c_155])).

tff(c_1398,plain,
    ( r1_tarski(k2_relat_1('#skF_11'),k1_xboole_0)
    | ~ v5_relat_1('#skF_11','#skF_9')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_1384,c_289])).

tff(c_1421,plain,
    ( r1_tarski(k2_relat_1('#skF_11'),k1_xboole_0)
    | ~ v5_relat_1('#skF_11','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_1398])).

tff(c_1424,plain,(
    ~ v5_relat_1('#skF_11','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1421])).

tff(c_1466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1460,c_1424])).

tff(c_1468,plain,(
    ~ r1_tarski(k2_relat_1('#skF_11'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1410])).

tff(c_1474,plain,
    ( ~ v5_relat_1('#skF_11',k1_xboole_0)
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_497,c_1468])).

tff(c_1482,plain,(
    ~ v5_relat_1('#skF_11',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_1474])).

tff(c_76,plain,(
    k1_funct_1('#skF_11','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3458,plain,(
    ! [B_303,A_304,C_305] :
      ( k1_xboole_0 = B_303
      | k1_relset_1(A_304,B_303,C_305) = A_304
      | ~ v1_funct_2(C_305,A_304,B_303)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_304,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3461,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_80,c_3458])).

tff(c_3464,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_394,c_3461])).

tff(c_3465,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3464])).

tff(c_36,plain,(
    ! [A_18,D_57] :
      ( r2_hidden(k1_funct_1(A_18,D_57),k2_relat_1(A_18))
      | ~ r2_hidden(D_57,k1_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_240,plain,(
    ! [D_113,A_114] :
      ( D_113 = A_114
      | D_113 = A_114
      | ~ r2_hidden(D_113,k1_tarski(A_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_169])).

tff(c_253,plain,(
    ! [A_114,B_2] :
      ( '#skF_1'(k1_tarski(A_114),B_2) = A_114
      | r1_tarski(k1_tarski(A_114),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_240])).

tff(c_87,plain,(
    ! [A_75] : k2_tarski(A_75,A_75) = k1_tarski(A_75) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [D_12,A_7] : r2_hidden(D_12,k2_tarski(A_7,D_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,(
    ! [A_75] : r2_hidden(A_75,k1_tarski(A_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_12])).

tff(c_105,plain,(
    ! [B_79,A_80] :
      ( ~ r1_tarski(B_79,A_80)
      | ~ r2_hidden(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_119,plain,(
    ! [A_75] : ~ r1_tarski(k1_tarski(A_75),A_75) ),
    inference(resolution,[status(thm)],[c_93,c_105])).

tff(c_310,plain,(
    ! [A_132,B_133] :
      ( '#skF_1'(k1_tarski(A_132),B_133) = A_132
      | r1_tarski(k1_tarski(A_132),B_133) ) ),
    inference(resolution,[status(thm)],[c_6,c_240])).

tff(c_331,plain,(
    ! [B_133] : '#skF_1'(k1_tarski(B_133),B_133) = B_133 ),
    inference(resolution,[status(thm)],[c_310,c_119])).

tff(c_431,plain,(
    ! [A_13,A_145,B_146] :
      ( A_13 = '#skF_1'(A_145,B_146)
      | ~ r1_tarski(A_145,k1_tarski(A_13))
      | r1_tarski(A_145,B_146) ) ),
    inference(resolution,[status(thm)],[c_402,c_179])).

tff(c_37142,plain,(
    ! [A_51236,B_51237] :
      ( A_51236 = '#skF_1'(k2_relat_1('#skF_11'),B_51237)
      | r1_tarski(k2_relat_1('#skF_11'),B_51237)
      | '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(A_51236)) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1299,c_431])).

tff(c_41233,plain,(
    ! [B_51237,A_51236] :
      ( v5_relat_1('#skF_11',B_51237)
      | ~ v1_relat_1('#skF_11')
      | A_51236 = '#skF_1'(k2_relat_1('#skF_11'),B_51237)
      | '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(A_51236)) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_37142,c_32])).

tff(c_44241,plain,(
    ! [B_61113,A_61114] :
      ( v5_relat_1('#skF_11',B_61113)
      | A_61114 = '#skF_1'(k2_relat_1('#skF_11'),B_61113)
      | '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(A_61114)) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_41233])).

tff(c_49020,plain,(
    ! [B_61113] :
      ( m1_subset_1('#skF_11',k1_zfmisc_1('#skF_1'(k2_relat_1('#skF_11'),B_61113)))
      | v5_relat_1('#skF_11',B_61113)
      | '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44241,c_80])).

tff(c_51374,plain,(
    '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_49020])).

tff(c_1342,plain,(
    ! [A_13,B_146] :
      ( A_13 = '#skF_1'(k2_relat_1('#skF_11'),B_146)
      | r1_tarski(k2_relat_1('#skF_11'),B_146)
      | '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(A_13)) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1299,c_431])).

tff(c_41816,plain,(
    ! [B_51237,A_51236] :
      ( v5_relat_1('#skF_11',B_51237)
      | A_51236 = '#skF_1'(k2_relat_1('#skF_11'),B_51237)
      | '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(A_51236)) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_41233])).

tff(c_49895,plain,(
    ! [A_69860] :
      ( v5_relat_1('#skF_11',k1_tarski(A_69860))
      | '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(A_69860)) = A_69860
      | A_69860 != '#skF_9' ) ),
    inference(factorization,[status(thm),theory(equality)],[c_41816])).

tff(c_49967,plain,(
    ! [A_69860] :
      ( ~ r2_hidden(A_69860,k1_tarski(A_69860))
      | r1_tarski(k2_relat_1('#skF_11'),k1_tarski(A_69860))
      | v5_relat_1('#skF_11',k1_tarski(A_69860))
      | A_69860 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49895,c_4])).

tff(c_50382,plain,(
    ! [A_70125] :
      ( r1_tarski(k2_relat_1('#skF_11'),k1_tarski(A_70125))
      | v5_relat_1('#skF_11',k1_tarski(A_70125))
      | A_70125 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_49967])).

tff(c_50402,plain,(
    ! [A_70125] :
      ( ~ v1_relat_1('#skF_11')
      | v5_relat_1('#skF_11',k1_tarski(A_70125))
      | A_70125 != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_50382,c_32])).

tff(c_50511,plain,(
    ! [A_70125] :
      ( v5_relat_1('#skF_11',k1_tarski(A_70125))
      | A_70125 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_50402])).

tff(c_3604,plain,(
    ! [A_311,B_312] :
      ( r2_hidden('#skF_5'(A_311,B_312),k1_relat_1(A_311))
      | r2_hidden('#skF_6'(A_311,B_312),B_312)
      | k2_relat_1(A_311) = B_312
      | ~ v1_funct_1(A_311)
      | ~ v1_relat_1(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3646,plain,(
    ! [B_312] :
      ( r2_hidden('#skF_5'('#skF_11',B_312),'#skF_8')
      | r2_hidden('#skF_6'('#skF_11',B_312),B_312)
      | k2_relat_1('#skF_11') = B_312
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3465,c_3604])).

tff(c_3734,plain,(
    ! [B_315] :
      ( r2_hidden('#skF_5'('#skF_11',B_315),'#skF_8')
      | r2_hidden('#skF_6'('#skF_11',B_315),B_315)
      | k2_relat_1('#skF_11') = B_315 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_84,c_3646])).

tff(c_559,plain,(
    ! [A_161,B_162] :
      ( r1_tarski(k1_tarski(A_161),B_162)
      | '#skF_1'(k1_tarski(A_161),k1_xboole_0) = A_161 ) ),
    inference(resolution,[status(thm)],[c_253,c_483])).

tff(c_599,plain,(
    ! [B_163] : '#skF_1'(k1_tarski(B_163),k1_xboole_0) = B_163 ),
    inference(resolution,[status(thm)],[c_559,c_119])).

tff(c_657,plain,(
    ! [B_164] :
      ( ~ r2_hidden(B_164,k1_xboole_0)
      | r1_tarski(k1_tarski(B_164),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_4])).

tff(c_461,plain,(
    ! [B_151,B_133] :
      ( ~ r1_tarski(B_151,B_133)
      | ~ r1_tarski(k1_tarski(B_133),B_151)
      | r1_tarski(k1_tarski(B_133),B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_455])).

tff(c_478,plain,(
    ! [B_151,B_133] :
      ( ~ r1_tarski(B_151,B_133)
      | ~ r1_tarski(k1_tarski(B_133),B_151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_461])).

tff(c_660,plain,(
    ! [B_164] :
      ( ~ r1_tarski(k1_xboole_0,B_164)
      | ~ r2_hidden(B_164,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_657,c_478])).

tff(c_674,plain,(
    ! [B_164] : ~ r2_hidden(B_164,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_660])).

tff(c_3778,plain,
    ( r2_hidden('#skF_5'('#skF_11',k1_xboole_0),'#skF_8')
    | k2_relat_1('#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3734,c_674])).

tff(c_3783,plain,(
    k2_relat_1('#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3778])).

tff(c_1467,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_1410])).

tff(c_1498,plain,(
    ~ r1_tarski(k2_relat_1('#skF_11'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_1467,c_54])).

tff(c_3803,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3783,c_1498])).

tff(c_3823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3803])).

tff(c_3825,plain,(
    k2_relat_1('#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3778])).

tff(c_3824,plain,(
    r2_hidden('#skF_5'('#skF_11',k1_xboole_0),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_3778])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4453,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_5'('#skF_11',k1_xboole_0),B_2)
      | ~ r1_tarski('#skF_8',B_2) ) ),
    inference(resolution,[status(thm)],[c_3824,c_2])).

tff(c_7252,plain,(
    ! [A_15542,B_15543] :
      ( k1_funct_1(A_15542,'#skF_5'(A_15542,B_15543)) = '#skF_4'(A_15542,B_15543)
      | r2_hidden('#skF_6'(A_15542,B_15543),B_15543)
      | k2_relat_1(A_15542) = B_15543
      | ~ v1_funct_1(A_15542)
      | ~ v1_relat_1(A_15542) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_92093,plain,(
    ! [A_154654,B_154655] :
      ( r2_hidden('#skF_4'(A_154654,B_154655),k2_relat_1(A_154654))
      | ~ r2_hidden('#skF_5'(A_154654,B_154655),k1_relat_1(A_154654))
      | ~ v1_funct_1(A_154654)
      | ~ v1_relat_1(A_154654)
      | r2_hidden('#skF_6'(A_154654,B_154655),B_154655)
      | k2_relat_1(A_154654) = B_154655
      | ~ v1_funct_1(A_154654)
      | ~ v1_relat_1(A_154654) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7252,c_36])).

tff(c_92158,plain,
    ( r2_hidden('#skF_4'('#skF_11',k1_xboole_0),k2_relat_1('#skF_11'))
    | r2_hidden('#skF_6'('#skF_11',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_11') = k1_xboole_0
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11')
    | ~ r1_tarski('#skF_8',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_4453,c_92093])).

tff(c_92182,plain,
    ( r2_hidden('#skF_4'('#skF_11',k1_xboole_0),k2_relat_1('#skF_11'))
    | r2_hidden('#skF_6'('#skF_11',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_3465,c_144,c_84,c_92158])).

tff(c_92183,plain,(
    r2_hidden('#skF_4'('#skF_11',k1_xboole_0),k2_relat_1('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_3825,c_674,c_92182])).

tff(c_93106,plain,(
    ! [B_157334] :
      ( r2_hidden('#skF_4'('#skF_11',k1_xboole_0),B_157334)
      | ~ r1_tarski(k2_relat_1('#skF_11'),B_157334) ) ),
    inference(resolution,[status(thm)],[c_92183,c_2])).

tff(c_93268,plain,(
    ! [A_157632] :
      ( A_157632 = '#skF_4'('#skF_11',k1_xboole_0)
      | ~ r1_tarski(k2_relat_1('#skF_11'),k1_tarski(A_157632)) ) ),
    inference(resolution,[status(thm)],[c_93106,c_179])).

tff(c_93320,plain,(
    ! [A_157632] :
      ( A_157632 = '#skF_4'('#skF_11',k1_xboole_0)
      | ~ v5_relat_1('#skF_11',k1_tarski(A_157632))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_34,c_93268])).

tff(c_93337,plain,(
    ! [A_157930] :
      ( A_157930 = '#skF_4'('#skF_11',k1_xboole_0)
      | ~ v5_relat_1('#skF_11',k1_tarski(A_157930)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_93320])).

tff(c_93426,plain,(
    '#skF_4'('#skF_11',k1_xboole_0) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_50511,c_93337])).

tff(c_93264,plain,(
    ! [A_13] :
      ( A_13 = '#skF_4'('#skF_11',k1_xboole_0)
      | ~ r1_tarski(k2_relat_1('#skF_11'),k1_tarski(A_13)) ) ),
    inference(resolution,[status(thm)],[c_93106,c_179])).

tff(c_93531,plain,(
    ! [A_159421] :
      ( A_159421 = '#skF_9'
      | ~ r1_tarski(k2_relat_1('#skF_11'),k1_tarski(A_159421)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93426,c_93264])).

tff(c_127250,plain,(
    ! [A_199093,A_199094] :
      ( A_199093 = '#skF_9'
      | A_199094 = '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(A_199093))
      | '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(A_199094)) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1342,c_93531])).

tff(c_129961,plain,(
    ! [A_199093] :
      ( '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(A_199093)) = '#skF_9'
      | A_199093 = '#skF_9'
      | '#skF_1'(k2_relat_1('#skF_11'),k1_tarski('#skF_1'(k2_relat_1('#skF_11'),k1_tarski(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))))) = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127250,c_51374])).

tff(c_135994,plain,(
    ! [A_199093] :
      ( '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(A_199093)) = '#skF_9'
      | A_199093 = '#skF_9'
      | '#skF_1'(k2_relat_1('#skF_11'),k1_tarski('#skF_9')) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51374,c_129961])).

tff(c_147588,plain,(
    '#skF_1'(k2_relat_1('#skF_11'),k1_tarski('#skF_9')) = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_135994])).

tff(c_147704,plain,
    ( ~ r2_hidden('#skF_9',k1_tarski('#skF_9'))
    | r1_tarski(k2_relat_1('#skF_11'),k1_tarski('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_147588,c_4])).

tff(c_148138,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k1_tarski('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_147704])).

tff(c_432,plain,(
    ! [A_145,B_146,B_2,B_147] :
      ( r2_hidden('#skF_1'(A_145,B_146),B_2)
      | ~ r1_tarski(B_147,B_2)
      | ~ r1_tarski(A_145,B_147)
      | r1_tarski(A_145,B_146) ) ),
    inference(resolution,[status(thm)],[c_402,c_2])).

tff(c_148284,plain,(
    ! [A_226587,B_226588] :
      ( r2_hidden('#skF_1'(A_226587,B_226588),k1_tarski('#skF_9'))
      | ~ r1_tarski(A_226587,k2_relat_1('#skF_11'))
      | r1_tarski(A_226587,B_226588) ) ),
    inference(resolution,[status(thm)],[c_148138,c_432])).

tff(c_149435,plain,(
    ! [B_133] :
      ( r2_hidden(B_133,k1_tarski('#skF_9'))
      | ~ r1_tarski(k1_tarski(B_133),k2_relat_1('#skF_11'))
      | r1_tarski(k1_tarski(B_133),B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_148284])).

tff(c_149878,plain,(
    ! [B_227316] :
      ( r2_hidden(B_227316,k1_tarski('#skF_9'))
      | ~ r1_tarski(k1_tarski(B_227316),k2_relat_1('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_149435])).

tff(c_150321,plain,(
    ! [A_228770] :
      ( r2_hidden(A_228770,k1_tarski('#skF_9'))
      | '#skF_1'(k1_tarski(A_228770),k2_relat_1('#skF_11')) = A_228770 ) ),
    inference(resolution,[status(thm)],[c_253,c_149878])).

tff(c_157113,plain,(
    ! [A_238960] :
      ( ~ r2_hidden(A_238960,k2_relat_1('#skF_11'))
      | r1_tarski(k1_tarski(A_238960),k2_relat_1('#skF_11'))
      | r2_hidden(A_238960,k1_tarski('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150321,c_4])).

tff(c_149735,plain,(
    ! [B_133] :
      ( r2_hidden(B_133,k1_tarski('#skF_9'))
      | ~ r1_tarski(k1_tarski(B_133),k2_relat_1('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_149435])).

tff(c_159257,plain,(
    ! [A_239690] :
      ( ~ r2_hidden(A_239690,k2_relat_1('#skF_11'))
      | r2_hidden(A_239690,k1_tarski('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_157113,c_149735])).

tff(c_159394,plain,(
    ! [D_57] :
      ( r2_hidden(k1_funct_1('#skF_11',D_57),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_57,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_36,c_159257])).

tff(c_159448,plain,(
    ! [D_240054] :
      ( r2_hidden(k1_funct_1('#skF_11',D_240054),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_240054,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_84,c_3465,c_159394])).

tff(c_159585,plain,(
    ! [D_240418] :
      ( k1_funct_1('#skF_11',D_240418) = '#skF_9'
      | ~ r2_hidden(D_240418,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_159448,c_179])).

tff(c_159727,plain,
    ( k1_funct_1('#skF_11','#skF_10') = '#skF_9'
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_203,c_159585])).

tff(c_159787,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_159727])).

tff(c_159789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_159787])).

tff(c_159791,plain,(
    '#skF_1'(k2_relat_1('#skF_11'),k1_tarski('#skF_9')) != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_135994])).

tff(c_1297,plain,(
    ! [B_234] :
      ( '#skF_1'(k2_relat_1('#skF_11'),B_234) = '#skF_9'
      | r1_tarski(k2_relat_1('#skF_11'),B_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_1294])).

tff(c_159843,plain,(
    ! [A_13] :
      ( A_13 != '#skF_9'
      | r1_tarski(k2_relat_1('#skF_11'),k1_tarski('#skF_9'))
      | '#skF_1'(k2_relat_1('#skF_11'),k1_tarski(A_13)) = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1342,c_159791])).

tff(c_160853,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k1_tarski('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_159843])).

tff(c_160969,plain,(
    ! [A_241872,B_241873] :
      ( r2_hidden('#skF_1'(A_241872,B_241873),k1_tarski('#skF_9'))
      | ~ r1_tarski(A_241872,k2_relat_1('#skF_11'))
      | r1_tarski(A_241872,B_241873) ) ),
    inference(resolution,[status(thm)],[c_160853,c_432])).

tff(c_162117,plain,(
    ! [B_133] :
      ( r2_hidden(B_133,k1_tarski('#skF_9'))
      | ~ r1_tarski(k1_tarski(B_133),k2_relat_1('#skF_11'))
      | r1_tarski(k1_tarski(B_133),B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_160969])).

tff(c_162562,plain,(
    ! [B_242601] :
      ( r2_hidden(B_242601,k1_tarski('#skF_9'))
      | ~ r1_tarski(k1_tarski(B_242601),k2_relat_1('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_162117])).

tff(c_163005,plain,(
    ! [A_244055] :
      ( r2_hidden(A_244055,k1_tarski('#skF_9'))
      | '#skF_1'(k1_tarski(A_244055),k2_relat_1('#skF_11')) = A_244055 ) ),
    inference(resolution,[status(thm)],[c_253,c_162562])).

tff(c_171745,plain,(
    ! [A_254611] :
      ( ~ r2_hidden(A_254611,k2_relat_1('#skF_11'))
      | r1_tarski(k1_tarski(A_254611),k2_relat_1('#skF_11'))
      | r2_hidden(A_254611,k1_tarski('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163005,c_4])).

tff(c_162419,plain,(
    ! [B_133] :
      ( r2_hidden(B_133,k1_tarski('#skF_9'))
      | ~ r1_tarski(k1_tarski(B_133),k2_relat_1('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_162117])).

tff(c_171936,plain,(
    ! [A_254975] :
      ( ~ r2_hidden(A_254975,k2_relat_1('#skF_11'))
      | r2_hidden(A_254975,k1_tarski('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_171745,c_162419])).

tff(c_172073,plain,(
    ! [D_57] :
      ( r2_hidden(k1_funct_1('#skF_11',D_57),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_57,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_36,c_171936])).

tff(c_172127,plain,(
    ! [D_255339] :
      ( r2_hidden(k1_funct_1('#skF_11',D_255339),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_255339,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_84,c_3465,c_172073])).

tff(c_172264,plain,(
    ! [D_255703] :
      ( k1_funct_1('#skF_11',D_255703) = '#skF_9'
      | ~ r2_hidden(D_255703,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_172127,c_179])).

tff(c_172406,plain,
    ( k1_funct_1('#skF_11','#skF_10') = '#skF_9'
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_203,c_172264])).

tff(c_172466,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_172406])).

tff(c_172468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_172466])).

tff(c_172470,plain,(
    ~ r1_tarski(k2_relat_1('#skF_11'),k1_tarski('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_159843])).

tff(c_172499,plain,(
    '#skF_1'(k2_relat_1('#skF_11'),k1_tarski('#skF_9')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1297,c_172470])).

tff(c_172527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159791,c_172499])).

tff(c_172528,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3464])).

tff(c_172531,plain,(
    v5_relat_1('#skF_11',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172528,c_168])).

tff(c_172535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1482,c_172531])).

tff(c_172536,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1421])).

tff(c_172613,plain,(
    ! [B_256433] : r1_tarski(k2_relat_1('#skF_11'),B_256433) ),
    inference(resolution,[status(thm)],[c_172536,c_482])).

tff(c_804,plain,(
    ! [A_179,D_180] :
      ( r2_hidden(k1_funct_1(A_179,D_180),k2_relat_1(A_179))
      | ~ r2_hidden(D_180,k1_relat_1(A_179))
      | ~ v1_funct_1(A_179)
      | ~ v1_relat_1(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_811,plain,(
    ! [A_179,D_180] :
      ( ~ r1_tarski(k2_relat_1(A_179),k1_funct_1(A_179,D_180))
      | ~ r2_hidden(D_180,k1_relat_1(A_179))
      | ~ v1_funct_1(A_179)
      | ~ v1_relat_1(A_179) ) ),
    inference(resolution,[status(thm)],[c_804,c_54])).

tff(c_172622,plain,(
    ! [D_180] :
      ( ~ r2_hidden(D_180,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_172613,c_811])).

tff(c_172668,plain,(
    ! [D_256434] : ~ r2_hidden(D_256434,k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_84,c_172622])).

tff(c_172689,plain,(
    ~ r1_tarski('#skF_8',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_203,c_172668])).

tff(c_172860,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172857,c_172689])).

tff(c_172865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_172860])).

tff(c_172866,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_172856])).

tff(c_172940,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_172866,c_119])).

tff(c_172965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_172940])).

tff(c_172970,plain,(
    ! [B_256446] : r1_tarski(k2_relat_1('#skF_11'),B_256446) ),
    inference(splitRight,[status(thm)],[c_1340])).

tff(c_172979,plain,(
    ! [D_180] :
      ( ~ r2_hidden(D_180,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_172970,c_811])).

tff(c_173061,plain,(
    ! [D_256448] : ~ r2_hidden(D_256448,k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_84,c_172979])).

tff(c_173075,plain,(
    ~ r1_tarski('#skF_8',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_203,c_173061])).

tff(c_173807,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173803,c_173075])).

tff(c_173813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_173807])).

tff(c_173814,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_173802])).

tff(c_173894,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_173814,c_119])).

tff(c_173919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_173894])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:52:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.50/23.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.50/23.68  
% 34.50/23.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.50/23.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 34.50/23.68  
% 34.50/23.68  %Foreground sorts:
% 34.50/23.68  
% 34.50/23.68  
% 34.50/23.68  %Background operators:
% 34.50/23.68  
% 34.50/23.68  
% 34.50/23.68  %Foreground operators:
% 34.50/23.68  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 34.50/23.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 34.50/23.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.50/23.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 34.50/23.68  tff('#skF_11', type, '#skF_11': $i).
% 34.50/23.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 34.50/23.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 34.50/23.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 34.50/23.68  tff('#skF_10', type, '#skF_10': $i).
% 34.50/23.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 34.50/23.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 34.50/23.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 34.50/23.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 34.50/23.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 34.50/23.68  tff('#skF_9', type, '#skF_9': $i).
% 34.50/23.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 34.50/23.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 34.50/23.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 34.50/23.68  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 34.50/23.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 34.50/23.68  tff('#skF_8', type, '#skF_8': $i).
% 34.50/23.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.50/23.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 34.50/23.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 34.50/23.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 34.50/23.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.50/23.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 34.50/23.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 34.50/23.68  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 34.50/23.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 34.50/23.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 34.50/23.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 34.50/23.68  
% 34.77/23.71  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 34.77/23.71  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 34.77/23.71  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 34.77/23.71  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 34.77/23.71  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 34.77/23.71  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 34.77/23.71  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 34.77/23.71  tff(f_73, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 34.77/23.71  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 34.77/23.71  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 34.77/23.71  tff(f_43, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 34.77/23.71  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 34.77/23.71  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 34.77/23.71  tff(c_146, plain, (![A_93, B_94]: (r2_hidden('#skF_1'(A_93, B_94), A_93) | r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.77/23.71  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.77/23.71  tff(c_154, plain, (![A_93]: (r1_tarski(A_93, A_93))), inference(resolution, [status(thm)], [c_146, c_4])).
% 34.77/23.71  tff(c_82, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 34.77/23.71  tff(c_80, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 34.77/23.71  tff(c_390, plain, (![A_138, B_139, C_140]: (k1_relset_1(A_138, B_139, C_140)=k1_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 34.77/23.71  tff(c_394, plain, (k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_80, c_390])).
% 34.77/23.71  tff(c_173796, plain, (![B_256476, A_256477, C_256478]: (k1_xboole_0=B_256476 | k1_relset_1(A_256477, B_256476, C_256478)=A_256477 | ~v1_funct_2(C_256478, A_256477, B_256476) | ~m1_subset_1(C_256478, k1_zfmisc_1(k2_zfmisc_1(A_256477, B_256476))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 34.77/23.71  tff(c_173799, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_80, c_173796])).
% 34.77/23.71  tff(c_173802, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_394, c_173799])).
% 34.77/23.71  tff(c_173803, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_173802])).
% 34.77/23.71  tff(c_78, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_116])).
% 34.77/23.71  tff(c_188, plain, (![C_104, B_105, A_106]: (r2_hidden(C_104, B_105) | ~r2_hidden(C_104, A_106) | ~r1_tarski(A_106, B_105))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.77/23.71  tff(c_203, plain, (![B_105]: (r2_hidden('#skF_10', B_105) | ~r1_tarski('#skF_8', B_105))), inference(resolution, [status(thm)], [c_78, c_188])).
% 34.77/23.71  tff(c_140, plain, (![C_88, A_89, B_90]: (v1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 34.77/23.71  tff(c_144, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_80, c_140])).
% 34.77/23.71  tff(c_84, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_116])).
% 34.77/23.71  tff(c_172850, plain, (![B_256443, A_256444, C_256445]: (k1_xboole_0=B_256443 | k1_relset_1(A_256444, B_256443, C_256445)=A_256444 | ~v1_funct_2(C_256445, A_256444, B_256443) | ~m1_subset_1(C_256445, k1_zfmisc_1(k2_zfmisc_1(A_256444, B_256443))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 34.77/23.71  tff(c_172853, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_80, c_172850])).
% 34.77/23.71  tff(c_172856, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_394, c_172853])).
% 34.77/23.71  tff(c_172857, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_172856])).
% 34.77/23.71  tff(c_34, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 34.77/23.71  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.77/23.71  tff(c_402, plain, (![A_145, B_146, B_147]: (r2_hidden('#skF_1'(A_145, B_146), B_147) | ~r1_tarski(A_145, B_147) | r1_tarski(A_145, B_146))), inference(resolution, [status(thm)], [c_6, c_188])).
% 34.77/23.71  tff(c_54, plain, (![B_59, A_58]: (~r1_tarski(B_59, A_58) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_73])).
% 34.77/23.71  tff(c_455, plain, (![B_151, A_152, B_153]: (~r1_tarski(B_151, '#skF_1'(A_152, B_153)) | ~r1_tarski(A_152, B_151) | r1_tarski(A_152, B_153))), inference(resolution, [status(thm)], [c_402, c_54])).
% 34.77/23.71  tff(c_483, plain, (![A_154, B_155]: (~r1_tarski(A_154, k1_xboole_0) | r1_tarski(A_154, B_155))), inference(resolution, [status(thm)], [c_8, c_455])).
% 34.77/23.71  tff(c_497, plain, (![B_17, B_155]: (r1_tarski(k2_relat_1(B_17), B_155) | ~v5_relat_1(B_17, k1_xboole_0) | ~v1_relat_1(B_17))), inference(resolution, [status(thm)], [c_34, c_483])).
% 34.77/23.71  tff(c_164, plain, (![C_98, B_99, A_100]: (v5_relat_1(C_98, B_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 34.77/23.71  tff(c_168, plain, (v5_relat_1('#skF_11', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_80, c_164])).
% 34.77/23.71  tff(c_28, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 34.77/23.71  tff(c_169, plain, (![D_101, B_102, A_103]: (D_101=B_102 | D_101=A_103 | ~r2_hidden(D_101, k2_tarski(A_103, B_102)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 34.77/23.71  tff(c_179, plain, (![D_101, A_13]: (D_101=A_13 | D_101=A_13 | ~r2_hidden(D_101, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_169])).
% 34.77/23.71  tff(c_437, plain, (![A_148, A_149, B_150]: (A_148='#skF_1'(A_149, B_150) | ~r1_tarski(A_149, k1_tarski(A_148)) | r1_tarski(A_149, B_150))), inference(resolution, [status(thm)], [c_402, c_179])).
% 34.77/23.71  tff(c_1292, plain, (![A_232, B_233, B_234]: (A_232='#skF_1'(k2_relat_1(B_233), B_234) | r1_tarski(k2_relat_1(B_233), B_234) | ~v5_relat_1(B_233, k1_tarski(A_232)) | ~v1_relat_1(B_233))), inference(resolution, [status(thm)], [c_34, c_437])).
% 34.77/23.71  tff(c_1294, plain, (![B_234]: ('#skF_1'(k2_relat_1('#skF_11'), B_234)='#skF_9' | r1_tarski(k2_relat_1('#skF_11'), B_234) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_168, c_1292])).
% 34.77/23.71  tff(c_1299, plain, (![B_238]: ('#skF_1'(k2_relat_1('#skF_11'), B_238)='#skF_9' | r1_tarski(k2_relat_1('#skF_11'), B_238))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_1294])).
% 34.77/23.71  tff(c_482, plain, (![A_152, B_153]: (~r1_tarski(A_152, k1_xboole_0) | r1_tarski(A_152, B_153))), inference(resolution, [status(thm)], [c_8, c_455])).
% 34.77/23.71  tff(c_1340, plain, (![B_153]: (r1_tarski(k2_relat_1('#skF_11'), B_153) | '#skF_1'(k2_relat_1('#skF_11'), k1_xboole_0)='#skF_9')), inference(resolution, [status(thm)], [c_1299, c_482])).
% 34.77/23.71  tff(c_1384, plain, ('#skF_1'(k2_relat_1('#skF_11'), k1_xboole_0)='#skF_9'), inference(splitLeft, [status(thm)], [c_1340])).
% 34.77/23.71  tff(c_1410, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_11')) | r1_tarski(k2_relat_1('#skF_11'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1384, c_6])).
% 34.77/23.71  tff(c_1425, plain, (r1_tarski(k2_relat_1('#skF_11'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1410])).
% 34.77/23.71  tff(c_32, plain, (![B_17, A_16]: (v5_relat_1(B_17, A_16) | ~r1_tarski(k2_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 34.77/23.71  tff(c_1444, plain, (v5_relat_1('#skF_11', k1_xboole_0) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_1425, c_32])).
% 34.77/23.71  tff(c_1453, plain, (v5_relat_1('#skF_11', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_1444])).
% 34.77/23.71  tff(c_699, plain, (![B_168, B_169]: (r1_tarski(k2_relat_1(B_168), B_169) | ~v5_relat_1(B_168, k1_xboole_0) | ~v1_relat_1(B_168))), inference(resolution, [status(thm)], [c_34, c_483])).
% 34.77/23.71  tff(c_725, plain, (![B_168, B_169]: (v5_relat_1(B_168, B_169) | ~v5_relat_1(B_168, k1_xboole_0) | ~v1_relat_1(B_168))), inference(resolution, [status(thm)], [c_699, c_32])).
% 34.77/23.71  tff(c_1457, plain, (![B_169]: (v5_relat_1('#skF_11', B_169) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_1453, c_725])).
% 34.77/23.71  tff(c_1460, plain, (![B_169]: (v5_relat_1('#skF_11', B_169))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_1457])).
% 34.77/23.71  tff(c_277, plain, (![B_122, A_123]: (r1_tarski(k2_relat_1(B_122), A_123) | ~v5_relat_1(B_122, A_123) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_53])).
% 34.77/23.71  tff(c_155, plain, (![A_93, B_94]: (~r1_tarski(A_93, '#skF_1'(A_93, B_94)) | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_146, c_54])).
% 34.77/23.71  tff(c_289, plain, (![B_122, B_94]: (r1_tarski(k2_relat_1(B_122), B_94) | ~v5_relat_1(B_122, '#skF_1'(k2_relat_1(B_122), B_94)) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_277, c_155])).
% 34.77/23.71  tff(c_1398, plain, (r1_tarski(k2_relat_1('#skF_11'), k1_xboole_0) | ~v5_relat_1('#skF_11', '#skF_9') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_1384, c_289])).
% 34.77/23.71  tff(c_1421, plain, (r1_tarski(k2_relat_1('#skF_11'), k1_xboole_0) | ~v5_relat_1('#skF_11', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_1398])).
% 34.77/23.71  tff(c_1424, plain, (~v5_relat_1('#skF_11', '#skF_9')), inference(splitLeft, [status(thm)], [c_1421])).
% 34.77/23.71  tff(c_1466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1460, c_1424])).
% 34.77/23.71  tff(c_1468, plain, (~r1_tarski(k2_relat_1('#skF_11'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1410])).
% 34.77/23.71  tff(c_1474, plain, (~v5_relat_1('#skF_11', k1_xboole_0) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_497, c_1468])).
% 34.77/23.71  tff(c_1482, plain, (~v5_relat_1('#skF_11', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_1474])).
% 34.77/23.71  tff(c_76, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_116])).
% 34.77/23.71  tff(c_3458, plain, (![B_303, A_304, C_305]: (k1_xboole_0=B_303 | k1_relset_1(A_304, B_303, C_305)=A_304 | ~v1_funct_2(C_305, A_304, B_303) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_304, B_303))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 34.77/23.71  tff(c_3461, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_80, c_3458])).
% 34.77/23.71  tff(c_3464, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_394, c_3461])).
% 34.77/23.71  tff(c_3465, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_3464])).
% 34.77/23.71  tff(c_36, plain, (![A_18, D_57]: (r2_hidden(k1_funct_1(A_18, D_57), k2_relat_1(A_18)) | ~r2_hidden(D_57, k1_relat_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 34.77/23.71  tff(c_240, plain, (![D_113, A_114]: (D_113=A_114 | D_113=A_114 | ~r2_hidden(D_113, k1_tarski(A_114)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_169])).
% 34.77/23.71  tff(c_253, plain, (![A_114, B_2]: ('#skF_1'(k1_tarski(A_114), B_2)=A_114 | r1_tarski(k1_tarski(A_114), B_2))), inference(resolution, [status(thm)], [c_6, c_240])).
% 34.77/23.71  tff(c_87, plain, (![A_75]: (k2_tarski(A_75, A_75)=k1_tarski(A_75))), inference(cnfTransformation, [status(thm)], [f_45])).
% 34.77/23.71  tff(c_12, plain, (![D_12, A_7]: (r2_hidden(D_12, k2_tarski(A_7, D_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 34.77/23.71  tff(c_93, plain, (![A_75]: (r2_hidden(A_75, k1_tarski(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_12])).
% 34.77/23.71  tff(c_105, plain, (![B_79, A_80]: (~r1_tarski(B_79, A_80) | ~r2_hidden(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_73])).
% 34.77/23.71  tff(c_119, plain, (![A_75]: (~r1_tarski(k1_tarski(A_75), A_75))), inference(resolution, [status(thm)], [c_93, c_105])).
% 34.77/23.71  tff(c_310, plain, (![A_132, B_133]: ('#skF_1'(k1_tarski(A_132), B_133)=A_132 | r1_tarski(k1_tarski(A_132), B_133))), inference(resolution, [status(thm)], [c_6, c_240])).
% 34.77/23.71  tff(c_331, plain, (![B_133]: ('#skF_1'(k1_tarski(B_133), B_133)=B_133)), inference(resolution, [status(thm)], [c_310, c_119])).
% 34.77/23.71  tff(c_431, plain, (![A_13, A_145, B_146]: (A_13='#skF_1'(A_145, B_146) | ~r1_tarski(A_145, k1_tarski(A_13)) | r1_tarski(A_145, B_146))), inference(resolution, [status(thm)], [c_402, c_179])).
% 34.77/23.71  tff(c_37142, plain, (![A_51236, B_51237]: (A_51236='#skF_1'(k2_relat_1('#skF_11'), B_51237) | r1_tarski(k2_relat_1('#skF_11'), B_51237) | '#skF_1'(k2_relat_1('#skF_11'), k1_tarski(A_51236))='#skF_9')), inference(resolution, [status(thm)], [c_1299, c_431])).
% 34.77/23.71  tff(c_41233, plain, (![B_51237, A_51236]: (v5_relat_1('#skF_11', B_51237) | ~v1_relat_1('#skF_11') | A_51236='#skF_1'(k2_relat_1('#skF_11'), B_51237) | '#skF_1'(k2_relat_1('#skF_11'), k1_tarski(A_51236))='#skF_9')), inference(resolution, [status(thm)], [c_37142, c_32])).
% 34.77/23.71  tff(c_44241, plain, (![B_61113, A_61114]: (v5_relat_1('#skF_11', B_61113) | A_61114='#skF_1'(k2_relat_1('#skF_11'), B_61113) | '#skF_1'(k2_relat_1('#skF_11'), k1_tarski(A_61114))='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_41233])).
% 34.77/23.71  tff(c_49020, plain, (![B_61113]: (m1_subset_1('#skF_11', k1_zfmisc_1('#skF_1'(k2_relat_1('#skF_11'), B_61113))) | v5_relat_1('#skF_11', B_61113) | '#skF_1'(k2_relat_1('#skF_11'), k1_tarski(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_44241, c_80])).
% 34.77/23.71  tff(c_51374, plain, ('#skF_1'(k2_relat_1('#skF_11'), k1_tarski(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))='#skF_9'), inference(splitLeft, [status(thm)], [c_49020])).
% 34.77/23.71  tff(c_1342, plain, (![A_13, B_146]: (A_13='#skF_1'(k2_relat_1('#skF_11'), B_146) | r1_tarski(k2_relat_1('#skF_11'), B_146) | '#skF_1'(k2_relat_1('#skF_11'), k1_tarski(A_13))='#skF_9')), inference(resolution, [status(thm)], [c_1299, c_431])).
% 34.77/23.71  tff(c_41816, plain, (![B_51237, A_51236]: (v5_relat_1('#skF_11', B_51237) | A_51236='#skF_1'(k2_relat_1('#skF_11'), B_51237) | '#skF_1'(k2_relat_1('#skF_11'), k1_tarski(A_51236))='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_41233])).
% 34.77/23.71  tff(c_49895, plain, (![A_69860]: (v5_relat_1('#skF_11', k1_tarski(A_69860)) | '#skF_1'(k2_relat_1('#skF_11'), k1_tarski(A_69860))=A_69860 | A_69860!='#skF_9')), inference(factorization, [status(thm), theory('equality')], [c_41816])).
% 34.77/23.71  tff(c_49967, plain, (![A_69860]: (~r2_hidden(A_69860, k1_tarski(A_69860)) | r1_tarski(k2_relat_1('#skF_11'), k1_tarski(A_69860)) | v5_relat_1('#skF_11', k1_tarski(A_69860)) | A_69860!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_49895, c_4])).
% 34.77/23.71  tff(c_50382, plain, (![A_70125]: (r1_tarski(k2_relat_1('#skF_11'), k1_tarski(A_70125)) | v5_relat_1('#skF_11', k1_tarski(A_70125)) | A_70125!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_49967])).
% 34.77/23.71  tff(c_50402, plain, (![A_70125]: (~v1_relat_1('#skF_11') | v5_relat_1('#skF_11', k1_tarski(A_70125)) | A_70125!='#skF_9')), inference(resolution, [status(thm)], [c_50382, c_32])).
% 34.77/23.71  tff(c_50511, plain, (![A_70125]: (v5_relat_1('#skF_11', k1_tarski(A_70125)) | A_70125!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_50402])).
% 34.77/23.71  tff(c_3604, plain, (![A_311, B_312]: (r2_hidden('#skF_5'(A_311, B_312), k1_relat_1(A_311)) | r2_hidden('#skF_6'(A_311, B_312), B_312) | k2_relat_1(A_311)=B_312 | ~v1_funct_1(A_311) | ~v1_relat_1(A_311))), inference(cnfTransformation, [status(thm)], [f_68])).
% 34.77/23.71  tff(c_3646, plain, (![B_312]: (r2_hidden('#skF_5'('#skF_11', B_312), '#skF_8') | r2_hidden('#skF_6'('#skF_11', B_312), B_312) | k2_relat_1('#skF_11')=B_312 | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_3465, c_3604])).
% 34.77/23.71  tff(c_3734, plain, (![B_315]: (r2_hidden('#skF_5'('#skF_11', B_315), '#skF_8') | r2_hidden('#skF_6'('#skF_11', B_315), B_315) | k2_relat_1('#skF_11')=B_315)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_84, c_3646])).
% 34.77/23.71  tff(c_559, plain, (![A_161, B_162]: (r1_tarski(k1_tarski(A_161), B_162) | '#skF_1'(k1_tarski(A_161), k1_xboole_0)=A_161)), inference(resolution, [status(thm)], [c_253, c_483])).
% 34.77/23.71  tff(c_599, plain, (![B_163]: ('#skF_1'(k1_tarski(B_163), k1_xboole_0)=B_163)), inference(resolution, [status(thm)], [c_559, c_119])).
% 34.77/23.71  tff(c_657, plain, (![B_164]: (~r2_hidden(B_164, k1_xboole_0) | r1_tarski(k1_tarski(B_164), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_599, c_4])).
% 34.77/23.71  tff(c_461, plain, (![B_151, B_133]: (~r1_tarski(B_151, B_133) | ~r1_tarski(k1_tarski(B_133), B_151) | r1_tarski(k1_tarski(B_133), B_133))), inference(superposition, [status(thm), theory('equality')], [c_331, c_455])).
% 34.77/23.71  tff(c_478, plain, (![B_151, B_133]: (~r1_tarski(B_151, B_133) | ~r1_tarski(k1_tarski(B_133), B_151))), inference(negUnitSimplification, [status(thm)], [c_119, c_461])).
% 34.77/23.71  tff(c_660, plain, (![B_164]: (~r1_tarski(k1_xboole_0, B_164) | ~r2_hidden(B_164, k1_xboole_0))), inference(resolution, [status(thm)], [c_657, c_478])).
% 34.77/23.71  tff(c_674, plain, (![B_164]: (~r2_hidden(B_164, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_660])).
% 34.77/23.71  tff(c_3778, plain, (r2_hidden('#skF_5'('#skF_11', k1_xboole_0), '#skF_8') | k2_relat_1('#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_3734, c_674])).
% 34.77/23.71  tff(c_3783, plain, (k2_relat_1('#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3778])).
% 34.77/23.71  tff(c_1467, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_1410])).
% 34.77/23.71  tff(c_1498, plain, (~r1_tarski(k2_relat_1('#skF_11'), '#skF_9')), inference(resolution, [status(thm)], [c_1467, c_54])).
% 34.77/23.71  tff(c_3803, plain, (~r1_tarski(k1_xboole_0, '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3783, c_1498])).
% 34.77/23.71  tff(c_3823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_3803])).
% 34.77/23.71  tff(c_3825, plain, (k2_relat_1('#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_3778])).
% 34.77/23.71  tff(c_3824, plain, (r2_hidden('#skF_5'('#skF_11', k1_xboole_0), '#skF_8')), inference(splitRight, [status(thm)], [c_3778])).
% 34.77/23.71  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.77/23.71  tff(c_4453, plain, (![B_2]: (r2_hidden('#skF_5'('#skF_11', k1_xboole_0), B_2) | ~r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_3824, c_2])).
% 34.77/23.71  tff(c_7252, plain, (![A_15542, B_15543]: (k1_funct_1(A_15542, '#skF_5'(A_15542, B_15543))='#skF_4'(A_15542, B_15543) | r2_hidden('#skF_6'(A_15542, B_15543), B_15543) | k2_relat_1(A_15542)=B_15543 | ~v1_funct_1(A_15542) | ~v1_relat_1(A_15542))), inference(cnfTransformation, [status(thm)], [f_68])).
% 34.77/23.71  tff(c_92093, plain, (![A_154654, B_154655]: (r2_hidden('#skF_4'(A_154654, B_154655), k2_relat_1(A_154654)) | ~r2_hidden('#skF_5'(A_154654, B_154655), k1_relat_1(A_154654)) | ~v1_funct_1(A_154654) | ~v1_relat_1(A_154654) | r2_hidden('#skF_6'(A_154654, B_154655), B_154655) | k2_relat_1(A_154654)=B_154655 | ~v1_funct_1(A_154654) | ~v1_relat_1(A_154654))), inference(superposition, [status(thm), theory('equality')], [c_7252, c_36])).
% 34.77/23.71  tff(c_92158, plain, (r2_hidden('#skF_4'('#skF_11', k1_xboole_0), k2_relat_1('#skF_11')) | r2_hidden('#skF_6'('#skF_11', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_11')=k1_xboole_0 | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11') | ~r1_tarski('#skF_8', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_4453, c_92093])).
% 34.77/23.71  tff(c_92182, plain, (r2_hidden('#skF_4'('#skF_11', k1_xboole_0), k2_relat_1('#skF_11')) | r2_hidden('#skF_6'('#skF_11', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_154, c_3465, c_144, c_84, c_92158])).
% 34.77/23.71  tff(c_92183, plain, (r2_hidden('#skF_4'('#skF_11', k1_xboole_0), k2_relat_1('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_3825, c_674, c_92182])).
% 34.77/23.71  tff(c_93106, plain, (![B_157334]: (r2_hidden('#skF_4'('#skF_11', k1_xboole_0), B_157334) | ~r1_tarski(k2_relat_1('#skF_11'), B_157334))), inference(resolution, [status(thm)], [c_92183, c_2])).
% 34.77/23.71  tff(c_93268, plain, (![A_157632]: (A_157632='#skF_4'('#skF_11', k1_xboole_0) | ~r1_tarski(k2_relat_1('#skF_11'), k1_tarski(A_157632)))), inference(resolution, [status(thm)], [c_93106, c_179])).
% 34.77/23.71  tff(c_93320, plain, (![A_157632]: (A_157632='#skF_4'('#skF_11', k1_xboole_0) | ~v5_relat_1('#skF_11', k1_tarski(A_157632)) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_34, c_93268])).
% 34.77/23.71  tff(c_93337, plain, (![A_157930]: (A_157930='#skF_4'('#skF_11', k1_xboole_0) | ~v5_relat_1('#skF_11', k1_tarski(A_157930)))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_93320])).
% 34.77/23.71  tff(c_93426, plain, ('#skF_4'('#skF_11', k1_xboole_0)='#skF_9'), inference(resolution, [status(thm)], [c_50511, c_93337])).
% 34.77/23.71  tff(c_93264, plain, (![A_13]: (A_13='#skF_4'('#skF_11', k1_xboole_0) | ~r1_tarski(k2_relat_1('#skF_11'), k1_tarski(A_13)))), inference(resolution, [status(thm)], [c_93106, c_179])).
% 34.77/23.71  tff(c_93531, plain, (![A_159421]: (A_159421='#skF_9' | ~r1_tarski(k2_relat_1('#skF_11'), k1_tarski(A_159421)))), inference(demodulation, [status(thm), theory('equality')], [c_93426, c_93264])).
% 34.77/23.71  tff(c_127250, plain, (![A_199093, A_199094]: (A_199093='#skF_9' | A_199094='#skF_1'(k2_relat_1('#skF_11'), k1_tarski(A_199093)) | '#skF_1'(k2_relat_1('#skF_11'), k1_tarski(A_199094))='#skF_9')), inference(resolution, [status(thm)], [c_1342, c_93531])).
% 34.77/23.71  tff(c_129961, plain, (![A_199093]: ('#skF_1'(k2_relat_1('#skF_11'), k1_tarski(A_199093))='#skF_9' | A_199093='#skF_9' | '#skF_1'(k2_relat_1('#skF_11'), k1_tarski('#skF_1'(k2_relat_1('#skF_11'), k1_tarski(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))))='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_127250, c_51374])).
% 34.77/23.71  tff(c_135994, plain, (![A_199093]: ('#skF_1'(k2_relat_1('#skF_11'), k1_tarski(A_199093))='#skF_9' | A_199093='#skF_9' | '#skF_1'(k2_relat_1('#skF_11'), k1_tarski('#skF_9'))='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_51374, c_129961])).
% 34.77/23.71  tff(c_147588, plain, ('#skF_1'(k2_relat_1('#skF_11'), k1_tarski('#skF_9'))='#skF_9'), inference(splitLeft, [status(thm)], [c_135994])).
% 34.77/23.71  tff(c_147704, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9')) | r1_tarski(k2_relat_1('#skF_11'), k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_147588, c_4])).
% 34.77/23.71  tff(c_148138, plain, (r1_tarski(k2_relat_1('#skF_11'), k1_tarski('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_147704])).
% 34.77/23.71  tff(c_432, plain, (![A_145, B_146, B_2, B_147]: (r2_hidden('#skF_1'(A_145, B_146), B_2) | ~r1_tarski(B_147, B_2) | ~r1_tarski(A_145, B_147) | r1_tarski(A_145, B_146))), inference(resolution, [status(thm)], [c_402, c_2])).
% 34.77/23.71  tff(c_148284, plain, (![A_226587, B_226588]: (r2_hidden('#skF_1'(A_226587, B_226588), k1_tarski('#skF_9')) | ~r1_tarski(A_226587, k2_relat_1('#skF_11')) | r1_tarski(A_226587, B_226588))), inference(resolution, [status(thm)], [c_148138, c_432])).
% 34.77/23.71  tff(c_149435, plain, (![B_133]: (r2_hidden(B_133, k1_tarski('#skF_9')) | ~r1_tarski(k1_tarski(B_133), k2_relat_1('#skF_11')) | r1_tarski(k1_tarski(B_133), B_133))), inference(superposition, [status(thm), theory('equality')], [c_331, c_148284])).
% 34.77/23.71  tff(c_149878, plain, (![B_227316]: (r2_hidden(B_227316, k1_tarski('#skF_9')) | ~r1_tarski(k1_tarski(B_227316), k2_relat_1('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_119, c_149435])).
% 34.77/23.71  tff(c_150321, plain, (![A_228770]: (r2_hidden(A_228770, k1_tarski('#skF_9')) | '#skF_1'(k1_tarski(A_228770), k2_relat_1('#skF_11'))=A_228770)), inference(resolution, [status(thm)], [c_253, c_149878])).
% 34.77/23.71  tff(c_157113, plain, (![A_238960]: (~r2_hidden(A_238960, k2_relat_1('#skF_11')) | r1_tarski(k1_tarski(A_238960), k2_relat_1('#skF_11')) | r2_hidden(A_238960, k1_tarski('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_150321, c_4])).
% 34.77/23.71  tff(c_149735, plain, (![B_133]: (r2_hidden(B_133, k1_tarski('#skF_9')) | ~r1_tarski(k1_tarski(B_133), k2_relat_1('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_119, c_149435])).
% 34.77/23.71  tff(c_159257, plain, (![A_239690]: (~r2_hidden(A_239690, k2_relat_1('#skF_11')) | r2_hidden(A_239690, k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_157113, c_149735])).
% 34.77/23.71  tff(c_159394, plain, (![D_57]: (r2_hidden(k1_funct_1('#skF_11', D_57), k1_tarski('#skF_9')) | ~r2_hidden(D_57, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_36, c_159257])).
% 34.77/23.71  tff(c_159448, plain, (![D_240054]: (r2_hidden(k1_funct_1('#skF_11', D_240054), k1_tarski('#skF_9')) | ~r2_hidden(D_240054, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_84, c_3465, c_159394])).
% 34.77/23.71  tff(c_159585, plain, (![D_240418]: (k1_funct_1('#skF_11', D_240418)='#skF_9' | ~r2_hidden(D_240418, '#skF_8'))), inference(resolution, [status(thm)], [c_159448, c_179])).
% 34.77/23.71  tff(c_159727, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9' | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_203, c_159585])).
% 34.77/23.71  tff(c_159787, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_159727])).
% 34.77/23.71  tff(c_159789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_159787])).
% 34.77/23.71  tff(c_159791, plain, ('#skF_1'(k2_relat_1('#skF_11'), k1_tarski('#skF_9'))!='#skF_9'), inference(splitRight, [status(thm)], [c_135994])).
% 34.77/23.71  tff(c_1297, plain, (![B_234]: ('#skF_1'(k2_relat_1('#skF_11'), B_234)='#skF_9' | r1_tarski(k2_relat_1('#skF_11'), B_234))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_1294])).
% 34.77/23.71  tff(c_159843, plain, (![A_13]: (A_13!='#skF_9' | r1_tarski(k2_relat_1('#skF_11'), k1_tarski('#skF_9')) | '#skF_1'(k2_relat_1('#skF_11'), k1_tarski(A_13))='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1342, c_159791])).
% 34.77/23.71  tff(c_160853, plain, (r1_tarski(k2_relat_1('#skF_11'), k1_tarski('#skF_9'))), inference(splitLeft, [status(thm)], [c_159843])).
% 34.77/23.71  tff(c_160969, plain, (![A_241872, B_241873]: (r2_hidden('#skF_1'(A_241872, B_241873), k1_tarski('#skF_9')) | ~r1_tarski(A_241872, k2_relat_1('#skF_11')) | r1_tarski(A_241872, B_241873))), inference(resolution, [status(thm)], [c_160853, c_432])).
% 34.77/23.71  tff(c_162117, plain, (![B_133]: (r2_hidden(B_133, k1_tarski('#skF_9')) | ~r1_tarski(k1_tarski(B_133), k2_relat_1('#skF_11')) | r1_tarski(k1_tarski(B_133), B_133))), inference(superposition, [status(thm), theory('equality')], [c_331, c_160969])).
% 34.77/23.71  tff(c_162562, plain, (![B_242601]: (r2_hidden(B_242601, k1_tarski('#skF_9')) | ~r1_tarski(k1_tarski(B_242601), k2_relat_1('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_119, c_162117])).
% 34.77/23.71  tff(c_163005, plain, (![A_244055]: (r2_hidden(A_244055, k1_tarski('#skF_9')) | '#skF_1'(k1_tarski(A_244055), k2_relat_1('#skF_11'))=A_244055)), inference(resolution, [status(thm)], [c_253, c_162562])).
% 34.77/23.71  tff(c_171745, plain, (![A_254611]: (~r2_hidden(A_254611, k2_relat_1('#skF_11')) | r1_tarski(k1_tarski(A_254611), k2_relat_1('#skF_11')) | r2_hidden(A_254611, k1_tarski('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_163005, c_4])).
% 34.77/23.71  tff(c_162419, plain, (![B_133]: (r2_hidden(B_133, k1_tarski('#skF_9')) | ~r1_tarski(k1_tarski(B_133), k2_relat_1('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_119, c_162117])).
% 34.77/23.71  tff(c_171936, plain, (![A_254975]: (~r2_hidden(A_254975, k2_relat_1('#skF_11')) | r2_hidden(A_254975, k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_171745, c_162419])).
% 34.77/23.71  tff(c_172073, plain, (![D_57]: (r2_hidden(k1_funct_1('#skF_11', D_57), k1_tarski('#skF_9')) | ~r2_hidden(D_57, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_36, c_171936])).
% 34.77/23.71  tff(c_172127, plain, (![D_255339]: (r2_hidden(k1_funct_1('#skF_11', D_255339), k1_tarski('#skF_9')) | ~r2_hidden(D_255339, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_84, c_3465, c_172073])).
% 34.77/23.71  tff(c_172264, plain, (![D_255703]: (k1_funct_1('#skF_11', D_255703)='#skF_9' | ~r2_hidden(D_255703, '#skF_8'))), inference(resolution, [status(thm)], [c_172127, c_179])).
% 34.77/23.71  tff(c_172406, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9' | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_203, c_172264])).
% 34.77/23.71  tff(c_172466, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_172406])).
% 34.77/23.71  tff(c_172468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_172466])).
% 34.77/23.71  tff(c_172470, plain, (~r1_tarski(k2_relat_1('#skF_11'), k1_tarski('#skF_9'))), inference(splitRight, [status(thm)], [c_159843])).
% 34.77/23.71  tff(c_172499, plain, ('#skF_1'(k2_relat_1('#skF_11'), k1_tarski('#skF_9'))='#skF_9'), inference(resolution, [status(thm)], [c_1297, c_172470])).
% 34.77/23.71  tff(c_172527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159791, c_172499])).
% 34.77/23.71  tff(c_172528, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3464])).
% 34.77/23.71  tff(c_172531, plain, (v5_relat_1('#skF_11', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_172528, c_168])).
% 34.77/23.71  tff(c_172535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1482, c_172531])).
% 34.77/23.71  tff(c_172536, plain, (r1_tarski(k2_relat_1('#skF_11'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1421])).
% 34.77/23.71  tff(c_172613, plain, (![B_256433]: (r1_tarski(k2_relat_1('#skF_11'), B_256433))), inference(resolution, [status(thm)], [c_172536, c_482])).
% 34.77/23.71  tff(c_804, plain, (![A_179, D_180]: (r2_hidden(k1_funct_1(A_179, D_180), k2_relat_1(A_179)) | ~r2_hidden(D_180, k1_relat_1(A_179)) | ~v1_funct_1(A_179) | ~v1_relat_1(A_179))), inference(cnfTransformation, [status(thm)], [f_68])).
% 34.77/23.71  tff(c_811, plain, (![A_179, D_180]: (~r1_tarski(k2_relat_1(A_179), k1_funct_1(A_179, D_180)) | ~r2_hidden(D_180, k1_relat_1(A_179)) | ~v1_funct_1(A_179) | ~v1_relat_1(A_179))), inference(resolution, [status(thm)], [c_804, c_54])).
% 34.77/23.71  tff(c_172622, plain, (![D_180]: (~r2_hidden(D_180, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_172613, c_811])).
% 34.77/23.71  tff(c_172668, plain, (![D_256434]: (~r2_hidden(D_256434, k1_relat_1('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_84, c_172622])).
% 34.77/23.71  tff(c_172689, plain, (~r1_tarski('#skF_8', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_203, c_172668])).
% 34.77/23.71  tff(c_172860, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_172857, c_172689])).
% 34.77/23.71  tff(c_172865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_172860])).
% 34.77/23.71  tff(c_172866, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_172856])).
% 34.77/23.71  tff(c_172940, plain, (~r1_tarski(k1_xboole_0, '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_172866, c_119])).
% 34.77/23.71  tff(c_172965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_172940])).
% 34.77/23.71  tff(c_172970, plain, (![B_256446]: (r1_tarski(k2_relat_1('#skF_11'), B_256446))), inference(splitRight, [status(thm)], [c_1340])).
% 34.77/23.71  tff(c_172979, plain, (![D_180]: (~r2_hidden(D_180, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_172970, c_811])).
% 34.77/23.71  tff(c_173061, plain, (![D_256448]: (~r2_hidden(D_256448, k1_relat_1('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_84, c_172979])).
% 34.77/23.71  tff(c_173075, plain, (~r1_tarski('#skF_8', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_203, c_173061])).
% 34.77/23.71  tff(c_173807, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_173803, c_173075])).
% 34.77/23.71  tff(c_173813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_173807])).
% 34.77/23.71  tff(c_173814, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_173802])).
% 34.77/23.71  tff(c_173894, plain, (~r1_tarski(k1_xboole_0, '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_173814, c_119])).
% 34.77/23.71  tff(c_173919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_173894])).
% 34.77/23.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.77/23.71  
% 34.77/23.71  Inference rules
% 34.77/23.71  ----------------------
% 34.77/23.71  #Ref     : 2
% 34.77/23.71  #Sup     : 30362
% 34.77/23.71  #Fact    : 222
% 34.77/23.71  #Define  : 0
% 34.77/23.71  #Split   : 85
% 34.77/23.71  #Chain   : 0
% 34.77/23.71  #Close   : 0
% 34.77/23.71  
% 34.77/23.71  Ordering : KBO
% 34.77/23.71  
% 34.77/23.71  Simplification rules
% 34.77/23.71  ----------------------
% 34.77/23.71  #Subsume      : 11371
% 34.77/23.71  #Demod        : 4097
% 34.77/23.71  #Tautology    : 5353
% 34.77/23.71  #SimpNegUnit  : 1405
% 34.77/23.71  #BackRed      : 153
% 34.77/23.71  
% 34.77/23.71  #Partial instantiations: 162456
% 34.77/23.71  #Strategies tried      : 1
% 34.77/23.71  
% 34.77/23.71  Timing (in seconds)
% 34.77/23.71  ----------------------
% 34.77/23.71  Preprocessing        : 0.35
% 34.77/23.71  Parsing              : 0.18
% 34.77/23.71  CNF conversion       : 0.03
% 34.77/23.71  Main loop            : 22.58
% 34.77/23.72  Inferencing          : 5.01
% 34.77/23.72  Reduction            : 5.95
% 34.77/23.72  Demodulation         : 3.69
% 34.77/23.72  BG Simplification    : 0.44
% 34.77/23.72  Subsumption          : 9.92
% 34.77/23.72  Abstraction          : 0.68
% 34.77/23.72  MUC search           : 0.00
% 34.77/23.72  Cooper               : 0.00
% 34.77/23.72  Total                : 23.00
% 34.77/23.72  Index Insertion      : 0.00
% 34.77/23.72  Index Deletion       : 0.00
% 34.77/23.72  Index Matching       : 0.00
% 34.77/23.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
