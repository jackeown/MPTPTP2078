%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:59 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 177 expanded)
%              Number of leaves         :   41 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  150 ( 399 expanded)
%              Number of equality atoms :   33 (  96 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_78,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_48] : r1_tarski(A_48,A_48) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_286,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_300,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_286])).

tff(c_58,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_304,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_58])).

tff(c_93,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_97,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_93])).

tff(c_62,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_194,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_203,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_194])).

tff(c_1268,plain,(
    ! [B_235,A_236,C_237] :
      ( k1_xboole_0 = B_235
      | k1_relset_1(A_236,B_235,C_237) = A_236
      | ~ v1_funct_2(C_237,A_236,B_235)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_236,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1283,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_1268])).

tff(c_1289,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_203,c_1283])).

tff(c_1290,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1289])).

tff(c_24,plain,(
    ! [A_17] :
      ( k9_relat_1(A_17,k1_relat_1(A_17)) = k2_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1304,plain,
    ( k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1290,c_24])).

tff(c_1314,plain,(
    k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_1304])).

tff(c_450,plain,(
    ! [A_119,B_120,C_121] :
      ( r2_hidden('#skF_2'(A_119,B_120,C_121),B_120)
      | ~ r2_hidden(A_119,k9_relat_1(C_121,B_120))
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_460,plain,(
    ! [A_119,B_120,C_121] :
      ( m1_subset_1('#skF_2'(A_119,B_120,C_121),B_120)
      | ~ r2_hidden(A_119,k9_relat_1(C_121,B_120))
      | ~ v1_relat_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_450,c_10])).

tff(c_1325,plain,(
    ! [A_119] :
      ( m1_subset_1('#skF_2'(A_119,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_119,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1314,c_460])).

tff(c_1333,plain,(
    ! [A_238] :
      ( m1_subset_1('#skF_2'(A_238,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_238,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_1325])).

tff(c_1365,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_304,c_1333])).

tff(c_56,plain,(
    ! [E_39] :
      ( k1_funct_1('#skF_6',E_39) != '#skF_3'
      | ~ m1_subset_1(E_39,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1371,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1365,c_56])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_811,plain,(
    ! [A_191,B_192,C_193] :
      ( r2_hidden(k4_tarski('#skF_2'(A_191,B_192,C_193),A_191),C_193)
      | ~ r2_hidden(A_191,k9_relat_1(C_193,B_192))
      | ~ v1_relat_1(C_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_funct_1(C_20,A_18) = B_19
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2343,plain,(
    ! [C_309,A_310,B_311] :
      ( k1_funct_1(C_309,'#skF_2'(A_310,B_311,C_309)) = A_310
      | ~ v1_funct_1(C_309)
      | ~ r2_hidden(A_310,k9_relat_1(C_309,B_311))
      | ~ v1_relat_1(C_309) ) ),
    inference(resolution,[status(thm)],[c_811,c_28])).

tff(c_2350,plain,(
    ! [A_310] :
      ( k1_funct_1('#skF_6','#skF_2'(A_310,'#skF_4','#skF_6')) = A_310
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(A_310,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1314,c_2343])).

tff(c_2381,plain,(
    ! [A_312] :
      ( k1_funct_1('#skF_6','#skF_2'(A_312,'#skF_4','#skF_6')) = A_312
      | ~ r2_hidden(A_312,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64,c_2350])).

tff(c_2404,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_304,c_2381])).

tff(c_2423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1371,c_2404])).

tff(c_2424,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1289])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_149,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_158,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_149])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_135,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_141,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_3',B_63)
      | ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_63) ) ),
    inference(resolution,[status(thm)],[c_58,c_135])).

tff(c_334,plain,(
    ! [B_100] :
      ( r2_hidden('#skF_3',B_100)
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_141])).

tff(c_342,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3',A_9)
      | ~ v5_relat_1('#skF_6',A_9)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_14,c_334])).

tff(c_355,plain,(
    ! [A_101] :
      ( r2_hidden('#skF_3',A_101)
      | ~ v5_relat_1('#skF_6',A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_342])).

tff(c_363,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_158,c_355])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_379,plain,(
    ! [B_104] :
      ( r2_hidden('#skF_3',B_104)
      | ~ r1_tarski('#skF_5',B_104) ) ),
    inference(resolution,[status(thm)],[c_363,c_2])).

tff(c_32,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_399,plain,(
    ! [B_109] :
      ( ~ r1_tarski(B_109,'#skF_3')
      | ~ r1_tarski('#skF_5',B_109) ) ),
    inference(resolution,[status(thm)],[c_379,c_32])).

tff(c_415,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_399])).

tff(c_2451,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2424,c_415])).

tff(c_2460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_2451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:26:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.82  
% 4.66/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.82  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 4.66/1.82  
% 4.66/1.82  %Foreground sorts:
% 4.66/1.82  
% 4.66/1.82  
% 4.66/1.82  %Background operators:
% 4.66/1.82  
% 4.66/1.82  
% 4.66/1.82  %Foreground operators:
% 4.66/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.66/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.66/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.66/1.82  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.66/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.66/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.66/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.66/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.66/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.66/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.66/1.82  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.66/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.66/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.66/1.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.66/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.66/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.66/1.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.66/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.66/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.66/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.66/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.66/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.66/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.66/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.66/1.82  
% 4.66/1.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.66/1.84  tff(f_126, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 4.66/1.84  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.66/1.84  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.66/1.84  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.66/1.84  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.66/1.84  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 4.66/1.84  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.66/1.84  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.66/1.84  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.66/1.84  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.66/1.84  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.66/1.84  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.66/1.84  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.66/1.84  tff(c_78, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.66/1.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.66/1.84  tff(c_89, plain, (![A_48]: (r1_tarski(A_48, A_48))), inference(resolution, [status(thm)], [c_78, c_4])).
% 4.66/1.84  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.66/1.84  tff(c_286, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.66/1.84  tff(c_300, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_286])).
% 4.66/1.84  tff(c_58, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.66/1.84  tff(c_304, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_300, c_58])).
% 4.66/1.84  tff(c_93, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.66/1.84  tff(c_97, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_93])).
% 4.66/1.84  tff(c_62, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.66/1.84  tff(c_194, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.66/1.84  tff(c_203, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_194])).
% 4.66/1.84  tff(c_1268, plain, (![B_235, A_236, C_237]: (k1_xboole_0=B_235 | k1_relset_1(A_236, B_235, C_237)=A_236 | ~v1_funct_2(C_237, A_236, B_235) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_236, B_235))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.66/1.84  tff(c_1283, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_1268])).
% 4.66/1.84  tff(c_1289, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_203, c_1283])).
% 4.66/1.84  tff(c_1290, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1289])).
% 4.66/1.84  tff(c_24, plain, (![A_17]: (k9_relat_1(A_17, k1_relat_1(A_17))=k2_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.66/1.84  tff(c_1304, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1290, c_24])).
% 4.66/1.84  tff(c_1314, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_1304])).
% 4.66/1.84  tff(c_450, plain, (![A_119, B_120, C_121]: (r2_hidden('#skF_2'(A_119, B_120, C_121), B_120) | ~r2_hidden(A_119, k9_relat_1(C_121, B_120)) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.66/1.84  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.66/1.84  tff(c_460, plain, (![A_119, B_120, C_121]: (m1_subset_1('#skF_2'(A_119, B_120, C_121), B_120) | ~r2_hidden(A_119, k9_relat_1(C_121, B_120)) | ~v1_relat_1(C_121))), inference(resolution, [status(thm)], [c_450, c_10])).
% 4.66/1.84  tff(c_1325, plain, (![A_119]: (m1_subset_1('#skF_2'(A_119, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_119, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1314, c_460])).
% 4.66/1.84  tff(c_1333, plain, (![A_238]: (m1_subset_1('#skF_2'(A_238, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_238, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_1325])).
% 4.66/1.84  tff(c_1365, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_304, c_1333])).
% 4.66/1.84  tff(c_56, plain, (![E_39]: (k1_funct_1('#skF_6', E_39)!='#skF_3' | ~m1_subset_1(E_39, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.66/1.84  tff(c_1371, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))!='#skF_3'), inference(resolution, [status(thm)], [c_1365, c_56])).
% 4.66/1.84  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.66/1.84  tff(c_811, plain, (![A_191, B_192, C_193]: (r2_hidden(k4_tarski('#skF_2'(A_191, B_192, C_193), A_191), C_193) | ~r2_hidden(A_191, k9_relat_1(C_193, B_192)) | ~v1_relat_1(C_193))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.66/1.84  tff(c_28, plain, (![C_20, A_18, B_19]: (k1_funct_1(C_20, A_18)=B_19 | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.66/1.84  tff(c_2343, plain, (![C_309, A_310, B_311]: (k1_funct_1(C_309, '#skF_2'(A_310, B_311, C_309))=A_310 | ~v1_funct_1(C_309) | ~r2_hidden(A_310, k9_relat_1(C_309, B_311)) | ~v1_relat_1(C_309))), inference(resolution, [status(thm)], [c_811, c_28])).
% 4.66/1.84  tff(c_2350, plain, (![A_310]: (k1_funct_1('#skF_6', '#skF_2'(A_310, '#skF_4', '#skF_6'))=A_310 | ~v1_funct_1('#skF_6') | ~r2_hidden(A_310, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1314, c_2343])).
% 4.66/1.84  tff(c_2381, plain, (![A_312]: (k1_funct_1('#skF_6', '#skF_2'(A_312, '#skF_4', '#skF_6'))=A_312 | ~r2_hidden(A_312, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64, c_2350])).
% 4.66/1.84  tff(c_2404, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3'), inference(resolution, [status(thm)], [c_304, c_2381])).
% 4.66/1.84  tff(c_2423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1371, c_2404])).
% 4.66/1.84  tff(c_2424, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1289])).
% 4.66/1.84  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.66/1.84  tff(c_149, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.66/1.84  tff(c_158, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_149])).
% 4.66/1.84  tff(c_14, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.66/1.84  tff(c_135, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.66/1.84  tff(c_141, plain, (![B_63]: (r2_hidden('#skF_3', B_63) | ~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_63))), inference(resolution, [status(thm)], [c_58, c_135])).
% 4.66/1.84  tff(c_334, plain, (![B_100]: (r2_hidden('#skF_3', B_100) | ~r1_tarski(k2_relat_1('#skF_6'), B_100))), inference(demodulation, [status(thm), theory('equality')], [c_300, c_141])).
% 4.66/1.84  tff(c_342, plain, (![A_9]: (r2_hidden('#skF_3', A_9) | ~v5_relat_1('#skF_6', A_9) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_14, c_334])).
% 4.66/1.84  tff(c_355, plain, (![A_101]: (r2_hidden('#skF_3', A_101) | ~v5_relat_1('#skF_6', A_101))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_342])).
% 4.66/1.84  tff(c_363, plain, (r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_158, c_355])).
% 4.66/1.84  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.66/1.84  tff(c_379, plain, (![B_104]: (r2_hidden('#skF_3', B_104) | ~r1_tarski('#skF_5', B_104))), inference(resolution, [status(thm)], [c_363, c_2])).
% 4.66/1.84  tff(c_32, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.66/1.84  tff(c_399, plain, (![B_109]: (~r1_tarski(B_109, '#skF_3') | ~r1_tarski('#skF_5', B_109))), inference(resolution, [status(thm)], [c_379, c_32])).
% 4.66/1.84  tff(c_415, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_399])).
% 4.66/1.84  tff(c_2451, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2424, c_415])).
% 4.66/1.84  tff(c_2460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_2451])).
% 4.66/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.84  
% 4.66/1.84  Inference rules
% 4.66/1.84  ----------------------
% 4.66/1.84  #Ref     : 0
% 4.66/1.84  #Sup     : 508
% 4.66/1.84  #Fact    : 0
% 4.66/1.84  #Define  : 0
% 4.66/1.84  #Split   : 7
% 4.66/1.84  #Chain   : 0
% 4.66/1.84  #Close   : 0
% 4.66/1.84  
% 4.66/1.84  Ordering : KBO
% 4.66/1.84  
% 4.66/1.84  Simplification rules
% 4.66/1.84  ----------------------
% 4.66/1.84  #Subsume      : 141
% 4.66/1.84  #Demod        : 113
% 4.66/1.84  #Tautology    : 36
% 4.66/1.84  #SimpNegUnit  : 3
% 4.66/1.84  #BackRed      : 38
% 4.66/1.84  
% 4.66/1.84  #Partial instantiations: 0
% 4.66/1.84  #Strategies tried      : 1
% 4.66/1.84  
% 4.66/1.84  Timing (in seconds)
% 4.66/1.84  ----------------------
% 4.66/1.85  Preprocessing        : 0.34
% 4.66/1.85  Parsing              : 0.18
% 4.81/1.85  CNF conversion       : 0.02
% 4.81/1.85  Main loop            : 0.72
% 4.81/1.85  Inferencing          : 0.25
% 4.81/1.85  Reduction            : 0.21
% 4.81/1.85  Demodulation         : 0.13
% 4.81/1.85  BG Simplification    : 0.03
% 4.81/1.85  Subsumption          : 0.16
% 4.81/1.85  Abstraction          : 0.04
% 4.81/1.85  MUC search           : 0.00
% 4.81/1.85  Cooper               : 0.00
% 4.81/1.85  Total                : 1.10
% 4.81/1.85  Index Insertion      : 0.00
% 4.81/1.85  Index Deletion       : 0.00
% 4.81/1.85  Index Matching       : 0.00
% 4.81/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
