%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:39 EST 2020

% Result     : Theorem 7.50s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 736 expanded)
%              Number of leaves         :   40 ( 245 expanded)
%              Depth                    :   14
%              Number of atoms          :  337 (1893 expanded)
%              Number of equality atoms :   33 ( 203 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_139,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_88,plain,(
    r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_713,plain,(
    ! [A_247,B_248,D_249] :
      ( '#skF_5'(A_247,B_248,k1_funct_2(A_247,B_248),D_249) = D_249
      | ~ r2_hidden(D_249,k1_funct_2(A_247,B_248)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_720,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_88,c_713])).

tff(c_743,plain,(
    ! [A_254,B_255,D_256] :
      ( v1_relat_1('#skF_5'(A_254,B_255,k1_funct_2(A_254,B_255),D_256))
      | ~ r2_hidden(D_256,k1_funct_2(A_254,B_255)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_746,plain,
    ( v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_743])).

tff(c_748,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_746])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_918,plain,(
    ! [A_294,B_295,D_296] :
      ( k1_relat_1('#skF_5'(A_294,B_295,k1_funct_2(A_294,B_295),D_296)) = A_294
      | ~ r2_hidden(D_296,k1_funct_2(A_294,B_295)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_953,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_918])).

tff(c_957,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_953])).

tff(c_1419,plain,(
    ! [A_334,B_335,D_336] :
      ( r1_tarski(k2_relat_1('#skF_5'(A_334,B_335,k1_funct_2(A_334,B_335),D_336)),B_335)
      | ~ r2_hidden(D_336,k1_funct_2(A_334,B_335)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1449,plain,
    ( r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_1419])).

tff(c_1460,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1449])).

tff(c_1604,plain,(
    ! [C_349,A_350,B_351] :
      ( m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_350,B_351)))
      | ~ r1_tarski(k2_relat_1(C_349),B_351)
      | ~ r1_tarski(k1_relat_1(C_349),A_350)
      | ~ v1_relat_1(C_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_86,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_123,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_456,plain,(
    ! [A_174,B_175,D_176] :
      ( '#skF_5'(A_174,B_175,k1_funct_2(A_174,B_175),D_176) = D_176
      | ~ r2_hidden(D_176,k1_funct_2(A_174,B_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_467,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_88,c_456])).

tff(c_52,plain,(
    ! [A_39,B_40,D_55] :
      ( v1_funct_1('#skF_5'(A_39,B_40,k1_funct_2(A_39,B_40),D_55))
      | ~ r2_hidden(D_55,k1_funct_2(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_474,plain,
    ( v1_funct_1('#skF_8')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_52])).

tff(c_480,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_474])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_480])).

tff(c_483,plain,
    ( ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_489,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_483])).

tff(c_1616,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
    | ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1604,c_489])).

tff(c_1626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_12,c_957,c_1460,c_1616])).

tff(c_1627,plain,(
    ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_484,plain,(
    v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_1628,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_1748,plain,(
    ! [C_370,A_371,B_372] :
      ( v4_relat_1(C_370,A_371)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(A_371,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1756,plain,(
    v4_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_1628,c_1748])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_485,plain,(
    ! [C_177,B_178,A_179] :
      ( ~ v1_xboole_0(C_177)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(C_177))
      | ~ r2_hidden(A_179,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1643,plain,(
    ! [B_352,A_353,A_354] :
      ( ~ v1_xboole_0(B_352)
      | ~ r2_hidden(A_353,A_354)
      | ~ r1_tarski(A_354,B_352) ) ),
    inference(resolution,[status(thm)],[c_18,c_485])).

tff(c_1687,plain,(
    ! [B_361,A_362,B_363] :
      ( ~ v1_xboole_0(B_361)
      | ~ r1_tarski(A_362,B_361)
      | r1_tarski(A_362,B_363) ) ),
    inference(resolution,[status(thm)],[c_6,c_1643])).

tff(c_1700,plain,(
    ! [B_364,B_365] :
      ( ~ v1_xboole_0(B_364)
      | r1_tarski(B_364,B_365) ) ),
    inference(resolution,[status(thm)],[c_12,c_1687])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1725,plain,(
    ! [B_367,B_366] :
      ( B_367 = B_366
      | ~ r1_tarski(B_366,B_367)
      | ~ v1_xboole_0(B_367) ) ),
    inference(resolution,[status(thm)],[c_1700,c_8])).

tff(c_1900,plain,(
    ! [B_410,A_411] :
      ( k1_relat_1(B_410) = A_411
      | ~ v1_xboole_0(A_411)
      | ~ v4_relat_1(B_410,A_411)
      | ~ v1_relat_1(B_410) ) ),
    inference(resolution,[status(thm)],[c_24,c_1725])).

tff(c_1925,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1756,c_1900])).

tff(c_1926,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1925])).

tff(c_2206,plain,(
    ! [A_468,B_469,D_470] :
      ( '#skF_5'(A_468,B_469,k1_funct_2(A_468,B_469),D_470) = D_470
      | ~ r2_hidden(D_470,k1_funct_2(A_468,B_469)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2217,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_88,c_2206])).

tff(c_54,plain,(
    ! [A_39,B_40,D_55] :
      ( v1_relat_1('#skF_5'(A_39,B_40,k1_funct_2(A_39,B_40),D_55))
      | ~ r2_hidden(D_55,k1_funct_2(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2224,plain,
    ( v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2217,c_54])).

tff(c_2230,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2224])).

tff(c_2232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1926,c_2230])).

tff(c_2233,plain,
    ( ~ v1_xboole_0('#skF_6')
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1925])).

tff(c_2235,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2233])).

tff(c_2234,plain,(
    v1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1925])).

tff(c_5523,plain,(
    ! [A_782,B_783,D_784] :
      ( '#skF_5'(A_782,B_783,k1_funct_2(A_782,B_783),D_784) = D_784
      | ~ r2_hidden(D_784,k1_funct_2(A_782,B_783)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_5534,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_88,c_5523])).

tff(c_5853,plain,(
    ! [A_841,B_842,D_843] :
      ( k1_relat_1('#skF_5'(A_841,B_842,k1_funct_2(A_841,B_842),D_843)) = A_841
      | ~ r2_hidden(D_843,k1_funct_2(A_841,B_842)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_5920,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5534,c_5853])).

tff(c_5924,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5920])).

tff(c_4717,plain,(
    ! [C_703,A_704,B_705] :
      ( v1_funct_2(C_703,A_704,B_705)
      | ~ v1_partfun1(C_703,A_704)
      | ~ v1_funct_1(C_703)
      | ~ m1_subset_1(C_703,k1_zfmisc_1(k2_zfmisc_1(A_704,B_705))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4726,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1628,c_4717])).

tff(c_4737,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_4726])).

tff(c_4738,plain,(
    ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1627,c_4737])).

tff(c_4150,plain,(
    ! [A_661,B_662,D_663] :
      ( '#skF_5'(A_661,B_662,k1_funct_2(A_661,B_662),D_663) = D_663
      | ~ r2_hidden(D_663,k1_funct_2(A_661,B_662)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4161,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_88,c_4150])).

tff(c_4203,plain,(
    ! [A_671,B_672,D_673] :
      ( k1_relat_1('#skF_5'(A_671,B_672,k1_funct_2(A_671,B_672),D_673)) = A_671
      | ~ r2_hidden(D_673,k1_funct_2(A_671,B_672)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4238,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4161,c_4203])).

tff(c_4242,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_4238])).

tff(c_82,plain,(
    ! [A_59] :
      ( v1_funct_2(A_59,k1_relat_1(A_59),k2_relat_1(A_59))
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4260,plain,
    ( v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4242,c_82])).

tff(c_4283,plain,(
    v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_484,c_4260])).

tff(c_80,plain,(
    ! [A_59] :
      ( m1_subset_1(A_59,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_59),k2_relat_1(A_59))))
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4257,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8'))))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4242,c_80])).

tff(c_4281,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_484,c_4257])).

tff(c_3183,plain,(
    ! [C_570,A_571,B_572] :
      ( v1_funct_2(C_570,A_571,B_572)
      | ~ v1_partfun1(C_570,A_571)
      | ~ v1_funct_1(C_570)
      | ~ m1_subset_1(C_570,k1_zfmisc_1(k2_zfmisc_1(A_571,B_572))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3192,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1628,c_3183])).

tff(c_3203,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_3192])).

tff(c_3204,plain,(
    ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1627,c_3203])).

tff(c_2515,plain,(
    ! [A_524,B_525,D_526] :
      ( '#skF_5'(A_524,B_525,k1_funct_2(A_524,B_525),D_526) = D_526
      | ~ r2_hidden(D_526,k1_funct_2(A_524,B_525)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2526,plain,(
    '#skF_5'('#skF_6','#skF_7',k1_funct_2('#skF_6','#skF_7'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_88,c_2515])).

tff(c_2550,plain,(
    ! [A_532,B_533,D_534] :
      ( k1_relat_1('#skF_5'(A_532,B_533,k1_funct_2(A_532,B_533),D_534)) = A_532
      | ~ r2_hidden(D_534,k1_funct_2(A_532,B_533)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2585,plain,
    ( k1_relat_1('#skF_8') = '#skF_6'
    | ~ r2_hidden('#skF_8',k1_funct_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2526,c_2550])).

tff(c_2589,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2585])).

tff(c_2607,plain,
    ( v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2589,c_82])).

tff(c_2630,plain,(
    v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_484,c_2607])).

tff(c_2604,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8'))))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2589,c_80])).

tff(c_2628,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_484,c_2604])).

tff(c_1699,plain,(
    ! [B_7,B_363] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_363) ) ),
    inference(resolution,[status(thm)],[c_12,c_1687])).

tff(c_1779,plain,(
    ! [A_376,A_377,B_378] :
      ( v4_relat_1(A_376,A_377)
      | ~ r1_tarski(A_376,k2_zfmisc_1(A_377,B_378)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1748])).

tff(c_1798,plain,(
    ! [B_7,A_377] :
      ( v4_relat_1(B_7,A_377)
      | ~ v1_xboole_0(B_7) ) ),
    inference(resolution,[status(thm)],[c_1699,c_1779])).

tff(c_2462,plain,(
    ! [A_512,B_513,B_514] :
      ( ~ v1_xboole_0(A_512)
      | r1_tarski(k1_relat_1(B_513),B_514)
      | ~ v4_relat_1(B_513,A_512)
      | ~ v1_relat_1(B_513) ) ),
    inference(resolution,[status(thm)],[c_24,c_1687])).

tff(c_2480,plain,(
    ! [A_377,B_7,B_514] :
      ( ~ v1_xboole_0(A_377)
      | r1_tarski(k1_relat_1(B_7),B_514)
      | ~ v1_relat_1(B_7)
      | ~ v1_xboole_0(B_7) ) ),
    inference(resolution,[status(thm)],[c_1798,c_2462])).

tff(c_2486,plain,(
    ! [A_377] : ~ v1_xboole_0(A_377) ),
    inference(splitLeft,[status(thm)],[c_2480])).

tff(c_40,plain,(
    ! [C_38,A_35,B_36] :
      ( v1_partfun1(C_38,A_35)
      | ~ v1_funct_2(C_38,A_35,B_36)
      | ~ v1_funct_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | v1_xboole_0(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4052,plain,(
    ! [C_647,A_648,B_649] :
      ( v1_partfun1(C_647,A_648)
      | ~ v1_funct_2(C_647,A_648,B_649)
      | ~ v1_funct_1(C_647)
      | ~ m1_subset_1(C_647,k1_zfmisc_1(k2_zfmisc_1(A_648,B_649))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2486,c_40])).

tff(c_4058,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_2628,c_4052])).

tff(c_4072,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_2630,c_4058])).

tff(c_4074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3204,c_4072])).

tff(c_4076,plain,(
    ! [B_650,B_651] :
      ( r1_tarski(k1_relat_1(B_650),B_651)
      | ~ v1_relat_1(B_650)
      | ~ v1_xboole_0(B_650) ) ),
    inference(splitRight,[status(thm)],[c_2480])).

tff(c_1823,plain,(
    ! [C_389,B_390,A_391] :
      ( v1_xboole_0(C_389)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(B_390,A_391)))
      | ~ v1_xboole_0(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1832,plain,(
    ! [A_11,A_391,B_390] :
      ( v1_xboole_0(A_11)
      | ~ v1_xboole_0(A_391)
      | ~ r1_tarski(A_11,k2_zfmisc_1(B_390,A_391)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1823])).

tff(c_4112,plain,(
    ! [B_650,A_391] :
      ( v1_xboole_0(k1_relat_1(B_650))
      | ~ v1_xboole_0(A_391)
      | ~ v1_relat_1(B_650)
      | ~ v1_xboole_0(B_650) ) ),
    inference(resolution,[status(thm)],[c_4076,c_1832])).

tff(c_4120,plain,(
    ! [A_391] : ~ v1_xboole_0(A_391) ),
    inference(splitLeft,[status(thm)],[c_4112])).

tff(c_5434,plain,(
    ! [C_766,A_767,B_768] :
      ( v1_partfun1(C_766,A_767)
      | ~ v1_funct_2(C_766,A_767,B_768)
      | ~ v1_funct_1(C_766)
      | ~ m1_subset_1(C_766,k1_zfmisc_1(k2_zfmisc_1(A_767,B_768))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4120,c_40])).

tff(c_5440,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4281,c_5434])).

tff(c_5454,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_4283,c_5440])).

tff(c_5456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4738,c_5454])).

tff(c_5457,plain,(
    ! [B_650] :
      ( v1_xboole_0(k1_relat_1(B_650))
      | ~ v1_relat_1(B_650)
      | ~ v1_xboole_0(B_650) ) ),
    inference(splitRight,[status(thm)],[c_4112])).

tff(c_5951,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5924,c_5457])).

tff(c_6005,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_5951])).

tff(c_6006,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2235,c_6005])).

tff(c_2347,plain,(
    ! [A_502] :
      ( m1_subset_1(A_502,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_502),k2_relat_1(A_502))))
      | ~ v1_funct_1(A_502)
      | ~ v1_relat_1(A_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2370,plain,(
    ! [A_502] :
      ( r1_tarski(A_502,k2_zfmisc_1(k1_relat_1(A_502),k2_relat_1(A_502)))
      | ~ v1_funct_1(A_502)
      | ~ v1_relat_1(A_502) ) ),
    inference(resolution,[status(thm)],[c_2347,c_16])).

tff(c_5957,plain,
    ( r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5924,c_2370])).

tff(c_6010,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_484,c_5957])).

tff(c_6039,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6010,c_1832])).

tff(c_6061,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_6006,c_6039])).

tff(c_6284,plain,(
    ! [C_855,A_856,B_857] :
      ( v1_funct_2(C_855,A_856,B_857)
      | ~ v1_partfun1(C_855,A_856)
      | ~ v1_funct_1(C_855)
      | ~ m1_subset_1(C_855,k1_zfmisc_1(k2_zfmisc_1(A_856,B_857))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6293,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1628,c_6284])).

tff(c_6304,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_6293])).

tff(c_6305,plain,(
    ~ v1_partfun1('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1627,c_6304])).

tff(c_5972,plain,
    ( v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5924,c_82])).

tff(c_6020,plain,(
    v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_484,c_5972])).

tff(c_5963,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8'))))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5924,c_80])).

tff(c_6014,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_484,c_5963])).

tff(c_7366,plain,(
    ! [C_916,A_917,B_918] :
      ( v1_partfun1(C_916,A_917)
      | ~ v1_funct_2(C_916,A_917,B_918)
      | ~ v1_funct_1(C_916)
      | ~ m1_subset_1(C_916,k1_zfmisc_1(k2_zfmisc_1(A_917,B_918)))
      | v1_xboole_0(B_918) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_7372,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_2('#skF_8','#skF_6',k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6014,c_7366])).

tff(c_7386,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_6020,c_7372])).

tff(c_7388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6061,c_6305,c_7386])).

tff(c_7390,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2233])).

tff(c_7468,plain,(
    ! [C_925,A_926,B_927] :
      ( v1_partfun1(C_925,A_926)
      | ~ m1_subset_1(C_925,k1_zfmisc_1(k2_zfmisc_1(A_926,B_927)))
      | ~ v1_xboole_0(A_926) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_7471,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1628,c_7468])).

tff(c_7478,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7390,c_7471])).

tff(c_8489,plain,(
    ! [C_1009,A_1010,B_1011] :
      ( v1_funct_2(C_1009,A_1010,B_1011)
      | ~ v1_partfun1(C_1009,A_1010)
      | ~ v1_funct_1(C_1009)
      | ~ m1_subset_1(C_1009,k1_zfmisc_1(k2_zfmisc_1(A_1010,B_1011))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8504,plain,
    ( v1_funct_2('#skF_8','#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1628,c_8489])).

tff(c_8515,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_7478,c_8504])).

tff(c_8517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1627,c_8515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:32:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.50/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.70  
% 7.50/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 7.50/2.71  
% 7.50/2.71  %Foreground sorts:
% 7.50/2.71  
% 7.50/2.71  
% 7.50/2.71  %Background operators:
% 7.50/2.71  
% 7.50/2.71  
% 7.50/2.71  %Foreground operators:
% 7.50/2.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.50/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.50/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.50/2.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.50/2.71  tff('#skF_7', type, '#skF_7': $i).
% 7.50/2.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.50/2.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.50/2.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.50/2.71  tff('#skF_6', type, '#skF_6': $i).
% 7.50/2.71  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.50/2.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.50/2.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.50/2.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.50/2.71  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 7.50/2.71  tff('#skF_8', type, '#skF_8': $i).
% 7.50/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.50/2.71  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 7.50/2.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.50/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.50/2.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.50/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.50/2.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.50/2.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.50/2.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.50/2.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.50/2.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.50/2.71  
% 7.67/2.73  tff(f_148, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 7.67/2.73  tff(f_129, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 7.67/2.73  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.67/2.73  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.67/2.73  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.67/2.73  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.67/2.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.67/2.73  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.67/2.73  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.67/2.73  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 7.67/2.73  tff(f_139, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.67/2.73  tff(f_113, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.67/2.73  tff(f_74, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.67/2.73  tff(f_99, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 7.67/2.73  tff(c_88, plain, (r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.67/2.73  tff(c_713, plain, (![A_247, B_248, D_249]: ('#skF_5'(A_247, B_248, k1_funct_2(A_247, B_248), D_249)=D_249 | ~r2_hidden(D_249, k1_funct_2(A_247, B_248)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_720, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_88, c_713])).
% 7.67/2.73  tff(c_743, plain, (![A_254, B_255, D_256]: (v1_relat_1('#skF_5'(A_254, B_255, k1_funct_2(A_254, B_255), D_256)) | ~r2_hidden(D_256, k1_funct_2(A_254, B_255)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_746, plain, (v1_relat_1('#skF_8') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_720, c_743])).
% 7.67/2.73  tff(c_748, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_746])).
% 7.67/2.73  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.67/2.73  tff(c_918, plain, (![A_294, B_295, D_296]: (k1_relat_1('#skF_5'(A_294, B_295, k1_funct_2(A_294, B_295), D_296))=A_294 | ~r2_hidden(D_296, k1_funct_2(A_294, B_295)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_953, plain, (k1_relat_1('#skF_8')='#skF_6' | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_720, c_918])).
% 7.67/2.73  tff(c_957, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_953])).
% 7.67/2.73  tff(c_1419, plain, (![A_334, B_335, D_336]: (r1_tarski(k2_relat_1('#skF_5'(A_334, B_335, k1_funct_2(A_334, B_335), D_336)), B_335) | ~r2_hidden(D_336, k1_funct_2(A_334, B_335)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_1449, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_720, c_1419])).
% 7.67/2.73  tff(c_1460, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1449])).
% 7.67/2.73  tff(c_1604, plain, (![C_349, A_350, B_351]: (m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_350, B_351))) | ~r1_tarski(k2_relat_1(C_349), B_351) | ~r1_tarski(k1_relat_1(C_349), A_350) | ~v1_relat_1(C_349))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.67/2.73  tff(c_86, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.67/2.73  tff(c_123, plain, (~v1_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_86])).
% 7.67/2.73  tff(c_456, plain, (![A_174, B_175, D_176]: ('#skF_5'(A_174, B_175, k1_funct_2(A_174, B_175), D_176)=D_176 | ~r2_hidden(D_176, k1_funct_2(A_174, B_175)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_467, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_88, c_456])).
% 7.67/2.73  tff(c_52, plain, (![A_39, B_40, D_55]: (v1_funct_1('#skF_5'(A_39, B_40, k1_funct_2(A_39, B_40), D_55)) | ~r2_hidden(D_55, k1_funct_2(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_474, plain, (v1_funct_1('#skF_8') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_467, c_52])).
% 7.67/2.73  tff(c_480, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_474])).
% 7.67/2.73  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_480])).
% 7.67/2.73  tff(c_483, plain, (~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(splitRight, [status(thm)], [c_86])).
% 7.67/2.73  tff(c_489, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(splitLeft, [status(thm)], [c_483])).
% 7.67/2.73  tff(c_1616, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | ~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1604, c_489])).
% 7.67/2.73  tff(c_1626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_748, c_12, c_957, c_1460, c_1616])).
% 7.67/2.73  tff(c_1627, plain, (~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_483])).
% 7.67/2.73  tff(c_484, plain, (v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_86])).
% 7.67/2.73  tff(c_1628, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(splitRight, [status(thm)], [c_483])).
% 7.67/2.73  tff(c_1748, plain, (![C_370, A_371, B_372]: (v4_relat_1(C_370, A_371) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(A_371, B_372))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.67/2.73  tff(c_1756, plain, (v4_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_1628, c_1748])).
% 7.67/2.73  tff(c_24, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.67/2.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.67/2.73  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.67/2.73  tff(c_485, plain, (![C_177, B_178, A_179]: (~v1_xboole_0(C_177) | ~m1_subset_1(B_178, k1_zfmisc_1(C_177)) | ~r2_hidden(A_179, B_178))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.67/2.73  tff(c_1643, plain, (![B_352, A_353, A_354]: (~v1_xboole_0(B_352) | ~r2_hidden(A_353, A_354) | ~r1_tarski(A_354, B_352))), inference(resolution, [status(thm)], [c_18, c_485])).
% 7.67/2.73  tff(c_1687, plain, (![B_361, A_362, B_363]: (~v1_xboole_0(B_361) | ~r1_tarski(A_362, B_361) | r1_tarski(A_362, B_363))), inference(resolution, [status(thm)], [c_6, c_1643])).
% 7.67/2.73  tff(c_1700, plain, (![B_364, B_365]: (~v1_xboole_0(B_364) | r1_tarski(B_364, B_365))), inference(resolution, [status(thm)], [c_12, c_1687])).
% 7.67/2.73  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.67/2.73  tff(c_1725, plain, (![B_367, B_366]: (B_367=B_366 | ~r1_tarski(B_366, B_367) | ~v1_xboole_0(B_367))), inference(resolution, [status(thm)], [c_1700, c_8])).
% 7.67/2.73  tff(c_1900, plain, (![B_410, A_411]: (k1_relat_1(B_410)=A_411 | ~v1_xboole_0(A_411) | ~v4_relat_1(B_410, A_411) | ~v1_relat_1(B_410))), inference(resolution, [status(thm)], [c_24, c_1725])).
% 7.67/2.73  tff(c_1925, plain, (k1_relat_1('#skF_8')='#skF_6' | ~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1756, c_1900])).
% 7.67/2.73  tff(c_1926, plain, (~v1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1925])).
% 7.67/2.73  tff(c_2206, plain, (![A_468, B_469, D_470]: ('#skF_5'(A_468, B_469, k1_funct_2(A_468, B_469), D_470)=D_470 | ~r2_hidden(D_470, k1_funct_2(A_468, B_469)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_2217, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_88, c_2206])).
% 7.67/2.73  tff(c_54, plain, (![A_39, B_40, D_55]: (v1_relat_1('#skF_5'(A_39, B_40, k1_funct_2(A_39, B_40), D_55)) | ~r2_hidden(D_55, k1_funct_2(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_2224, plain, (v1_relat_1('#skF_8') | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2217, c_54])).
% 7.67/2.73  tff(c_2230, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2224])).
% 7.67/2.73  tff(c_2232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1926, c_2230])).
% 7.67/2.73  tff(c_2233, plain, (~v1_xboole_0('#skF_6') | k1_relat_1('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_1925])).
% 7.67/2.73  tff(c_2235, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_2233])).
% 7.67/2.73  tff(c_2234, plain, (v1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_1925])).
% 7.67/2.73  tff(c_5523, plain, (![A_782, B_783, D_784]: ('#skF_5'(A_782, B_783, k1_funct_2(A_782, B_783), D_784)=D_784 | ~r2_hidden(D_784, k1_funct_2(A_782, B_783)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_5534, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_88, c_5523])).
% 7.67/2.73  tff(c_5853, plain, (![A_841, B_842, D_843]: (k1_relat_1('#skF_5'(A_841, B_842, k1_funct_2(A_841, B_842), D_843))=A_841 | ~r2_hidden(D_843, k1_funct_2(A_841, B_842)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_5920, plain, (k1_relat_1('#skF_8')='#skF_6' | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5534, c_5853])).
% 7.67/2.73  tff(c_5924, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5920])).
% 7.67/2.73  tff(c_4717, plain, (![C_703, A_704, B_705]: (v1_funct_2(C_703, A_704, B_705) | ~v1_partfun1(C_703, A_704) | ~v1_funct_1(C_703) | ~m1_subset_1(C_703, k1_zfmisc_1(k2_zfmisc_1(A_704, B_705))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.67/2.73  tff(c_4726, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1628, c_4717])).
% 7.67/2.73  tff(c_4737, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_4726])).
% 7.67/2.73  tff(c_4738, plain, (~v1_partfun1('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1627, c_4737])).
% 7.67/2.73  tff(c_4150, plain, (![A_661, B_662, D_663]: ('#skF_5'(A_661, B_662, k1_funct_2(A_661, B_662), D_663)=D_663 | ~r2_hidden(D_663, k1_funct_2(A_661, B_662)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_4161, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_88, c_4150])).
% 7.67/2.73  tff(c_4203, plain, (![A_671, B_672, D_673]: (k1_relat_1('#skF_5'(A_671, B_672, k1_funct_2(A_671, B_672), D_673))=A_671 | ~r2_hidden(D_673, k1_funct_2(A_671, B_672)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_4238, plain, (k1_relat_1('#skF_8')='#skF_6' | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_4161, c_4203])).
% 7.67/2.73  tff(c_4242, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_4238])).
% 7.67/2.73  tff(c_82, plain, (![A_59]: (v1_funct_2(A_59, k1_relat_1(A_59), k2_relat_1(A_59)) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.67/2.73  tff(c_4260, plain, (v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4242, c_82])).
% 7.67/2.73  tff(c_4283, plain, (v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_484, c_4260])).
% 7.67/2.73  tff(c_80, plain, (![A_59]: (m1_subset_1(A_59, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_59), k2_relat_1(A_59)))) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.67/2.73  tff(c_4257, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4242, c_80])).
% 7.67/2.73  tff(c_4281, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_484, c_4257])).
% 7.67/2.73  tff(c_3183, plain, (![C_570, A_571, B_572]: (v1_funct_2(C_570, A_571, B_572) | ~v1_partfun1(C_570, A_571) | ~v1_funct_1(C_570) | ~m1_subset_1(C_570, k1_zfmisc_1(k2_zfmisc_1(A_571, B_572))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.67/2.73  tff(c_3192, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1628, c_3183])).
% 7.67/2.73  tff(c_3203, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_3192])).
% 7.67/2.73  tff(c_3204, plain, (~v1_partfun1('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1627, c_3203])).
% 7.67/2.73  tff(c_2515, plain, (![A_524, B_525, D_526]: ('#skF_5'(A_524, B_525, k1_funct_2(A_524, B_525), D_526)=D_526 | ~r2_hidden(D_526, k1_funct_2(A_524, B_525)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_2526, plain, ('#skF_5'('#skF_6', '#skF_7', k1_funct_2('#skF_6', '#skF_7'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_88, c_2515])).
% 7.67/2.73  tff(c_2550, plain, (![A_532, B_533, D_534]: (k1_relat_1('#skF_5'(A_532, B_533, k1_funct_2(A_532, B_533), D_534))=A_532 | ~r2_hidden(D_534, k1_funct_2(A_532, B_533)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.73  tff(c_2585, plain, (k1_relat_1('#skF_8')='#skF_6' | ~r2_hidden('#skF_8', k1_funct_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2526, c_2550])).
% 7.67/2.73  tff(c_2589, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2585])).
% 7.67/2.73  tff(c_2607, plain, (v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2589, c_82])).
% 7.67/2.73  tff(c_2630, plain, (v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_484, c_2607])).
% 7.67/2.73  tff(c_2604, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2589, c_80])).
% 7.67/2.73  tff(c_2628, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_484, c_2604])).
% 7.67/2.73  tff(c_1699, plain, (![B_7, B_363]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_363))), inference(resolution, [status(thm)], [c_12, c_1687])).
% 7.67/2.73  tff(c_1779, plain, (![A_376, A_377, B_378]: (v4_relat_1(A_376, A_377) | ~r1_tarski(A_376, k2_zfmisc_1(A_377, B_378)))), inference(resolution, [status(thm)], [c_18, c_1748])).
% 7.67/2.73  tff(c_1798, plain, (![B_7, A_377]: (v4_relat_1(B_7, A_377) | ~v1_xboole_0(B_7))), inference(resolution, [status(thm)], [c_1699, c_1779])).
% 7.67/2.73  tff(c_2462, plain, (![A_512, B_513, B_514]: (~v1_xboole_0(A_512) | r1_tarski(k1_relat_1(B_513), B_514) | ~v4_relat_1(B_513, A_512) | ~v1_relat_1(B_513))), inference(resolution, [status(thm)], [c_24, c_1687])).
% 7.67/2.73  tff(c_2480, plain, (![A_377, B_7, B_514]: (~v1_xboole_0(A_377) | r1_tarski(k1_relat_1(B_7), B_514) | ~v1_relat_1(B_7) | ~v1_xboole_0(B_7))), inference(resolution, [status(thm)], [c_1798, c_2462])).
% 7.67/2.73  tff(c_2486, plain, (![A_377]: (~v1_xboole_0(A_377))), inference(splitLeft, [status(thm)], [c_2480])).
% 7.67/2.73  tff(c_40, plain, (![C_38, A_35, B_36]: (v1_partfun1(C_38, A_35) | ~v1_funct_2(C_38, A_35, B_36) | ~v1_funct_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | v1_xboole_0(B_36))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.67/2.73  tff(c_4052, plain, (![C_647, A_648, B_649]: (v1_partfun1(C_647, A_648) | ~v1_funct_2(C_647, A_648, B_649) | ~v1_funct_1(C_647) | ~m1_subset_1(C_647, k1_zfmisc_1(k2_zfmisc_1(A_648, B_649))))), inference(negUnitSimplification, [status(thm)], [c_2486, c_40])).
% 7.67/2.73  tff(c_4058, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_2628, c_4052])).
% 7.67/2.73  tff(c_4072, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_2630, c_4058])).
% 7.67/2.73  tff(c_4074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3204, c_4072])).
% 7.67/2.73  tff(c_4076, plain, (![B_650, B_651]: (r1_tarski(k1_relat_1(B_650), B_651) | ~v1_relat_1(B_650) | ~v1_xboole_0(B_650))), inference(splitRight, [status(thm)], [c_2480])).
% 7.67/2.73  tff(c_1823, plain, (![C_389, B_390, A_391]: (v1_xboole_0(C_389) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(B_390, A_391))) | ~v1_xboole_0(A_391))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.67/2.73  tff(c_1832, plain, (![A_11, A_391, B_390]: (v1_xboole_0(A_11) | ~v1_xboole_0(A_391) | ~r1_tarski(A_11, k2_zfmisc_1(B_390, A_391)))), inference(resolution, [status(thm)], [c_18, c_1823])).
% 7.67/2.73  tff(c_4112, plain, (![B_650, A_391]: (v1_xboole_0(k1_relat_1(B_650)) | ~v1_xboole_0(A_391) | ~v1_relat_1(B_650) | ~v1_xboole_0(B_650))), inference(resolution, [status(thm)], [c_4076, c_1832])).
% 7.67/2.73  tff(c_4120, plain, (![A_391]: (~v1_xboole_0(A_391))), inference(splitLeft, [status(thm)], [c_4112])).
% 7.67/2.73  tff(c_5434, plain, (![C_766, A_767, B_768]: (v1_partfun1(C_766, A_767) | ~v1_funct_2(C_766, A_767, B_768) | ~v1_funct_1(C_766) | ~m1_subset_1(C_766, k1_zfmisc_1(k2_zfmisc_1(A_767, B_768))))), inference(negUnitSimplification, [status(thm)], [c_4120, c_40])).
% 7.67/2.73  tff(c_5440, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_4281, c_5434])).
% 7.67/2.73  tff(c_5454, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_4283, c_5440])).
% 7.67/2.73  tff(c_5456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4738, c_5454])).
% 7.67/2.73  tff(c_5457, plain, (![B_650]: (v1_xboole_0(k1_relat_1(B_650)) | ~v1_relat_1(B_650) | ~v1_xboole_0(B_650))), inference(splitRight, [status(thm)], [c_4112])).
% 7.67/2.73  tff(c_5951, plain, (v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_8') | ~v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5924, c_5457])).
% 7.67/2.73  tff(c_6005, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_5951])).
% 7.67/2.73  tff(c_6006, plain, (~v1_xboole_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2235, c_6005])).
% 7.67/2.73  tff(c_2347, plain, (![A_502]: (m1_subset_1(A_502, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_502), k2_relat_1(A_502)))) | ~v1_funct_1(A_502) | ~v1_relat_1(A_502))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.67/2.73  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.67/2.73  tff(c_2370, plain, (![A_502]: (r1_tarski(A_502, k2_zfmisc_1(k1_relat_1(A_502), k2_relat_1(A_502))) | ~v1_funct_1(A_502) | ~v1_relat_1(A_502))), inference(resolution, [status(thm)], [c_2347, c_16])).
% 7.67/2.73  tff(c_5957, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5924, c_2370])).
% 7.67/2.73  tff(c_6010, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_484, c_5957])).
% 7.67/2.73  tff(c_6039, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6010, c_1832])).
% 7.67/2.73  tff(c_6061, plain, (~v1_xboole_0(k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_6006, c_6039])).
% 7.67/2.73  tff(c_6284, plain, (![C_855, A_856, B_857]: (v1_funct_2(C_855, A_856, B_857) | ~v1_partfun1(C_855, A_856) | ~v1_funct_1(C_855) | ~m1_subset_1(C_855, k1_zfmisc_1(k2_zfmisc_1(A_856, B_857))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.67/2.73  tff(c_6293, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1628, c_6284])).
% 7.67/2.73  tff(c_6304, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_6293])).
% 7.67/2.73  tff(c_6305, plain, (~v1_partfun1('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1627, c_6304])).
% 7.67/2.73  tff(c_5972, plain, (v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5924, c_82])).
% 7.67/2.73  tff(c_6020, plain, (v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_484, c_5972])).
% 7.67/2.73  tff(c_5963, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8')))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5924, c_80])).
% 7.67/2.73  tff(c_6014, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_484, c_5963])).
% 7.67/2.73  tff(c_7366, plain, (![C_916, A_917, B_918]: (v1_partfun1(C_916, A_917) | ~v1_funct_2(C_916, A_917, B_918) | ~v1_funct_1(C_916) | ~m1_subset_1(C_916, k1_zfmisc_1(k2_zfmisc_1(A_917, B_918))) | v1_xboole_0(B_918))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.67/2.73  tff(c_7372, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_2('#skF_8', '#skF_6', k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | v1_xboole_0(k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6014, c_7366])).
% 7.67/2.73  tff(c_7386, plain, (v1_partfun1('#skF_8', '#skF_6') | v1_xboole_0(k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_484, c_6020, c_7372])).
% 7.67/2.73  tff(c_7388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6061, c_6305, c_7386])).
% 7.67/2.73  tff(c_7390, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_2233])).
% 7.67/2.73  tff(c_7468, plain, (![C_925, A_926, B_927]: (v1_partfun1(C_925, A_926) | ~m1_subset_1(C_925, k1_zfmisc_1(k2_zfmisc_1(A_926, B_927))) | ~v1_xboole_0(A_926))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.67/2.73  tff(c_7471, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1628, c_7468])).
% 7.67/2.73  tff(c_7478, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7390, c_7471])).
% 7.67/2.73  tff(c_8489, plain, (![C_1009, A_1010, B_1011]: (v1_funct_2(C_1009, A_1010, B_1011) | ~v1_partfun1(C_1009, A_1010) | ~v1_funct_1(C_1009) | ~m1_subset_1(C_1009, k1_zfmisc_1(k2_zfmisc_1(A_1010, B_1011))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.67/2.73  tff(c_8504, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1628, c_8489])).
% 7.67/2.73  tff(c_8515, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_7478, c_8504])).
% 7.67/2.73  tff(c_8517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1627, c_8515])).
% 7.67/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/2.73  
% 7.67/2.73  Inference rules
% 7.67/2.73  ----------------------
% 7.67/2.73  #Ref     : 0
% 7.67/2.73  #Sup     : 1918
% 7.67/2.73  #Fact    : 0
% 7.67/2.73  #Define  : 0
% 7.67/2.73  #Split   : 50
% 7.67/2.73  #Chain   : 0
% 7.67/2.73  #Close   : 0
% 7.67/2.73  
% 7.67/2.73  Ordering : KBO
% 7.67/2.73  
% 7.67/2.73  Simplification rules
% 7.67/2.73  ----------------------
% 7.67/2.73  #Subsume      : 741
% 7.67/2.73  #Demod        : 670
% 7.67/2.73  #Tautology    : 255
% 7.67/2.73  #SimpNegUnit  : 37
% 7.67/2.73  #BackRed      : 0
% 7.67/2.73  
% 7.67/2.73  #Partial instantiations: 0
% 7.67/2.73  #Strategies tried      : 1
% 7.67/2.73  
% 7.67/2.73  Timing (in seconds)
% 7.67/2.73  ----------------------
% 7.67/2.73  Preprocessing        : 0.36
% 7.67/2.73  Parsing              : 0.18
% 7.67/2.73  CNF conversion       : 0.03
% 7.67/2.73  Main loop            : 1.58
% 7.67/2.73  Inferencing          : 0.55
% 7.67/2.73  Reduction            : 0.47
% 7.67/2.73  Demodulation         : 0.29
% 7.67/2.73  BG Simplification    : 0.06
% 7.67/2.73  Subsumption          : 0.38
% 7.67/2.73  Abstraction          : 0.07
% 7.67/2.74  MUC search           : 0.00
% 7.67/2.74  Cooper               : 0.00
% 7.67/2.74  Total                : 2.00
% 7.67/2.74  Index Insertion      : 0.00
% 7.67/2.74  Index Deletion       : 0.00
% 7.67/2.74  Index Matching       : 0.00
% 7.67/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
