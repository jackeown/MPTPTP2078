%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:10 EST 2020

% Result     : Theorem 10.08s
% Output     : CNFRefutation 10.40s
% Verified   : 
% Statistics : Number of formulae       :  270 (2145 expanded)
%              Number of leaves         :   44 ( 696 expanded)
%              Depth                    :   13
%              Number of atoms          :  479 (6147 expanded)
%              Number of equality atoms :  187 (2161 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_152,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_132,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_36,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_19797,plain,(
    ! [B_1273,A_1274] :
      ( v1_relat_1(B_1273)
      | ~ m1_subset_1(B_1273,k1_zfmisc_1(A_1274))
      | ~ v1_relat_1(A_1274) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_19809,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_19797])).

tff(c_19819,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_19809])).

tff(c_20063,plain,(
    ! [C_1301,A_1302,B_1303] :
      ( v4_relat_1(C_1301,A_1302)
      | ~ m1_subset_1(C_1301,k1_zfmisc_1(k2_zfmisc_1(A_1302,B_1303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20082,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_20063])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20363,plain,(
    ! [A_1341,B_1342,C_1343] :
      ( k2_relset_1(A_1341,B_1342,C_1343) = k2_relat_1(C_1343)
      | ~ m1_subset_1(C_1343,k1_zfmisc_1(k2_zfmisc_1(A_1341,B_1342))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_20382,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_20363])).

tff(c_70,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_20384,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20382,c_70])).

tff(c_20491,plain,(
    ! [C_1357,A_1358,B_1359] :
      ( m1_subset_1(C_1357,k1_zfmisc_1(k2_zfmisc_1(A_1358,B_1359)))
      | ~ r1_tarski(k2_relat_1(C_1357),B_1359)
      | ~ r1_tarski(k1_relat_1(C_1357),A_1358)
      | ~ v1_relat_1(C_1357) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_119,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_581,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_600,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_581])).

tff(c_1063,plain,(
    ! [B_160,A_161,C_162] :
      ( k1_xboole_0 = B_160
      | k1_relset_1(A_161,B_160,C_162) = A_161
      | ~ v1_funct_2(C_162,A_161,B_160)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1076,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1063])).

tff(c_1089,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_600,c_1076])).

tff(c_1090,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_1089])).

tff(c_283,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_292,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_283])).

tff(c_299,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_292])).

tff(c_696,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_715,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_696])).

tff(c_721,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_70])).

tff(c_795,plain,(
    ! [C_125,A_126,B_127] :
      ( m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ r1_tarski(k2_relat_1(C_125),B_127)
      | ~ r1_tarski(k1_relat_1(C_125),A_126)
      | ~ v1_relat_1(C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4411,plain,(
    ! [C_309,A_310,B_311] :
      ( r1_tarski(C_309,k2_zfmisc_1(A_310,B_311))
      | ~ r1_tarski(k2_relat_1(C_309),B_311)
      | ~ r1_tarski(k1_relat_1(C_309),A_310)
      | ~ v1_relat_1(C_309) ) ),
    inference(resolution,[status(thm)],[c_795,c_22])).

tff(c_4417,plain,(
    ! [A_310] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_310,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_310)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_721,c_4411])).

tff(c_4429,plain,(
    ! [A_312] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_312,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_1090,c_4417])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_599,plain,(
    ! [A_100,B_101,A_9] :
      ( k1_relset_1(A_100,B_101,A_9) = k1_relat_1(A_9)
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_100,B_101)) ) ),
    inference(resolution,[status(thm)],[c_24,c_581])).

tff(c_4432,plain,(
    ! [A_312] :
      ( k1_relset_1(A_312,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_312) ) ),
    inference(resolution,[status(thm)],[c_4429,c_599])).

tff(c_4497,plain,(
    ! [A_314] :
      ( k1_relset_1(A_314,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_4432])).

tff(c_4502,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_4497])).

tff(c_374,plain,(
    ! [A_70,B_71] :
      ( v1_relat_1(A_70)
      | ~ v1_relat_1(B_71)
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_24,c_283])).

tff(c_396,plain,
    ( v1_relat_1(k2_relset_1('#skF_2','#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_374])).

tff(c_411,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_4427,plain,(
    ! [A_310] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_310,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_1090,c_4417])).

tff(c_934,plain,(
    ! [B_143,C_144,A_145] :
      ( k1_xboole_0 = B_143
      | v1_funct_2(C_144,A_145,B_143)
      | k1_relset_1(A_145,B_143,C_144) != A_145
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5193,plain,(
    ! [B_337,A_338,A_339] :
      ( k1_xboole_0 = B_337
      | v1_funct_2(A_338,A_339,B_337)
      | k1_relset_1(A_339,B_337,A_338) != A_339
      | ~ r1_tarski(A_338,k2_zfmisc_1(A_339,B_337)) ) ),
    inference(resolution,[status(thm)],[c_24,c_934])).

tff(c_5227,plain,(
    ! [A_310] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_310,'#skF_4')
      | k1_relset_1(A_310,'#skF_4','#skF_5') != A_310
      | ~ r1_tarski('#skF_2',A_310) ) ),
    inference(resolution,[status(thm)],[c_4427,c_5193])).

tff(c_5739,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5227])).

tff(c_20,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_114,plain,(
    ! [A_44,B_45] : v1_relat_1(k2_zfmisc_1(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_116,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_114])).

tff(c_5830,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5739,c_116])).

tff(c_5838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_5830])).

tff(c_5993,plain,(
    ! [A_372] :
      ( v1_funct_2('#skF_5',A_372,'#skF_4')
      | k1_relset_1(A_372,'#skF_4','#skF_5') != A_372
      | ~ r1_tarski('#skF_2',A_372) ) ),
    inference(splitRight,[status(thm)],[c_5227])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_66,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_78,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66])).

tff(c_145,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_5999,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_5993,c_145])).

tff(c_6004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4502,c_5999])).

tff(c_6006,plain,(
    v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_40,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6014,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6006,c_40])).

tff(c_6024,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6014])).

tff(c_6418,plain,(
    ! [A_424,B_425,C_426] :
      ( k1_relset_1(A_424,B_425,C_426) = k1_relat_1(C_426)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(A_424,B_425))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6437,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_6418])).

tff(c_6674,plain,(
    ! [B_459,A_460,C_461] :
      ( k1_xboole_0 = B_459
      | k1_relset_1(A_460,B_459,C_461) = A_460
      | ~ v1_funct_2(C_461,A_460,B_459)
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1(A_460,B_459))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6687,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_6674])).

tff(c_6700,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6437,c_6687])).

tff(c_6701,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_6700])).

tff(c_6363,plain,(
    ! [A_421,B_422,C_423] :
      ( k2_relset_1(A_421,B_422,C_423) = k2_relat_1(C_423)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_421,B_422))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6382,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_6363])).

tff(c_6386,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6382,c_70])).

tff(c_6536,plain,(
    ! [C_440,A_441,B_442] :
      ( m1_subset_1(C_440,k1_zfmisc_1(k2_zfmisc_1(A_441,B_442)))
      | ~ r1_tarski(k2_relat_1(C_440),B_442)
      | ~ r1_tarski(k1_relat_1(C_440),A_441)
      | ~ v1_relat_1(C_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_9830,plain,(
    ! [C_617,A_618,B_619] :
      ( r1_tarski(C_617,k2_zfmisc_1(A_618,B_619))
      | ~ r1_tarski(k2_relat_1(C_617),B_619)
      | ~ r1_tarski(k1_relat_1(C_617),A_618)
      | ~ v1_relat_1(C_617) ) ),
    inference(resolution,[status(thm)],[c_6536,c_22])).

tff(c_9834,plain,(
    ! [A_618] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_618,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_618)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6386,c_9830])).

tff(c_9928,plain,(
    ! [A_628] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_628,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_628) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_6701,c_9834])).

tff(c_6436,plain,(
    ! [A_424,B_425,A_9] :
      ( k1_relset_1(A_424,B_425,A_9) = k1_relat_1(A_9)
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_424,B_425)) ) ),
    inference(resolution,[status(thm)],[c_24,c_6418])).

tff(c_9931,plain,(
    ! [A_628] :
      ( k1_relset_1(A_628,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_628) ) ),
    inference(resolution,[status(thm)],[c_9928,c_6436])).

tff(c_9996,plain,(
    ! [A_630] :
      ( k1_relset_1(A_630,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_630) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6701,c_9931])).

tff(c_10001,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_9996])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6103,plain,(
    ! [C_384,B_385,A_386] :
      ( ~ v1_xboole_0(C_384)
      | ~ m1_subset_1(B_385,k1_zfmisc_1(C_384))
      | ~ r2_hidden(A_386,B_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6129,plain,(
    ! [B_391,A_392,A_393] :
      ( ~ v1_xboole_0(B_391)
      | ~ r2_hidden(A_392,A_393)
      | ~ r1_tarski(A_393,B_391) ) ),
    inference(resolution,[status(thm)],[c_24,c_6103])).

tff(c_6133,plain,(
    ! [B_394,A_395] :
      ( ~ v1_xboole_0(B_394)
      | ~ r1_tarski(A_395,B_394)
      | k1_xboole_0 = A_395 ) ),
    inference(resolution,[status(thm)],[c_6,c_6129])).

tff(c_6155,plain,
    ( ~ v1_xboole_0('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_6133])).

tff(c_6172,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6155])).

tff(c_9842,plain,(
    ! [A_618] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_618,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_6701,c_9834])).

tff(c_6809,plain,(
    ! [B_468,C_469,A_470] :
      ( k1_xboole_0 = B_468
      | v1_funct_2(C_469,A_470,B_468)
      | k1_relset_1(A_470,B_468,C_469) != A_470
      | ~ m1_subset_1(C_469,k1_zfmisc_1(k2_zfmisc_1(A_470,B_468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_10924,plain,(
    ! [B_668,A_669,A_670] :
      ( k1_xboole_0 = B_668
      | v1_funct_2(A_669,A_670,B_668)
      | k1_relset_1(A_670,B_668,A_669) != A_670
      | ~ r1_tarski(A_669,k2_zfmisc_1(A_670,B_668)) ) ),
    inference(resolution,[status(thm)],[c_24,c_6809])).

tff(c_10955,plain,(
    ! [A_618] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_618,'#skF_4')
      | k1_relset_1(A_618,'#skF_4','#skF_5') != A_618
      | ~ r1_tarski('#skF_2',A_618) ) ),
    inference(resolution,[status(thm)],[c_9842,c_10924])).

tff(c_11051,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10955])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_11148,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11051,c_2])).

tff(c_11151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6172,c_11148])).

tff(c_11483,plain,(
    ! [A_687] :
      ( v1_funct_2('#skF_5',A_687,'#skF_4')
      | k1_relset_1(A_687,'#skF_4','#skF_5') != A_687
      | ~ r1_tarski('#skF_2',A_687) ) ),
    inference(splitRight,[status(thm)],[c_10955])).

tff(c_11489,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_11483,c_145])).

tff(c_11494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10001,c_11489])).

tff(c_11496,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_6155])).

tff(c_121,plain,(
    ! [A_46] :
      ( v1_xboole_0(k1_relat_1(A_46))
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_125,plain,(
    ! [A_46] :
      ( k1_relat_1(A_46) = k1_xboole_0
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_121,c_4])).

tff(c_11499,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11496,c_125])).

tff(c_11506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6024,c_11499])).

tff(c_11507,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6014])).

tff(c_14,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_11530,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11507,c_14])).

tff(c_244,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_262,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_70,c_244])).

tff(c_331,plain,(
    ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_11584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11530,c_331])).

tff(c_11585,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_11862,plain,(
    ! [A_730,B_731,C_732] :
      ( k2_relset_1(A_730,B_731,C_732) = k2_relat_1(C_732)
      | ~ m1_subset_1(C_732,k1_zfmisc_1(k2_zfmisc_1(A_730,B_731))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_11872,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_11862])).

tff(c_11882,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11585,c_11872])).

tff(c_38,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_306,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_299,c_38])).

tff(c_11625,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_11883,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11882,c_11625])).

tff(c_11956,plain,(
    ! [A_746,B_747,C_748] :
      ( k1_relset_1(A_746,B_747,C_748) = k1_relat_1(C_748)
      | ~ m1_subset_1(C_748,k1_zfmisc_1(k2_zfmisc_1(A_746,B_747))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_11975,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_11956])).

tff(c_12208,plain,(
    ! [B_776,A_777,C_778] :
      ( k1_xboole_0 = B_776
      | k1_relset_1(A_777,B_776,C_778) = A_777
      | ~ v1_funct_2(C_778,A_777,B_776)
      | ~ m1_subset_1(C_778,k1_zfmisc_1(k2_zfmisc_1(A_777,B_776))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_12221,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_12208])).

tff(c_12234,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_11975,c_12221])).

tff(c_12235,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_12234])).

tff(c_12084,plain,(
    ! [C_759,A_760,B_761] :
      ( m1_subset_1(C_759,k1_zfmisc_1(k2_zfmisc_1(A_760,B_761)))
      | ~ r1_tarski(k2_relat_1(C_759),B_761)
      | ~ r1_tarski(k1_relat_1(C_759),A_760)
      | ~ v1_relat_1(C_759) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,(
    ! [A_26,B_27,C_28] :
      ( k1_relset_1(A_26,B_27,C_28) = k1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_15840,plain,(
    ! [A_965,B_966,C_967] :
      ( k1_relset_1(A_965,B_966,C_967) = k1_relat_1(C_967)
      | ~ r1_tarski(k2_relat_1(C_967),B_966)
      | ~ r1_tarski(k1_relat_1(C_967),A_965)
      | ~ v1_relat_1(C_967) ) ),
    inference(resolution,[status(thm)],[c_12084,c_46])).

tff(c_15846,plain,(
    ! [A_965,B_966] :
      ( k1_relset_1(A_965,B_966,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_4',B_966)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_965)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11882,c_15840])).

tff(c_15947,plain,(
    ! [A_974,B_975] :
      ( k1_relset_1(A_974,B_975,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_4',B_975)
      | ~ r1_tarski('#skF_2',A_974) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_12235,c_12235,c_15846])).

tff(c_15952,plain,(
    ! [A_976] :
      ( k1_relset_1(A_976,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_976) ) ),
    inference(resolution,[status(thm)],[c_12,c_15947])).

tff(c_15957,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_15952])).

tff(c_15117,plain,(
    ! [C_932,A_933,B_934] :
      ( r1_tarski(C_932,k2_zfmisc_1(A_933,B_934))
      | ~ r1_tarski(k2_relat_1(C_932),B_934)
      | ~ r1_tarski(k1_relat_1(C_932),A_933)
      | ~ v1_relat_1(C_932) ) ),
    inference(resolution,[status(thm)],[c_12084,c_22])).

tff(c_15123,plain,(
    ! [A_933,B_934] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_933,B_934))
      | ~ r1_tarski('#skF_4',B_934)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_933)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11882,c_15117])).

tff(c_15132,plain,(
    ! [A_933,B_934] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_933,B_934))
      | ~ r1_tarski('#skF_4',B_934)
      | ~ r1_tarski('#skF_2',A_933) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_12235,c_15123])).

tff(c_12273,plain,(
    ! [B_779,C_780,A_781] :
      ( k1_xboole_0 = B_779
      | v1_funct_2(C_780,A_781,B_779)
      | k1_relset_1(A_781,B_779,C_780) != A_781
      | ~ m1_subset_1(C_780,k1_zfmisc_1(k2_zfmisc_1(A_781,B_779))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_16376,plain,(
    ! [B_995,A_996,A_997] :
      ( k1_xboole_0 = B_995
      | v1_funct_2(A_996,A_997,B_995)
      | k1_relset_1(A_997,B_995,A_996) != A_997
      | ~ r1_tarski(A_996,k2_zfmisc_1(A_997,B_995)) ) ),
    inference(resolution,[status(thm)],[c_24,c_12273])).

tff(c_17068,plain,(
    ! [B_1018,A_1019] :
      ( k1_xboole_0 = B_1018
      | v1_funct_2('#skF_5',A_1019,B_1018)
      | k1_relset_1(A_1019,B_1018,'#skF_5') != A_1019
      | ~ r1_tarski('#skF_4',B_1018)
      | ~ r1_tarski('#skF_2',A_1019) ) ),
    inference(resolution,[status(thm)],[c_15132,c_16376])).

tff(c_17077,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_17068,c_145])).

tff(c_17082,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_15957,c_17077])).

tff(c_17084,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11883,c_17082])).

tff(c_17085,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_126,plain,(
    ! [A_47] :
      ( k1_relat_1(A_47) = k1_xboole_0
      | ~ v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_121,c_4])).

tff(c_134,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_126])).

tff(c_17097,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17085,c_17085,c_134])).

tff(c_307,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_299,c_40])).

tff(c_11607,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_17088,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17085,c_11607])).

tff(c_17150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17097,c_17088])).

tff(c_17151,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_17165,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17151,c_119])).

tff(c_17152,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_17176,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17151,c_17152])).

tff(c_17537,plain,(
    ! [A_1061,B_1062,C_1063] :
      ( k1_relset_1(A_1061,B_1062,C_1063) = k1_relat_1(C_1063)
      | ~ m1_subset_1(C_1063,k1_zfmisc_1(k2_zfmisc_1(A_1061,B_1062))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_17553,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_17537])).

tff(c_17557,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17176,c_17553])).

tff(c_64,plain,(
    ! [B_37,A_36,C_38] :
      ( k1_xboole_0 = B_37
      | k1_relset_1(A_36,B_37,C_38) = A_36
      | ~ v1_funct_2(C_38,A_36,B_37)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_17898,plain,(
    ! [B_1111,A_1112,C_1113] :
      ( B_1111 = '#skF_5'
      | k1_relset_1(A_1112,B_1111,C_1113) = A_1112
      | ~ v1_funct_2(C_1113,A_1112,B_1111)
      | ~ m1_subset_1(C_1113,k1_zfmisc_1(k2_zfmisc_1(A_1112,B_1111))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17151,c_64])).

tff(c_17917,plain,
    ( '#skF_5' = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_17898])).

tff(c_17925,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_17557,c_17917])).

tff(c_17926,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_17165,c_17925])).

tff(c_17166,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_5',B_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17151,c_17151,c_20])).

tff(c_17961,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_2',B_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17926,c_17926,c_17166])).

tff(c_182,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_198,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_182])).

tff(c_258,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_198,c_244])).

tff(c_17225,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_17957,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17926,c_17225])).

tff(c_18365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_17961,c_17957])).

tff(c_18366,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_16,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18919,plain,(
    ! [B_1200,A_1201] :
      ( B_1200 = '#skF_5'
      | A_1201 = '#skF_5'
      | k2_zfmisc_1(A_1201,B_1200) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17151,c_17151,c_17151,c_16])).

tff(c_18922,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_18366,c_18919])).

tff(c_18931,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_17165,c_18922])).

tff(c_18967,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18931,c_18931,c_17176])).

tff(c_17169,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17151,c_14])).

tff(c_18966,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18931,c_17169])).

tff(c_18707,plain,(
    ! [A_1172,B_1173,C_1174] :
      ( k1_relset_1(A_1172,B_1173,C_1174) = k1_relat_1(C_1174)
      | ~ m1_subset_1(C_1174,k1_zfmisc_1(k2_zfmisc_1(A_1172,B_1173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_19669,plain,(
    ! [A_1261,B_1262,A_1263] :
      ( k1_relset_1(A_1261,B_1262,A_1263) = k1_relat_1(A_1263)
      | ~ r1_tarski(A_1263,k2_zfmisc_1(A_1261,B_1262)) ) ),
    inference(resolution,[status(thm)],[c_24,c_18707])).

tff(c_19679,plain,(
    ! [A_1261,B_1262] : k1_relset_1(A_1261,B_1262,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18966,c_19669])).

tff(c_19692,plain,(
    ! [A_1261,B_1262] : k1_relset_1(A_1261,B_1262,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18967,c_19679])).

tff(c_18416,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18366,c_72])).

tff(c_18960,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18931,c_18931,c_18416])).

tff(c_18970,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18931,c_17151])).

tff(c_58,plain,(
    ! [C_38,B_37] :
      ( v1_funct_2(C_38,k1_xboole_0,B_37)
      | k1_relset_1(k1_xboole_0,B_37,C_38) != k1_xboole_0
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_80,plain,(
    ! [C_38,B_37] :
      ( v1_funct_2(C_38,k1_xboole_0,B_37)
      | k1_relset_1(k1_xboole_0,B_37,C_38) != k1_xboole_0
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_58])).

tff(c_19040,plain,(
    ! [C_38,B_37] :
      ( v1_funct_2(C_38,'#skF_2',B_37)
      | k1_relset_1('#skF_2',B_37,C_38) != '#skF_2'
      | ~ m1_subset_1(C_38,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18970,c_18970,c_18970,c_18970,c_80])).

tff(c_19316,plain,(
    ! [B_1223] :
      ( v1_funct_2('#skF_2','#skF_2',B_1223)
      | k1_relset_1('#skF_2',B_1223,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_18960,c_19040])).

tff(c_18973,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18931,c_145])).

tff(c_19325,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_2') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_19316,c_18973])).

tff(c_19703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19692,c_19325])).

tff(c_19704,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_20514,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20491,c_19704])).

tff(c_20532,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19819,c_20384,c_20514])).

tff(c_20535,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_20532])).

tff(c_20539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19819,c_20082,c_20535])).

tff(c_20541,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_20540,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_20551,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20541,c_20540])).

tff(c_20546,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20540,c_2])).

tff(c_20556,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20551,c_20546])).

tff(c_20604,plain,(
    ! [A_1364] :
      ( v1_xboole_0(k1_relat_1(A_1364))
      | ~ v1_xboole_0(A_1364) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20544,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20540,c_4])).

tff(c_20597,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20551,c_20544])).

tff(c_20610,plain,(
    ! [A_1365] :
      ( k1_relat_1(A_1365) = '#skF_3'
      | ~ v1_xboole_0(A_1365) ) ),
    inference(resolution,[status(thm)],[c_20604,c_20597])).

tff(c_20618,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20556,c_20610])).

tff(c_20545,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20540,c_14])).

tff(c_20564,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20551,c_20545])).

tff(c_20542,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_2',B_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20540,c_20540,c_20])).

tff(c_20567,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_3',B_8) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20551,c_20551,c_20542])).

tff(c_20609,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20567,c_20551,c_72])).

tff(c_20693,plain,(
    ! [A_1373,B_1374] :
      ( r1_tarski(A_1373,B_1374)
      | ~ m1_subset_1(A_1373,k1_zfmisc_1(B_1374)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20709,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_20609,c_20693])).

tff(c_20773,plain,(
    ! [B_1381,A_1382] :
      ( B_1381 = A_1382
      | ~ r1_tarski(B_1381,A_1382)
      | ~ r1_tarski(A_1382,B_1381) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20779,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_20709,c_20773])).

tff(c_20792,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20564,c_20779])).

tff(c_20802,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20792,c_20609])).

tff(c_21297,plain,(
    ! [A_1448,B_1449,C_1450] :
      ( k1_relset_1(A_1448,B_1449,C_1450) = k1_relat_1(C_1450)
      | ~ m1_subset_1(C_1450,k1_zfmisc_1(k2_zfmisc_1(A_1448,B_1449))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_21330,plain,(
    ! [B_1452,C_1453] :
      ( k1_relset_1('#skF_3',B_1452,C_1453) = k1_relat_1(C_1453)
      | ~ m1_subset_1(C_1453,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20567,c_21297])).

tff(c_21332,plain,(
    ! [B_1452] : k1_relset_1('#skF_3',B_1452,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20802,c_21330])).

tff(c_21337,plain,(
    ! [B_1452] : k1_relset_1('#skF_3',B_1452,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20618,c_21332])).

tff(c_21491,plain,(
    ! [C_1474,B_1475] :
      ( v1_funct_2(C_1474,'#skF_3',B_1475)
      | k1_relset_1('#skF_3',B_1475,C_1474) != '#skF_3'
      | ~ m1_subset_1(C_1474,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20541,c_20541,c_20541,c_20541,c_80])).

tff(c_21493,plain,(
    ! [B_1475] :
      ( v1_funct_2('#skF_3','#skF_3',B_1475)
      | k1_relset_1('#skF_3',B_1475,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_20802,c_21491])).

tff(c_21499,plain,(
    ! [B_1475] : v1_funct_2('#skF_3','#skF_3',B_1475) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21337,c_21493])).

tff(c_20631,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20551,c_20609,c_20567,c_20551,c_78])).

tff(c_20801,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20792,c_20631])).

tff(c_21504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21499,c_20801])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:55:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.08/3.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/3.76  
% 10.08/3.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/3.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 10.08/3.76  
% 10.08/3.76  %Foreground sorts:
% 10.08/3.76  
% 10.08/3.76  
% 10.08/3.76  %Background operators:
% 10.08/3.76  
% 10.08/3.76  
% 10.08/3.76  %Foreground operators:
% 10.08/3.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.08/3.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.08/3.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.08/3.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.08/3.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.08/3.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.08/3.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.08/3.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.08/3.76  tff('#skF_5', type, '#skF_5': $i).
% 10.08/3.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.08/3.76  tff('#skF_2', type, '#skF_2': $i).
% 10.08/3.76  tff('#skF_3', type, '#skF_3': $i).
% 10.08/3.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.08/3.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.08/3.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.08/3.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.08/3.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.08/3.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.08/3.76  tff('#skF_4', type, '#skF_4': $i).
% 10.08/3.76  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.08/3.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.08/3.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.08/3.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.08/3.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.08/3.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.08/3.76  
% 10.40/3.80  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.40/3.80  tff(f_152, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 10.40/3.80  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.40/3.80  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.40/3.80  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 10.40/3.80  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.40/3.80  tff(f_112, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 10.40/3.80  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.40/3.80  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.40/3.80  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.40/3.80  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.40/3.80  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.40/3.80  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 10.40/3.80  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.40/3.80  tff(f_63, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 10.40/3.80  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.40/3.80  tff(f_80, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 10.40/3.80  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.40/3.80  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.40/3.80  tff(c_36, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.40/3.80  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.40/3.80  tff(c_19797, plain, (![B_1273, A_1274]: (v1_relat_1(B_1273) | ~m1_subset_1(B_1273, k1_zfmisc_1(A_1274)) | ~v1_relat_1(A_1274))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.40/3.80  tff(c_19809, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_19797])).
% 10.40/3.80  tff(c_19819, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_19809])).
% 10.40/3.80  tff(c_20063, plain, (![C_1301, A_1302, B_1303]: (v4_relat_1(C_1301, A_1302) | ~m1_subset_1(C_1301, k1_zfmisc_1(k2_zfmisc_1(A_1302, B_1303))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.40/3.80  tff(c_20082, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_20063])).
% 10.40/3.80  tff(c_32, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.40/3.80  tff(c_20363, plain, (![A_1341, B_1342, C_1343]: (k2_relset_1(A_1341, B_1342, C_1343)=k2_relat_1(C_1343) | ~m1_subset_1(C_1343, k1_zfmisc_1(k2_zfmisc_1(A_1341, B_1342))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.40/3.80  tff(c_20382, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_20363])).
% 10.40/3.80  tff(c_70, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.40/3.80  tff(c_20384, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20382, c_70])).
% 10.40/3.80  tff(c_20491, plain, (![C_1357, A_1358, B_1359]: (m1_subset_1(C_1357, k1_zfmisc_1(k2_zfmisc_1(A_1358, B_1359))) | ~r1_tarski(k2_relat_1(C_1357), B_1359) | ~r1_tarski(k1_relat_1(C_1357), A_1358) | ~v1_relat_1(C_1357))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.40/3.80  tff(c_12, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.40/3.80  tff(c_68, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.40/3.80  tff(c_119, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_68])).
% 10.40/3.80  tff(c_74, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.40/3.80  tff(c_581, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.80  tff(c_600, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_581])).
% 10.40/3.80  tff(c_1063, plain, (![B_160, A_161, C_162]: (k1_xboole_0=B_160 | k1_relset_1(A_161, B_160, C_162)=A_161 | ~v1_funct_2(C_162, A_161, B_160) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.40/3.80  tff(c_1076, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_1063])).
% 10.40/3.80  tff(c_1089, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_600, c_1076])).
% 10.40/3.80  tff(c_1090, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_119, c_1089])).
% 10.40/3.80  tff(c_283, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.40/3.80  tff(c_292, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_283])).
% 10.40/3.80  tff(c_299, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_292])).
% 10.40/3.80  tff(c_696, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.40/3.80  tff(c_715, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_696])).
% 10.40/3.80  tff(c_721, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_715, c_70])).
% 10.40/3.80  tff(c_795, plain, (![C_125, A_126, B_127]: (m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~r1_tarski(k2_relat_1(C_125), B_127) | ~r1_tarski(k1_relat_1(C_125), A_126) | ~v1_relat_1(C_125))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.40/3.80  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.40/3.80  tff(c_4411, plain, (![C_309, A_310, B_311]: (r1_tarski(C_309, k2_zfmisc_1(A_310, B_311)) | ~r1_tarski(k2_relat_1(C_309), B_311) | ~r1_tarski(k1_relat_1(C_309), A_310) | ~v1_relat_1(C_309))), inference(resolution, [status(thm)], [c_795, c_22])).
% 10.40/3.80  tff(c_4417, plain, (![A_310]: (r1_tarski('#skF_5', k2_zfmisc_1(A_310, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_310) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_721, c_4411])).
% 10.40/3.80  tff(c_4429, plain, (![A_312]: (r1_tarski('#skF_5', k2_zfmisc_1(A_312, '#skF_4')) | ~r1_tarski('#skF_2', A_312))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_1090, c_4417])).
% 10.40/3.80  tff(c_24, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.40/3.80  tff(c_599, plain, (![A_100, B_101, A_9]: (k1_relset_1(A_100, B_101, A_9)=k1_relat_1(A_9) | ~r1_tarski(A_9, k2_zfmisc_1(A_100, B_101)))), inference(resolution, [status(thm)], [c_24, c_581])).
% 10.40/3.80  tff(c_4432, plain, (![A_312]: (k1_relset_1(A_312, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_312))), inference(resolution, [status(thm)], [c_4429, c_599])).
% 10.40/3.80  tff(c_4497, plain, (![A_314]: (k1_relset_1(A_314, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_314))), inference(demodulation, [status(thm), theory('equality')], [c_1090, c_4432])).
% 10.40/3.80  tff(c_4502, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_4497])).
% 10.40/3.80  tff(c_374, plain, (![A_70, B_71]: (v1_relat_1(A_70) | ~v1_relat_1(B_71) | ~r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_24, c_283])).
% 10.40/3.80  tff(c_396, plain, (v1_relat_1(k2_relset_1('#skF_2', '#skF_3', '#skF_5')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_374])).
% 10.40/3.80  tff(c_411, plain, (~v1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_396])).
% 10.40/3.80  tff(c_4427, plain, (![A_310]: (r1_tarski('#skF_5', k2_zfmisc_1(A_310, '#skF_4')) | ~r1_tarski('#skF_2', A_310))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_1090, c_4417])).
% 10.40/3.80  tff(c_934, plain, (![B_143, C_144, A_145]: (k1_xboole_0=B_143 | v1_funct_2(C_144, A_145, B_143) | k1_relset_1(A_145, B_143, C_144)!=A_145 | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_143))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.40/3.80  tff(c_5193, plain, (![B_337, A_338, A_339]: (k1_xboole_0=B_337 | v1_funct_2(A_338, A_339, B_337) | k1_relset_1(A_339, B_337, A_338)!=A_339 | ~r1_tarski(A_338, k2_zfmisc_1(A_339, B_337)))), inference(resolution, [status(thm)], [c_24, c_934])).
% 10.40/3.80  tff(c_5227, plain, (![A_310]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_310, '#skF_4') | k1_relset_1(A_310, '#skF_4', '#skF_5')!=A_310 | ~r1_tarski('#skF_2', A_310))), inference(resolution, [status(thm)], [c_4427, c_5193])).
% 10.40/3.80  tff(c_5739, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5227])).
% 10.40/3.80  tff(c_20, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.40/3.80  tff(c_114, plain, (![A_44, B_45]: (v1_relat_1(k2_zfmisc_1(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.40/3.80  tff(c_116, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_114])).
% 10.40/3.80  tff(c_5830, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5739, c_116])).
% 10.40/3.80  tff(c_5838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_411, c_5830])).
% 10.40/3.80  tff(c_5993, plain, (![A_372]: (v1_funct_2('#skF_5', A_372, '#skF_4') | k1_relset_1(A_372, '#skF_4', '#skF_5')!=A_372 | ~r1_tarski('#skF_2', A_372))), inference(splitRight, [status(thm)], [c_5227])).
% 10.40/3.80  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.40/3.80  tff(c_66, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.40/3.80  tff(c_78, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66])).
% 10.40/3.80  tff(c_145, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_78])).
% 10.40/3.80  tff(c_5999, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_5993, c_145])).
% 10.40/3.80  tff(c_6004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4502, c_5999])).
% 10.40/3.80  tff(c_6006, plain, (v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_396])).
% 10.40/3.80  tff(c_40, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.40/3.80  tff(c_6014, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6006, c_40])).
% 10.40/3.80  tff(c_6024, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6014])).
% 10.40/3.80  tff(c_6418, plain, (![A_424, B_425, C_426]: (k1_relset_1(A_424, B_425, C_426)=k1_relat_1(C_426) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(A_424, B_425))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.80  tff(c_6437, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_6418])).
% 10.40/3.80  tff(c_6674, plain, (![B_459, A_460, C_461]: (k1_xboole_0=B_459 | k1_relset_1(A_460, B_459, C_461)=A_460 | ~v1_funct_2(C_461, A_460, B_459) | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1(A_460, B_459))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.40/3.80  tff(c_6687, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_6674])).
% 10.40/3.80  tff(c_6700, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6437, c_6687])).
% 10.40/3.80  tff(c_6701, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_119, c_6700])).
% 10.40/3.80  tff(c_6363, plain, (![A_421, B_422, C_423]: (k2_relset_1(A_421, B_422, C_423)=k2_relat_1(C_423) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_421, B_422))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.40/3.80  tff(c_6382, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_6363])).
% 10.40/3.80  tff(c_6386, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6382, c_70])).
% 10.40/3.80  tff(c_6536, plain, (![C_440, A_441, B_442]: (m1_subset_1(C_440, k1_zfmisc_1(k2_zfmisc_1(A_441, B_442))) | ~r1_tarski(k2_relat_1(C_440), B_442) | ~r1_tarski(k1_relat_1(C_440), A_441) | ~v1_relat_1(C_440))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.40/3.80  tff(c_9830, plain, (![C_617, A_618, B_619]: (r1_tarski(C_617, k2_zfmisc_1(A_618, B_619)) | ~r1_tarski(k2_relat_1(C_617), B_619) | ~r1_tarski(k1_relat_1(C_617), A_618) | ~v1_relat_1(C_617))), inference(resolution, [status(thm)], [c_6536, c_22])).
% 10.40/3.80  tff(c_9834, plain, (![A_618]: (r1_tarski('#skF_5', k2_zfmisc_1(A_618, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_618) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_6386, c_9830])).
% 10.40/3.80  tff(c_9928, plain, (![A_628]: (r1_tarski('#skF_5', k2_zfmisc_1(A_628, '#skF_4')) | ~r1_tarski('#skF_2', A_628))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_6701, c_9834])).
% 10.40/3.80  tff(c_6436, plain, (![A_424, B_425, A_9]: (k1_relset_1(A_424, B_425, A_9)=k1_relat_1(A_9) | ~r1_tarski(A_9, k2_zfmisc_1(A_424, B_425)))), inference(resolution, [status(thm)], [c_24, c_6418])).
% 10.40/3.80  tff(c_9931, plain, (![A_628]: (k1_relset_1(A_628, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_628))), inference(resolution, [status(thm)], [c_9928, c_6436])).
% 10.40/3.80  tff(c_9996, plain, (![A_630]: (k1_relset_1(A_630, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_630))), inference(demodulation, [status(thm), theory('equality')], [c_6701, c_9931])).
% 10.40/3.80  tff(c_10001, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_9996])).
% 10.40/3.80  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.40/3.80  tff(c_6103, plain, (![C_384, B_385, A_386]: (~v1_xboole_0(C_384) | ~m1_subset_1(B_385, k1_zfmisc_1(C_384)) | ~r2_hidden(A_386, B_385))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.40/3.80  tff(c_6129, plain, (![B_391, A_392, A_393]: (~v1_xboole_0(B_391) | ~r2_hidden(A_392, A_393) | ~r1_tarski(A_393, B_391))), inference(resolution, [status(thm)], [c_24, c_6103])).
% 10.40/3.80  tff(c_6133, plain, (![B_394, A_395]: (~v1_xboole_0(B_394) | ~r1_tarski(A_395, B_394) | k1_xboole_0=A_395)), inference(resolution, [status(thm)], [c_6, c_6129])).
% 10.40/3.80  tff(c_6155, plain, (~v1_xboole_0('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_6133])).
% 10.40/3.80  tff(c_6172, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_6155])).
% 10.40/3.80  tff(c_9842, plain, (![A_618]: (r1_tarski('#skF_5', k2_zfmisc_1(A_618, '#skF_4')) | ~r1_tarski('#skF_2', A_618))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_6701, c_9834])).
% 10.40/3.80  tff(c_6809, plain, (![B_468, C_469, A_470]: (k1_xboole_0=B_468 | v1_funct_2(C_469, A_470, B_468) | k1_relset_1(A_470, B_468, C_469)!=A_470 | ~m1_subset_1(C_469, k1_zfmisc_1(k2_zfmisc_1(A_470, B_468))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.40/3.80  tff(c_10924, plain, (![B_668, A_669, A_670]: (k1_xboole_0=B_668 | v1_funct_2(A_669, A_670, B_668) | k1_relset_1(A_670, B_668, A_669)!=A_670 | ~r1_tarski(A_669, k2_zfmisc_1(A_670, B_668)))), inference(resolution, [status(thm)], [c_24, c_6809])).
% 10.40/3.80  tff(c_10955, plain, (![A_618]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_618, '#skF_4') | k1_relset_1(A_618, '#skF_4', '#skF_5')!=A_618 | ~r1_tarski('#skF_2', A_618))), inference(resolution, [status(thm)], [c_9842, c_10924])).
% 10.40/3.80  tff(c_11051, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_10955])).
% 10.40/3.80  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.40/3.80  tff(c_11148, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11051, c_2])).
% 10.40/3.80  tff(c_11151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6172, c_11148])).
% 10.40/3.80  tff(c_11483, plain, (![A_687]: (v1_funct_2('#skF_5', A_687, '#skF_4') | k1_relset_1(A_687, '#skF_4', '#skF_5')!=A_687 | ~r1_tarski('#skF_2', A_687))), inference(splitRight, [status(thm)], [c_10955])).
% 10.40/3.80  tff(c_11489, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_11483, c_145])).
% 10.40/3.80  tff(c_11494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10001, c_11489])).
% 10.40/3.80  tff(c_11496, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_6155])).
% 10.40/3.80  tff(c_121, plain, (![A_46]: (v1_xboole_0(k1_relat_1(A_46)) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.40/3.80  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 10.40/3.80  tff(c_125, plain, (![A_46]: (k1_relat_1(A_46)=k1_xboole_0 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_121, c_4])).
% 10.40/3.80  tff(c_11499, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_11496, c_125])).
% 10.40/3.80  tff(c_11506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6024, c_11499])).
% 10.40/3.80  tff(c_11507, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_6014])).
% 10.40/3.80  tff(c_14, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.40/3.80  tff(c_11530, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_11507, c_14])).
% 10.40/3.80  tff(c_244, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.40/3.80  tff(c_262, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_70, c_244])).
% 10.40/3.80  tff(c_331, plain, (~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_262])).
% 10.40/3.80  tff(c_11584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11530, c_331])).
% 10.40/3.80  tff(c_11585, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_262])).
% 10.40/3.80  tff(c_11862, plain, (![A_730, B_731, C_732]: (k2_relset_1(A_730, B_731, C_732)=k2_relat_1(C_732) | ~m1_subset_1(C_732, k1_zfmisc_1(k2_zfmisc_1(A_730, B_731))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.40/3.80  tff(c_11872, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_11862])).
% 10.40/3.80  tff(c_11882, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11585, c_11872])).
% 10.40/3.80  tff(c_38, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.40/3.80  tff(c_306, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_299, c_38])).
% 10.40/3.80  tff(c_11625, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_306])).
% 10.40/3.80  tff(c_11883, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11882, c_11625])).
% 10.40/3.80  tff(c_11956, plain, (![A_746, B_747, C_748]: (k1_relset_1(A_746, B_747, C_748)=k1_relat_1(C_748) | ~m1_subset_1(C_748, k1_zfmisc_1(k2_zfmisc_1(A_746, B_747))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.80  tff(c_11975, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_11956])).
% 10.40/3.80  tff(c_12208, plain, (![B_776, A_777, C_778]: (k1_xboole_0=B_776 | k1_relset_1(A_777, B_776, C_778)=A_777 | ~v1_funct_2(C_778, A_777, B_776) | ~m1_subset_1(C_778, k1_zfmisc_1(k2_zfmisc_1(A_777, B_776))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.40/3.80  tff(c_12221, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_12208])).
% 10.40/3.80  tff(c_12234, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_11975, c_12221])).
% 10.40/3.80  tff(c_12235, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_119, c_12234])).
% 10.40/3.80  tff(c_12084, plain, (![C_759, A_760, B_761]: (m1_subset_1(C_759, k1_zfmisc_1(k2_zfmisc_1(A_760, B_761))) | ~r1_tarski(k2_relat_1(C_759), B_761) | ~r1_tarski(k1_relat_1(C_759), A_760) | ~v1_relat_1(C_759))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.40/3.80  tff(c_46, plain, (![A_26, B_27, C_28]: (k1_relset_1(A_26, B_27, C_28)=k1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.80  tff(c_15840, plain, (![A_965, B_966, C_967]: (k1_relset_1(A_965, B_966, C_967)=k1_relat_1(C_967) | ~r1_tarski(k2_relat_1(C_967), B_966) | ~r1_tarski(k1_relat_1(C_967), A_965) | ~v1_relat_1(C_967))), inference(resolution, [status(thm)], [c_12084, c_46])).
% 10.40/3.80  tff(c_15846, plain, (![A_965, B_966]: (k1_relset_1(A_965, B_966, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_4', B_966) | ~r1_tarski(k1_relat_1('#skF_5'), A_965) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11882, c_15840])).
% 10.40/3.80  tff(c_15947, plain, (![A_974, B_975]: (k1_relset_1(A_974, B_975, '#skF_5')='#skF_2' | ~r1_tarski('#skF_4', B_975) | ~r1_tarski('#skF_2', A_974))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_12235, c_12235, c_15846])).
% 10.40/3.80  tff(c_15952, plain, (![A_976]: (k1_relset_1(A_976, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_976))), inference(resolution, [status(thm)], [c_12, c_15947])).
% 10.40/3.80  tff(c_15957, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_15952])).
% 10.40/3.80  tff(c_15117, plain, (![C_932, A_933, B_934]: (r1_tarski(C_932, k2_zfmisc_1(A_933, B_934)) | ~r1_tarski(k2_relat_1(C_932), B_934) | ~r1_tarski(k1_relat_1(C_932), A_933) | ~v1_relat_1(C_932))), inference(resolution, [status(thm)], [c_12084, c_22])).
% 10.40/3.80  tff(c_15123, plain, (![A_933, B_934]: (r1_tarski('#skF_5', k2_zfmisc_1(A_933, B_934)) | ~r1_tarski('#skF_4', B_934) | ~r1_tarski(k1_relat_1('#skF_5'), A_933) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11882, c_15117])).
% 10.40/3.80  tff(c_15132, plain, (![A_933, B_934]: (r1_tarski('#skF_5', k2_zfmisc_1(A_933, B_934)) | ~r1_tarski('#skF_4', B_934) | ~r1_tarski('#skF_2', A_933))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_12235, c_15123])).
% 10.40/3.80  tff(c_12273, plain, (![B_779, C_780, A_781]: (k1_xboole_0=B_779 | v1_funct_2(C_780, A_781, B_779) | k1_relset_1(A_781, B_779, C_780)!=A_781 | ~m1_subset_1(C_780, k1_zfmisc_1(k2_zfmisc_1(A_781, B_779))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.40/3.80  tff(c_16376, plain, (![B_995, A_996, A_997]: (k1_xboole_0=B_995 | v1_funct_2(A_996, A_997, B_995) | k1_relset_1(A_997, B_995, A_996)!=A_997 | ~r1_tarski(A_996, k2_zfmisc_1(A_997, B_995)))), inference(resolution, [status(thm)], [c_24, c_12273])).
% 10.40/3.80  tff(c_17068, plain, (![B_1018, A_1019]: (k1_xboole_0=B_1018 | v1_funct_2('#skF_5', A_1019, B_1018) | k1_relset_1(A_1019, B_1018, '#skF_5')!=A_1019 | ~r1_tarski('#skF_4', B_1018) | ~r1_tarski('#skF_2', A_1019))), inference(resolution, [status(thm)], [c_15132, c_16376])).
% 10.40/3.80  tff(c_17077, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_17068, c_145])).
% 10.40/3.80  tff(c_17082, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_15957, c_17077])).
% 10.40/3.80  tff(c_17084, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11883, c_17082])).
% 10.40/3.80  tff(c_17085, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_306])).
% 10.40/3.80  tff(c_126, plain, (![A_47]: (k1_relat_1(A_47)=k1_xboole_0 | ~v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_121, c_4])).
% 10.40/3.80  tff(c_134, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_126])).
% 10.40/3.80  tff(c_17097, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17085, c_17085, c_134])).
% 10.40/3.80  tff(c_307, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_299, c_40])).
% 10.40/3.80  tff(c_11607, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_307])).
% 10.40/3.80  tff(c_17088, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17085, c_11607])).
% 10.40/3.80  tff(c_17150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17097, c_17088])).
% 10.40/3.80  tff(c_17151, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_307])).
% 10.40/3.80  tff(c_17165, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17151, c_119])).
% 10.40/3.80  tff(c_17152, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_307])).
% 10.40/3.80  tff(c_17176, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17151, c_17152])).
% 10.40/3.80  tff(c_17537, plain, (![A_1061, B_1062, C_1063]: (k1_relset_1(A_1061, B_1062, C_1063)=k1_relat_1(C_1063) | ~m1_subset_1(C_1063, k1_zfmisc_1(k2_zfmisc_1(A_1061, B_1062))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.80  tff(c_17553, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_17537])).
% 10.40/3.80  tff(c_17557, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17176, c_17553])).
% 10.40/3.80  tff(c_64, plain, (![B_37, A_36, C_38]: (k1_xboole_0=B_37 | k1_relset_1(A_36, B_37, C_38)=A_36 | ~v1_funct_2(C_38, A_36, B_37) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.40/3.80  tff(c_17898, plain, (![B_1111, A_1112, C_1113]: (B_1111='#skF_5' | k1_relset_1(A_1112, B_1111, C_1113)=A_1112 | ~v1_funct_2(C_1113, A_1112, B_1111) | ~m1_subset_1(C_1113, k1_zfmisc_1(k2_zfmisc_1(A_1112, B_1111))))), inference(demodulation, [status(thm), theory('equality')], [c_17151, c_64])).
% 10.40/3.80  tff(c_17917, plain, ('#skF_5'='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_17898])).
% 10.40/3.80  tff(c_17925, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_17557, c_17917])).
% 10.40/3.80  tff(c_17926, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_17165, c_17925])).
% 10.40/3.80  tff(c_17166, plain, (![B_8]: (k2_zfmisc_1('#skF_5', B_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17151, c_17151, c_20])).
% 10.40/3.80  tff(c_17961, plain, (![B_8]: (k2_zfmisc_1('#skF_2', B_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17926, c_17926, c_17166])).
% 10.40/3.80  tff(c_182, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.40/3.80  tff(c_198, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_182])).
% 10.40/3.80  tff(c_258, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_198, c_244])).
% 10.40/3.80  tff(c_17225, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_258])).
% 10.40/3.80  tff(c_17957, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17926, c_17225])).
% 10.40/3.80  tff(c_18365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_17961, c_17957])).
% 10.40/3.80  tff(c_18366, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_258])).
% 10.40/3.80  tff(c_16, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.40/3.80  tff(c_18919, plain, (![B_1200, A_1201]: (B_1200='#skF_5' | A_1201='#skF_5' | k2_zfmisc_1(A_1201, B_1200)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17151, c_17151, c_17151, c_16])).
% 10.40/3.80  tff(c_18922, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_18366, c_18919])).
% 10.40/3.80  tff(c_18931, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_17165, c_18922])).
% 10.40/3.80  tff(c_18967, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18931, c_18931, c_17176])).
% 10.40/3.80  tff(c_17169, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_17151, c_14])).
% 10.40/3.80  tff(c_18966, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_18931, c_17169])).
% 10.40/3.80  tff(c_18707, plain, (![A_1172, B_1173, C_1174]: (k1_relset_1(A_1172, B_1173, C_1174)=k1_relat_1(C_1174) | ~m1_subset_1(C_1174, k1_zfmisc_1(k2_zfmisc_1(A_1172, B_1173))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.80  tff(c_19669, plain, (![A_1261, B_1262, A_1263]: (k1_relset_1(A_1261, B_1262, A_1263)=k1_relat_1(A_1263) | ~r1_tarski(A_1263, k2_zfmisc_1(A_1261, B_1262)))), inference(resolution, [status(thm)], [c_24, c_18707])).
% 10.40/3.80  tff(c_19679, plain, (![A_1261, B_1262]: (k1_relset_1(A_1261, B_1262, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_18966, c_19669])).
% 10.40/3.80  tff(c_19692, plain, (![A_1261, B_1262]: (k1_relset_1(A_1261, B_1262, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18967, c_19679])).
% 10.40/3.80  tff(c_18416, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18366, c_72])).
% 10.40/3.80  tff(c_18960, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18931, c_18931, c_18416])).
% 10.40/3.80  tff(c_18970, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18931, c_17151])).
% 10.40/3.80  tff(c_58, plain, (![C_38, B_37]: (v1_funct_2(C_38, k1_xboole_0, B_37) | k1_relset_1(k1_xboole_0, B_37, C_38)!=k1_xboole_0 | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_37))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.40/3.80  tff(c_80, plain, (![C_38, B_37]: (v1_funct_2(C_38, k1_xboole_0, B_37) | k1_relset_1(k1_xboole_0, B_37, C_38)!=k1_xboole_0 | ~m1_subset_1(C_38, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_58])).
% 10.40/3.80  tff(c_19040, plain, (![C_38, B_37]: (v1_funct_2(C_38, '#skF_2', B_37) | k1_relset_1('#skF_2', B_37, C_38)!='#skF_2' | ~m1_subset_1(C_38, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18970, c_18970, c_18970, c_18970, c_80])).
% 10.40/3.80  tff(c_19316, plain, (![B_1223]: (v1_funct_2('#skF_2', '#skF_2', B_1223) | k1_relset_1('#skF_2', B_1223, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_18960, c_19040])).
% 10.40/3.80  tff(c_18973, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18931, c_145])).
% 10.40/3.80  tff(c_19325, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_2')!='#skF_2'), inference(resolution, [status(thm)], [c_19316, c_18973])).
% 10.40/3.80  tff(c_19703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19692, c_19325])).
% 10.40/3.80  tff(c_19704, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_78])).
% 10.40/3.80  tff(c_20514, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20491, c_19704])).
% 10.40/3.80  tff(c_20532, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19819, c_20384, c_20514])).
% 10.40/3.80  tff(c_20535, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_20532])).
% 10.40/3.80  tff(c_20539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19819, c_20082, c_20535])).
% 10.40/3.80  tff(c_20541, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_68])).
% 10.40/3.80  tff(c_20540, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_68])).
% 10.40/3.80  tff(c_20551, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20541, c_20540])).
% 10.40/3.80  tff(c_20546, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20540, c_2])).
% 10.40/3.80  tff(c_20556, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20551, c_20546])).
% 10.40/3.80  tff(c_20604, plain, (![A_1364]: (v1_xboole_0(k1_relat_1(A_1364)) | ~v1_xboole_0(A_1364))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.40/3.80  tff(c_20544, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_20540, c_4])).
% 10.40/3.80  tff(c_20597, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_20551, c_20544])).
% 10.40/3.80  tff(c_20610, plain, (![A_1365]: (k1_relat_1(A_1365)='#skF_3' | ~v1_xboole_0(A_1365))), inference(resolution, [status(thm)], [c_20604, c_20597])).
% 10.40/3.80  tff(c_20618, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_20556, c_20610])).
% 10.40/3.80  tff(c_20545, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_20540, c_14])).
% 10.40/3.80  tff(c_20564, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_20551, c_20545])).
% 10.40/3.80  tff(c_20542, plain, (![B_8]: (k2_zfmisc_1('#skF_2', B_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20540, c_20540, c_20])).
% 10.40/3.80  tff(c_20567, plain, (![B_8]: (k2_zfmisc_1('#skF_3', B_8)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20551, c_20551, c_20542])).
% 10.40/3.80  tff(c_20609, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20567, c_20551, c_72])).
% 10.40/3.80  tff(c_20693, plain, (![A_1373, B_1374]: (r1_tarski(A_1373, B_1374) | ~m1_subset_1(A_1373, k1_zfmisc_1(B_1374)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.40/3.80  tff(c_20709, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_20609, c_20693])).
% 10.40/3.80  tff(c_20773, plain, (![B_1381, A_1382]: (B_1381=A_1382 | ~r1_tarski(B_1381, A_1382) | ~r1_tarski(A_1382, B_1381))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.40/3.80  tff(c_20779, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_20709, c_20773])).
% 10.40/3.80  tff(c_20792, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20564, c_20779])).
% 10.40/3.80  tff(c_20802, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20792, c_20609])).
% 10.40/3.80  tff(c_21297, plain, (![A_1448, B_1449, C_1450]: (k1_relset_1(A_1448, B_1449, C_1450)=k1_relat_1(C_1450) | ~m1_subset_1(C_1450, k1_zfmisc_1(k2_zfmisc_1(A_1448, B_1449))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.40/3.80  tff(c_21330, plain, (![B_1452, C_1453]: (k1_relset_1('#skF_3', B_1452, C_1453)=k1_relat_1(C_1453) | ~m1_subset_1(C_1453, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_20567, c_21297])).
% 10.40/3.80  tff(c_21332, plain, (![B_1452]: (k1_relset_1('#skF_3', B_1452, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_20802, c_21330])).
% 10.40/3.80  tff(c_21337, plain, (![B_1452]: (k1_relset_1('#skF_3', B_1452, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20618, c_21332])).
% 10.40/3.80  tff(c_21491, plain, (![C_1474, B_1475]: (v1_funct_2(C_1474, '#skF_3', B_1475) | k1_relset_1('#skF_3', B_1475, C_1474)!='#skF_3' | ~m1_subset_1(C_1474, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_20541, c_20541, c_20541, c_20541, c_80])).
% 10.40/3.80  tff(c_21493, plain, (![B_1475]: (v1_funct_2('#skF_3', '#skF_3', B_1475) | k1_relset_1('#skF_3', B_1475, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_20802, c_21491])).
% 10.40/3.80  tff(c_21499, plain, (![B_1475]: (v1_funct_2('#skF_3', '#skF_3', B_1475))), inference(demodulation, [status(thm), theory('equality')], [c_21337, c_21493])).
% 10.40/3.80  tff(c_20631, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20551, c_20609, c_20567, c_20551, c_78])).
% 10.40/3.80  tff(c_20801, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20792, c_20631])).
% 10.40/3.80  tff(c_21504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21499, c_20801])).
% 10.40/3.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.40/3.80  
% 10.40/3.80  Inference rules
% 10.40/3.80  ----------------------
% 10.40/3.80  #Ref     : 0
% 10.40/3.80  #Sup     : 4645
% 10.40/3.80  #Fact    : 0
% 10.40/3.80  #Define  : 0
% 10.40/3.80  #Split   : 60
% 10.40/3.80  #Chain   : 0
% 10.40/3.80  #Close   : 0
% 10.40/3.80  
% 10.40/3.80  Ordering : KBO
% 10.40/3.80  
% 10.40/3.80  Simplification rules
% 10.40/3.80  ----------------------
% 10.40/3.80  #Subsume      : 1181
% 10.40/3.80  #Demod        : 5119
% 10.40/3.80  #Tautology    : 2331
% 10.40/3.80  #SimpNegUnit  : 141
% 10.40/3.80  #BackRed      : 441
% 10.40/3.80  
% 10.40/3.80  #Partial instantiations: 0
% 10.40/3.80  #Strategies tried      : 1
% 10.40/3.80  
% 10.40/3.80  Timing (in seconds)
% 10.40/3.80  ----------------------
% 10.40/3.80  Preprocessing        : 0.46
% 10.40/3.80  Parsing              : 0.28
% 10.40/3.80  CNF conversion       : 0.02
% 10.40/3.80  Main loop            : 2.48
% 10.40/3.80  Inferencing          : 0.74
% 10.40/3.80  Reduction            : 0.93
% 10.40/3.80  Demodulation         : 0.67
% 10.40/3.80  BG Simplification    : 0.07
% 10.40/3.80  Subsumption          : 0.54
% 10.40/3.80  Abstraction          : 0.10
% 10.40/3.80  MUC search           : 0.00
% 10.40/3.80  Cooper               : 0.00
% 10.40/3.80  Total                : 3.03
% 10.40/3.80  Index Insertion      : 0.00
% 10.40/3.80  Index Deletion       : 0.00
% 10.40/3.80  Index Matching       : 0.00
% 10.40/3.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
