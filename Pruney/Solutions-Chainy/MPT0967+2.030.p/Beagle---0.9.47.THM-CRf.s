%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:17 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 410 expanded)
%              Number of leaves         :   30 ( 142 expanded)
%              Depth                    :    9
%              Number of atoms          :  194 (1298 expanded)
%              Number of equality atoms :   56 ( 473 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_116,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
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

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_20,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_102,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_108,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_102])).

tff(c_112,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_108])).

tff(c_847,plain,(
    ! [C_163,B_164,A_165] :
      ( v5_relat_1(C_163,B_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_862,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_847])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_50,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_831,plain,(
    ! [A_159,C_160,B_161] :
      ( r1_tarski(A_159,C_160)
      | ~ r1_tarski(B_161,C_160)
      | ~ r1_tarski(A_159,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_841,plain,(
    ! [A_162] :
      ( r1_tarski(A_162,'#skF_3')
      | ~ r1_tarski(A_162,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_831])).

tff(c_846,plain,(
    ! [B_12] :
      ( r1_tarski(k2_relat_1(B_12),'#skF_3')
      | ~ v5_relat_1(B_12,'#skF_2')
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_841])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1074,plain,(
    ! [A_212,B_213,C_214] :
      ( k1_relset_1(A_212,B_213,C_214) = k1_relat_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1089,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1074])).

tff(c_1302,plain,(
    ! [B_256,A_257,C_258] :
      ( k1_xboole_0 = B_256
      | k1_relset_1(A_257,B_256,C_258) = A_257
      | ~ v1_funct_2(C_258,A_257,B_256)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_257,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1312,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1302])).

tff(c_1323,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1089,c_1312])).

tff(c_1324,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1323])).

tff(c_40,plain,(
    ! [B_25,A_24] :
      ( m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_25),A_24)))
      | ~ r1_tarski(k2_relat_1(B_25),A_24)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1335,plain,(
    ! [A_24] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_24)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_24)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1324,c_40])).

tff(c_1388,plain,(
    ! [A_261] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_261)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_56,c_1335])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46])).

tff(c_136,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_137,plain,(
    ! [C_40,B_41,A_42] :
      ( v5_relat_1(C_40,B_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_42,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_152,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_137])).

tff(c_201,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(k2_relat_1(B_59),A_60)
      | ~ v5_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_172,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(B_54,C_53)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_178,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,'#skF_3')
      | ~ r1_tarski(A_52,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_172])).

tff(c_223,plain,(
    ! [B_59] :
      ( r1_tarski(k2_relat_1(B_59),'#skF_3')
      | ~ v5_relat_1(B_59,'#skF_2')
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_201,c_178])).

tff(c_390,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_405,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_390])).

tff(c_752,plain,(
    ! [B_153,A_154,C_155] :
      ( k1_xboole_0 = B_153
      | k1_relset_1(A_154,B_153,C_155) = A_154
      | ~ v1_funct_2(C_155,A_154,B_153)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_154,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_762,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_752])).

tff(c_773,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_405,c_762])).

tff(c_774,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_773])).

tff(c_42,plain,(
    ! [B_25,A_24] :
      ( v1_funct_2(B_25,k1_relat_1(B_25),A_24)
      | ~ r1_tarski(k2_relat_1(B_25),A_24)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_788,plain,(
    ! [A_24] :
      ( v1_funct_2('#skF_4','#skF_1',A_24)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_24)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_42])).

tff(c_802,plain,(
    ! [A_156] :
      ( v1_funct_2('#skF_4','#skF_1',A_156)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_56,c_788])).

tff(c_806,plain,
    ( v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_223,c_802])).

tff(c_817,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_152,c_806])).

tff(c_819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_817])).

tff(c_820,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1420,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1388,c_820])).

tff(c_1455,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_846,c_1420])).

tff(c_1462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_862,c_1455])).

tff(c_1463,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_8,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1477,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1463,c_1463,c_8])).

tff(c_1464,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1469,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1463,c_1464])).

tff(c_1476,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_52])).

tff(c_1478,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1477,c_1476])).

tff(c_1865,plain,(
    ! [A_330,B_331,C_332] :
      ( k1_relset_1(A_330,B_331,C_332) = k1_relat_1(C_332)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1909,plain,(
    ! [B_340,C_341] :
      ( k1_relset_1('#skF_1',B_340,C_341) = k1_relat_1(C_341)
      | ~ m1_subset_1(C_341,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1477,c_1865])).

tff(c_1916,plain,(
    ! [B_340] : k1_relset_1('#skF_1',B_340,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1478,c_1909])).

tff(c_32,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_59,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_1963,plain,(
    ! [C_348,B_349] :
      ( v1_funct_2(C_348,'#skF_1',B_349)
      | k1_relset_1('#skF_1',B_349,C_348) != '#skF_1'
      | ~ m1_subset_1(C_348,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1463,c_1463,c_1463,c_1463,c_59])).

tff(c_1968,plain,(
    ! [B_349] :
      ( v1_funct_2('#skF_4','#skF_1',B_349)
      | k1_relset_1('#skF_1',B_349,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_1478,c_1963])).

tff(c_1971,plain,(
    ! [B_349] :
      ( v1_funct_2('#skF_4','#skF_1',B_349)
      | k1_relat_1('#skF_4') != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1916,c_1968])).

tff(c_1972,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1971])).

tff(c_6,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1488,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1463,c_1463,c_6])).

tff(c_1877,plain,(
    ! [A_333,C_334] :
      ( k1_relset_1(A_333,'#skF_1',C_334) = k1_relat_1(C_334)
      | ~ m1_subset_1(C_334,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1488,c_1865])).

tff(c_1884,plain,(
    ! [A_333] : k1_relset_1(A_333,'#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1478,c_1877])).

tff(c_1470,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_54])).

tff(c_36,plain,(
    ! [B_22,C_23] :
      ( k1_relset_1(k1_xboole_0,B_22,C_23) = k1_xboole_0
      | ~ v1_funct_2(C_23,k1_xboole_0,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_60,plain,(
    ! [B_22,C_23] :
      ( k1_relset_1(k1_xboole_0,B_22,C_23) = k1_xboole_0
      | ~ v1_funct_2(C_23,k1_xboole_0,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36])).

tff(c_2125,plain,(
    ! [B_370,C_371] :
      ( k1_relset_1('#skF_1',B_370,C_371) = '#skF_1'
      | ~ v1_funct_2(C_371,'#skF_1',B_370)
      | ~ m1_subset_1(C_371,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1463,c_1463,c_1463,c_1463,c_60])).

tff(c_2127,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1470,c_2125])).

tff(c_2130,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1478,c_1884,c_2127])).

tff(c_2132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1972,c_2130])).

tff(c_2133,plain,(
    ! [B_349] : v1_funct_2('#skF_4','#skF_1',B_349) ),
    inference(splitRight,[status(thm)],[c_1971])).

tff(c_1518,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1478,c_1477,c_58])).

tff(c_2144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2133,c_1518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.17/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.75  
% 4.17/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.17/1.76  
% 4.17/1.76  %Foreground sorts:
% 4.17/1.76  
% 4.17/1.76  
% 4.17/1.76  %Background operators:
% 4.17/1.76  
% 4.17/1.76  
% 4.17/1.76  %Foreground operators:
% 4.17/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.17/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.17/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.17/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.17/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.17/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.17/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.17/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.17/1.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.17/1.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.17/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.17/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.17/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.17/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.17/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.17/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.17/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.17/1.76  
% 4.55/1.80  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.55/1.80  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 4.55/1.80  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.55/1.80  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.55/1.80  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.55/1.80  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.55/1.80  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.55/1.80  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.55/1.80  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.55/1.80  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.55/1.80  tff(c_20, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.55/1.80  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.55/1.80  tff(c_102, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.55/1.80  tff(c_108, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_102])).
% 4.55/1.80  tff(c_112, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_108])).
% 4.55/1.80  tff(c_847, plain, (![C_163, B_164, A_165]: (v5_relat_1(C_163, B_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.55/1.80  tff(c_862, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_847])).
% 4.55/1.80  tff(c_18, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.55/1.80  tff(c_50, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.55/1.80  tff(c_831, plain, (![A_159, C_160, B_161]: (r1_tarski(A_159, C_160) | ~r1_tarski(B_161, C_160) | ~r1_tarski(A_159, B_161))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/1.80  tff(c_841, plain, (![A_162]: (r1_tarski(A_162, '#skF_3') | ~r1_tarski(A_162, '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_831])).
% 4.55/1.80  tff(c_846, plain, (![B_12]: (r1_tarski(k2_relat_1(B_12), '#skF_3') | ~v5_relat_1(B_12, '#skF_2') | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_18, c_841])).
% 4.55/1.80  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.55/1.80  tff(c_48, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.55/1.80  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_48])).
% 4.55/1.80  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.55/1.80  tff(c_1074, plain, (![A_212, B_213, C_214]: (k1_relset_1(A_212, B_213, C_214)=k1_relat_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.55/1.80  tff(c_1089, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1074])).
% 4.55/1.80  tff(c_1302, plain, (![B_256, A_257, C_258]: (k1_xboole_0=B_256 | k1_relset_1(A_257, B_256, C_258)=A_257 | ~v1_funct_2(C_258, A_257, B_256) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_257, B_256))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.55/1.80  tff(c_1312, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_1302])).
% 4.55/1.80  tff(c_1323, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1089, c_1312])).
% 4.55/1.80  tff(c_1324, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_1323])).
% 4.55/1.80  tff(c_40, plain, (![B_25, A_24]: (m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_25), A_24))) | ~r1_tarski(k2_relat_1(B_25), A_24) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.55/1.80  tff(c_1335, plain, (![A_24]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_24))) | ~r1_tarski(k2_relat_1('#skF_4'), A_24) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1324, c_40])).
% 4.55/1.80  tff(c_1388, plain, (![A_261]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_261))) | ~r1_tarski(k2_relat_1('#skF_4'), A_261))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_56, c_1335])).
% 4.55/1.80  tff(c_46, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.55/1.80  tff(c_58, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46])).
% 4.55/1.80  tff(c_136, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 4.55/1.80  tff(c_137, plain, (![C_40, B_41, A_42]: (v5_relat_1(C_40, B_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_42, B_41))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.55/1.80  tff(c_152, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_137])).
% 4.55/1.80  tff(c_201, plain, (![B_59, A_60]: (r1_tarski(k2_relat_1(B_59), A_60) | ~v5_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.55/1.80  tff(c_172, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(B_54, C_53) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/1.80  tff(c_178, plain, (![A_52]: (r1_tarski(A_52, '#skF_3') | ~r1_tarski(A_52, '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_172])).
% 4.55/1.80  tff(c_223, plain, (![B_59]: (r1_tarski(k2_relat_1(B_59), '#skF_3') | ~v5_relat_1(B_59, '#skF_2') | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_201, c_178])).
% 4.55/1.80  tff(c_390, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.55/1.80  tff(c_405, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_390])).
% 4.55/1.80  tff(c_752, plain, (![B_153, A_154, C_155]: (k1_xboole_0=B_153 | k1_relset_1(A_154, B_153, C_155)=A_154 | ~v1_funct_2(C_155, A_154, B_153) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_154, B_153))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.55/1.80  tff(c_762, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_752])).
% 4.55/1.80  tff(c_773, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_405, c_762])).
% 4.55/1.80  tff(c_774, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_773])).
% 4.55/1.80  tff(c_42, plain, (![B_25, A_24]: (v1_funct_2(B_25, k1_relat_1(B_25), A_24) | ~r1_tarski(k2_relat_1(B_25), A_24) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.55/1.80  tff(c_788, plain, (![A_24]: (v1_funct_2('#skF_4', '#skF_1', A_24) | ~r1_tarski(k2_relat_1('#skF_4'), A_24) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_774, c_42])).
% 4.55/1.80  tff(c_802, plain, (![A_156]: (v1_funct_2('#skF_4', '#skF_1', A_156) | ~r1_tarski(k2_relat_1('#skF_4'), A_156))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_56, c_788])).
% 4.55/1.80  tff(c_806, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_223, c_802])).
% 4.55/1.80  tff(c_817, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_152, c_806])).
% 4.55/1.80  tff(c_819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_817])).
% 4.55/1.80  tff(c_820, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_58])).
% 4.55/1.80  tff(c_1420, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1388, c_820])).
% 4.55/1.80  tff(c_1455, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_846, c_1420])).
% 4.55/1.80  tff(c_1462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_862, c_1455])).
% 4.55/1.80  tff(c_1463, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_48])).
% 4.55/1.80  tff(c_8, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/1.80  tff(c_1477, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1463, c_1463, c_8])).
% 4.55/1.80  tff(c_1464, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 4.55/1.80  tff(c_1469, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1463, c_1464])).
% 4.55/1.80  tff(c_1476, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_52])).
% 4.55/1.80  tff(c_1478, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1477, c_1476])).
% 4.55/1.80  tff(c_1865, plain, (![A_330, B_331, C_332]: (k1_relset_1(A_330, B_331, C_332)=k1_relat_1(C_332) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.55/1.80  tff(c_1909, plain, (![B_340, C_341]: (k1_relset_1('#skF_1', B_340, C_341)=k1_relat_1(C_341) | ~m1_subset_1(C_341, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1477, c_1865])).
% 4.55/1.80  tff(c_1916, plain, (![B_340]: (k1_relset_1('#skF_1', B_340, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1478, c_1909])).
% 4.55/1.80  tff(c_32, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.55/1.80  tff(c_59, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 4.55/1.80  tff(c_1963, plain, (![C_348, B_349]: (v1_funct_2(C_348, '#skF_1', B_349) | k1_relset_1('#skF_1', B_349, C_348)!='#skF_1' | ~m1_subset_1(C_348, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1463, c_1463, c_1463, c_1463, c_59])).
% 4.55/1.80  tff(c_1968, plain, (![B_349]: (v1_funct_2('#skF_4', '#skF_1', B_349) | k1_relset_1('#skF_1', B_349, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_1478, c_1963])).
% 4.55/1.80  tff(c_1971, plain, (![B_349]: (v1_funct_2('#skF_4', '#skF_1', B_349) | k1_relat_1('#skF_4')!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1916, c_1968])).
% 4.55/1.80  tff(c_1972, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1971])).
% 4.55/1.80  tff(c_6, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/1.80  tff(c_1488, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1463, c_1463, c_6])).
% 4.55/1.80  tff(c_1877, plain, (![A_333, C_334]: (k1_relset_1(A_333, '#skF_1', C_334)=k1_relat_1(C_334) | ~m1_subset_1(C_334, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1488, c_1865])).
% 4.55/1.80  tff(c_1884, plain, (![A_333]: (k1_relset_1(A_333, '#skF_1', '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1478, c_1877])).
% 4.55/1.80  tff(c_1470, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_54])).
% 4.55/1.80  tff(c_36, plain, (![B_22, C_23]: (k1_relset_1(k1_xboole_0, B_22, C_23)=k1_xboole_0 | ~v1_funct_2(C_23, k1_xboole_0, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.55/1.80  tff(c_60, plain, (![B_22, C_23]: (k1_relset_1(k1_xboole_0, B_22, C_23)=k1_xboole_0 | ~v1_funct_2(C_23, k1_xboole_0, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36])).
% 4.55/1.80  tff(c_2125, plain, (![B_370, C_371]: (k1_relset_1('#skF_1', B_370, C_371)='#skF_1' | ~v1_funct_2(C_371, '#skF_1', B_370) | ~m1_subset_1(C_371, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1463, c_1463, c_1463, c_1463, c_60])).
% 4.55/1.80  tff(c_2127, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_1470, c_2125])).
% 4.55/1.80  tff(c_2130, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1478, c_1884, c_2127])).
% 4.55/1.80  tff(c_2132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1972, c_2130])).
% 4.55/1.80  tff(c_2133, plain, (![B_349]: (v1_funct_2('#skF_4', '#skF_1', B_349))), inference(splitRight, [status(thm)], [c_1971])).
% 4.55/1.80  tff(c_1518, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1478, c_1477, c_58])).
% 4.55/1.80  tff(c_2144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2133, c_1518])).
% 4.55/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.80  
% 4.55/1.80  Inference rules
% 4.55/1.80  ----------------------
% 4.55/1.80  #Ref     : 0
% 4.55/1.80  #Sup     : 451
% 4.55/1.80  #Fact    : 0
% 4.55/1.80  #Define  : 0
% 4.55/1.80  #Split   : 22
% 4.55/1.80  #Chain   : 0
% 4.55/1.80  #Close   : 0
% 4.55/1.80  
% 4.55/1.80  Ordering : KBO
% 4.55/1.80  
% 4.55/1.80  Simplification rules
% 4.55/1.80  ----------------------
% 4.55/1.80  #Subsume      : 163
% 4.55/1.80  #Demod        : 152
% 4.55/1.80  #Tautology    : 97
% 4.55/1.80  #SimpNegUnit  : 43
% 4.55/1.80  #BackRed      : 30
% 4.55/1.80  
% 4.55/1.80  #Partial instantiations: 0
% 4.55/1.80  #Strategies tried      : 1
% 4.55/1.80  
% 4.55/1.80  Timing (in seconds)
% 4.55/1.80  ----------------------
% 4.65/1.80  Preprocessing        : 0.33
% 4.65/1.80  Parsing              : 0.17
% 4.65/1.80  CNF conversion       : 0.02
% 4.65/1.80  Main loop            : 0.66
% 4.65/1.80  Inferencing          : 0.26
% 4.65/1.80  Reduction            : 0.19
% 4.65/1.80  Demodulation         : 0.12
% 4.65/1.80  BG Simplification    : 0.03
% 4.65/1.80  Subsumption          : 0.13
% 4.65/1.80  Abstraction          : 0.03
% 4.65/1.80  MUC search           : 0.00
% 4.65/1.80  Cooper               : 0.00
% 4.65/1.80  Total                : 1.06
% 4.65/1.81  Index Insertion      : 0.00
% 4.65/1.81  Index Deletion       : 0.00
% 4.65/1.81  Index Matching       : 0.00
% 4.65/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
