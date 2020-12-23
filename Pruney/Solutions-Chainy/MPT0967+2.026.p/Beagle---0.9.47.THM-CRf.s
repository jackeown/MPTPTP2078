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
% DateTime   : Thu Dec  3 10:11:16 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 432 expanded)
%              Number of leaves         :   44 ( 155 expanded)
%              Depth                    :   10
%              Number of atoms          :  256 (1261 expanded)
%              Number of equality atoms :   52 ( 411 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_188,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v5_relat_1(C,A) )
         => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_168,axiom,(
    ! [A,B,C,D] :
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

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_149,axiom,(
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

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_40,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_98,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_196,plain,(
    ! [B_82,A_83] :
      ( v1_relat_1(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_202,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_98,c_196])).

tff(c_212,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_202])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_5212,plain,(
    ! [C_371,B_372,A_373] :
      ( v5_relat_1(C_371,B_372)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_373,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5231,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_5212])).

tff(c_6013,plain,(
    ! [C_450,B_451,A_452] :
      ( v5_relat_1(C_450,B_451)
      | ~ v5_relat_1(C_450,A_452)
      | ~ v1_relat_1(C_450)
      | ~ r1_tarski(A_452,B_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6025,plain,(
    ! [B_451] :
      ( v5_relat_1('#skF_6',B_451)
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_4',B_451) ) ),
    inference(resolution,[status(thm)],[c_5231,c_6013])).

tff(c_6043,plain,(
    ! [B_453] :
      ( v5_relat_1('#skF_6',B_453)
      | ~ r1_tarski('#skF_4',B_453) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_6025])).

tff(c_48,plain,(
    ! [C_36,B_34,A_33] :
      ( v5_relat_1(C_36,B_34)
      | ~ v5_relat_1(C_36,A_33)
      | ~ v1_relat_1(C_36)
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6045,plain,(
    ! [B_34,B_453] :
      ( v5_relat_1('#skF_6',B_34)
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski(B_453,B_34)
      | ~ r1_tarski('#skF_4',B_453) ) ),
    inference(resolution,[status(thm)],[c_6043,c_48])).

tff(c_7113,plain,(
    ! [B_505,B_506] :
      ( v5_relat_1('#skF_6',B_505)
      | ~ r1_tarski(B_506,B_505)
      | ~ r1_tarski('#skF_4',B_506) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_6045])).

tff(c_7137,plain,
    ( v5_relat_1('#skF_6','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_7113])).

tff(c_7151,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7137])).

tff(c_38,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_94,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_130,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_102,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_100,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_6894,plain,(
    ! [A_497,B_498,C_499] :
      ( k2_relset_1(A_497,B_498,C_499) = k2_relat_1(C_499)
      | ~ m1_subset_1(C_499,k1_zfmisc_1(k2_zfmisc_1(A_497,B_498))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6925,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_98,c_6894])).

tff(c_9875,plain,(
    ! [B_637,D_638,A_639,C_640] :
      ( k1_xboole_0 = B_637
      | m1_subset_1(D_638,k1_zfmisc_1(k2_zfmisc_1(A_639,C_640)))
      | ~ r1_tarski(k2_relset_1(A_639,B_637,D_638),C_640)
      | ~ m1_subset_1(D_638,k1_zfmisc_1(k2_zfmisc_1(A_639,B_637)))
      | ~ v1_funct_2(D_638,A_639,B_637)
      | ~ v1_funct_1(D_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_9879,plain,(
    ! [C_640] :
      ( k1_xboole_0 = '#skF_4'
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',C_640)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_640)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6925,c_9875])).

tff(c_9892,plain,(
    ! [C_640] :
      ( k1_xboole_0 = '#skF_4'
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',C_640)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_640) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_9879])).

tff(c_9911,plain,(
    ! [C_641] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',C_641)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_641) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_9892])).

tff(c_92,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_104,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_92])).

tff(c_223,plain,(
    ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_179,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,B_81)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_193,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_98,c_179])).

tff(c_440,plain,(
    ! [A_114,C_115,B_116] :
      ( r1_tarski(A_114,C_115)
      | ~ r1_tarski(B_116,C_115)
      | ~ r1_tarski(A_114,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_452,plain,(
    ! [A_114] :
      ( r1_tarski(A_114,k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_114,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_193,c_440])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_561,plain,(
    ! [C_127,B_128,A_129] :
      ( v5_relat_1(C_127,B_128)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_625,plain,(
    ! [A_137,B_138,A_139] :
      ( v5_relat_1(A_137,B_138)
      | ~ r1_tarski(A_137,k2_zfmisc_1(A_139,B_138)) ) ),
    inference(resolution,[status(thm)],[c_30,c_561])).

tff(c_650,plain,(
    ! [A_114] :
      ( v5_relat_1(A_114,'#skF_4')
      | ~ r1_tarski(A_114,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_452,c_625])).

tff(c_471,plain,(
    ! [A_119] :
      ( r1_tarski(A_119,'#skF_5')
      | ~ r1_tarski(A_119,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_96,c_440])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_707,plain,(
    ! [A_148,A_149] :
      ( r1_tarski(A_148,'#skF_5')
      | ~ r1_tarski(A_148,A_149)
      | ~ r1_tarski(A_149,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_471,c_8])).

tff(c_4843,plain,(
    ! [B_352,A_353] :
      ( r1_tarski(k2_relat_1(B_352),'#skF_5')
      | ~ r1_tarski(A_353,'#skF_4')
      | ~ v5_relat_1(B_352,A_353)
      | ~ v1_relat_1(B_352) ) ),
    inference(resolution,[status(thm)],[c_38,c_707])).

tff(c_4869,plain,(
    ! [A_114] :
      ( r1_tarski(k2_relat_1(A_114),'#skF_5')
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ v1_relat_1(A_114)
      | ~ r1_tarski(A_114,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_650,c_4843])).

tff(c_4912,plain,(
    ! [A_114] :
      ( r1_tarski(k2_relat_1(A_114),'#skF_5')
      | ~ v1_relat_1(A_114)
      | ~ r1_tarski(A_114,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4869])).

tff(c_1530,plain,(
    ! [A_208,B_209,C_210] :
      ( k2_relset_1(A_208,B_209,C_210) = k2_relat_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1549,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_98,c_1530])).

tff(c_5059,plain,(
    ! [B_356,D_357,A_358,C_359] :
      ( k1_xboole_0 = B_356
      | v1_funct_2(D_357,A_358,C_359)
      | ~ r1_tarski(k2_relset_1(A_358,B_356,D_357),C_359)
      | ~ m1_subset_1(D_357,k1_zfmisc_1(k2_zfmisc_1(A_358,B_356)))
      | ~ v1_funct_2(D_357,A_358,B_356)
      | ~ v1_funct_1(D_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_5063,plain,(
    ! [C_359] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_6','#skF_3',C_359)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_359)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1549,c_5059])).

tff(c_5076,plain,(
    ! [C_359] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_6','#skF_3',C_359)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_5063])).

tff(c_5083,plain,(
    ! [C_360] :
      ( v1_funct_2('#skF_6','#skF_3',C_360)
      | ~ r1_tarski(k2_relat_1('#skF_6'),C_360) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_5076])).

tff(c_5087,plain,
    ( v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v1_relat_1('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_4912,c_5083])).

tff(c_5113,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_212,c_5087])).

tff(c_5115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_5113])).

tff(c_5116,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_9970,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_9911,c_5116])).

tff(c_9987,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_9970])).

tff(c_9995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_7151,c_9987])).

tff(c_9997,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_24,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10046,plain,(
    k1_zfmisc_1('#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9997,c_9997,c_24])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10052,plain,(
    ! [A_648] : m1_subset_1('#skF_4',k1_zfmisc_1(A_648)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9997,c_26])).

tff(c_10054,plain,(
    m1_subset_1('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10046,c_10052])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10035,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9997,c_9997,c_14])).

tff(c_10074,plain,(
    ! [A_650,B_651] : ~ r2_hidden(A_650,k2_zfmisc_1(A_650,B_651)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10080,plain,(
    ! [A_7] : ~ r2_hidden(A_7,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10035,c_10074])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10055,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_4',B_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9997,c_9997,c_16])).

tff(c_11070,plain,(
    ! [A_772,B_773,C_774] :
      ( r2_hidden('#skF_1'(A_772,B_773,C_774),B_773)
      | k1_relset_1(B_773,A_772,C_774) = B_773
      | ~ m1_subset_1(C_774,k1_zfmisc_1(k2_zfmisc_1(B_773,A_772))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_11075,plain,(
    ! [B_8,C_774] :
      ( r2_hidden('#skF_1'(B_8,'#skF_4',C_774),'#skF_4')
      | k1_relset_1('#skF_4',B_8,C_774) = '#skF_4'
      | ~ m1_subset_1(C_774,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10055,c_11070])).

tff(c_11082,plain,(
    ! [B_8,C_774] :
      ( r2_hidden('#skF_1'(B_8,'#skF_4',C_774),'#skF_4')
      | k1_relset_1('#skF_4',B_8,C_774) = '#skF_4'
      | ~ m1_subset_1(C_774,k1_tarski('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10046,c_11075])).

tff(c_11087,plain,(
    ! [B_778,C_779] :
      ( k1_relset_1('#skF_4',B_778,C_779) = '#skF_4'
      | ~ m1_subset_1(C_779,k1_tarski('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10080,c_11082])).

tff(c_11093,plain,(
    ! [B_778] : k1_relset_1('#skF_4',B_778,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10054,c_11087])).

tff(c_72,plain,(
    ! [C_60,B_59] :
      ( v1_funct_2(C_60,k1_xboole_0,B_59)
      | k1_relset_1(k1_xboole_0,B_59,C_60) != k1_xboole_0
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_109,plain,(
    ! [C_60,B_59] :
      ( v1_funct_2(C_60,k1_xboole_0,B_59)
      | k1_relset_1(k1_xboole_0,B_59,C_60) != k1_xboole_0
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_72])).

tff(c_113,plain,(
    ! [C_60,B_59] :
      ( v1_funct_2(C_60,k1_xboole_0,B_59)
      | k1_relset_1(k1_xboole_0,B_59,C_60) != k1_xboole_0
      | ~ m1_subset_1(C_60,k1_tarski(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_109])).

tff(c_11095,plain,(
    ! [C_780,B_781] :
      ( v1_funct_2(C_780,'#skF_4',B_781)
      | k1_relset_1('#skF_4',B_781,C_780) != '#skF_4'
      | ~ m1_subset_1(C_780,k1_tarski('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9997,c_9997,c_9997,c_9997,c_113])).

tff(c_11101,plain,(
    ! [B_781] :
      ( v1_funct_2('#skF_4','#skF_4',B_781)
      | k1_relset_1('#skF_4',B_781,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_10054,c_11095])).

tff(c_11261,plain,(
    ! [B_781] : v1_funct_2('#skF_4','#skF_4',B_781) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11093,c_11101])).

tff(c_9996,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_10007,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9997,c_9996])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10002,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9996,c_10])).

tff(c_10027,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10007,c_10002])).

tff(c_10012,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10007,c_98])).

tff(c_10082,plain,(
    m1_subset_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10046,c_10035,c_10012])).

tff(c_10085,plain,(
    ! [A_654,B_655] :
      ( r1_tarski(A_654,B_655)
      | ~ m1_subset_1(A_654,k1_zfmisc_1(B_655)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10102,plain,(
    ! [A_658] :
      ( r1_tarski(A_658,'#skF_4')
      | ~ m1_subset_1(A_658,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10046,c_10085])).

tff(c_10109,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_10082,c_10102])).

tff(c_10112,plain,(
    ! [B_659,A_660] :
      ( B_659 = A_660
      | ~ r1_tarski(B_659,A_660)
      | ~ r1_tarski(A_660,B_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10114,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_10109,c_10112])).

tff(c_10121,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10027,c_10114])).

tff(c_10138,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10121,c_10007,c_10054,c_10121,c_10046,c_10055,c_10007,c_104])).

tff(c_11265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11261,c_10138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.41/2.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.59  
% 7.41/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 7.41/2.59  
% 7.41/2.59  %Foreground sorts:
% 7.41/2.59  
% 7.41/2.59  
% 7.41/2.59  %Background operators:
% 7.41/2.59  
% 7.41/2.59  
% 7.41/2.59  %Foreground operators:
% 7.41/2.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.41/2.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.41/2.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.41/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.41/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.41/2.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.41/2.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.41/2.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.41/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.41/2.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.41/2.59  tff('#skF_5', type, '#skF_5': $i).
% 7.41/2.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.41/2.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.41/2.59  tff('#skF_6', type, '#skF_6': $i).
% 7.41/2.59  tff('#skF_3', type, '#skF_3': $i).
% 7.41/2.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.41/2.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.41/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.41/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.41/2.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.41/2.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.41/2.59  tff('#skF_4', type, '#skF_4': $i).
% 7.41/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.41/2.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.41/2.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.41/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.41/2.59  
% 7.41/2.61  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.41/2.61  tff(f_188, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 7.41/2.61  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.41/2.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.41/2.61  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.41/2.61  tff(f_104, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t218_relat_1)).
% 7.41/2.61  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.41/2.61  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.41/2.61  tff(f_168, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 7.41/2.61  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.41/2.61  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.41/2.61  tff(f_55, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 7.41/2.61  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.41/2.61  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.41/2.61  tff(f_54, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 7.41/2.61  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 7.41/2.61  tff(f_149, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.41/2.61  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.41/2.61  tff(c_40, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.41/2.61  tff(c_98, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.41/2.61  tff(c_196, plain, (![B_82, A_83]: (v1_relat_1(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.41/2.61  tff(c_202, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_98, c_196])).
% 7.41/2.61  tff(c_212, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_202])).
% 7.41/2.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.41/2.61  tff(c_96, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.41/2.61  tff(c_5212, plain, (![C_371, B_372, A_373]: (v5_relat_1(C_371, B_372) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_373, B_372))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.41/2.61  tff(c_5231, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_98, c_5212])).
% 7.41/2.61  tff(c_6013, plain, (![C_450, B_451, A_452]: (v5_relat_1(C_450, B_451) | ~v5_relat_1(C_450, A_452) | ~v1_relat_1(C_450) | ~r1_tarski(A_452, B_451))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.41/2.61  tff(c_6025, plain, (![B_451]: (v5_relat_1('#skF_6', B_451) | ~v1_relat_1('#skF_6') | ~r1_tarski('#skF_4', B_451))), inference(resolution, [status(thm)], [c_5231, c_6013])).
% 7.41/2.61  tff(c_6043, plain, (![B_453]: (v5_relat_1('#skF_6', B_453) | ~r1_tarski('#skF_4', B_453))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_6025])).
% 7.41/2.61  tff(c_48, plain, (![C_36, B_34, A_33]: (v5_relat_1(C_36, B_34) | ~v5_relat_1(C_36, A_33) | ~v1_relat_1(C_36) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.41/2.61  tff(c_6045, plain, (![B_34, B_453]: (v5_relat_1('#skF_6', B_34) | ~v1_relat_1('#skF_6') | ~r1_tarski(B_453, B_34) | ~r1_tarski('#skF_4', B_453))), inference(resolution, [status(thm)], [c_6043, c_48])).
% 7.41/2.61  tff(c_7113, plain, (![B_505, B_506]: (v5_relat_1('#skF_6', B_505) | ~r1_tarski(B_506, B_505) | ~r1_tarski('#skF_4', B_506))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_6045])).
% 7.41/2.61  tff(c_7137, plain, (v5_relat_1('#skF_6', '#skF_5') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_96, c_7113])).
% 7.41/2.61  tff(c_7151, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7137])).
% 7.41/2.61  tff(c_38, plain, (![B_24, A_23]: (r1_tarski(k2_relat_1(B_24), A_23) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.41/2.61  tff(c_94, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.41/2.61  tff(c_130, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_94])).
% 7.41/2.61  tff(c_102, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.41/2.61  tff(c_100, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.41/2.61  tff(c_6894, plain, (![A_497, B_498, C_499]: (k2_relset_1(A_497, B_498, C_499)=k2_relat_1(C_499) | ~m1_subset_1(C_499, k1_zfmisc_1(k2_zfmisc_1(A_497, B_498))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.41/2.61  tff(c_6925, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_98, c_6894])).
% 7.41/2.61  tff(c_9875, plain, (![B_637, D_638, A_639, C_640]: (k1_xboole_0=B_637 | m1_subset_1(D_638, k1_zfmisc_1(k2_zfmisc_1(A_639, C_640))) | ~r1_tarski(k2_relset_1(A_639, B_637, D_638), C_640) | ~m1_subset_1(D_638, k1_zfmisc_1(k2_zfmisc_1(A_639, B_637))) | ~v1_funct_2(D_638, A_639, B_637) | ~v1_funct_1(D_638))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.41/2.61  tff(c_9879, plain, (![C_640]: (k1_xboole_0='#skF_4' | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', C_640))) | ~r1_tarski(k2_relat_1('#skF_6'), C_640) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6925, c_9875])).
% 7.41/2.61  tff(c_9892, plain, (![C_640]: (k1_xboole_0='#skF_4' | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', C_640))) | ~r1_tarski(k2_relat_1('#skF_6'), C_640))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_9879])).
% 7.41/2.61  tff(c_9911, plain, (![C_641]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', C_641))) | ~r1_tarski(k2_relat_1('#skF_6'), C_641))), inference(negUnitSimplification, [status(thm)], [c_130, c_9892])).
% 7.41/2.61  tff(c_92, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.41/2.61  tff(c_104, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_92])).
% 7.41/2.61  tff(c_223, plain, (~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_104])).
% 7.41/2.61  tff(c_179, plain, (![A_80, B_81]: (r1_tarski(A_80, B_81) | ~m1_subset_1(A_80, k1_zfmisc_1(B_81)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.41/2.61  tff(c_193, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_98, c_179])).
% 7.41/2.61  tff(c_440, plain, (![A_114, C_115, B_116]: (r1_tarski(A_114, C_115) | ~r1_tarski(B_116, C_115) | ~r1_tarski(A_114, B_116))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.41/2.61  tff(c_452, plain, (![A_114]: (r1_tarski(A_114, k2_zfmisc_1('#skF_3', '#skF_4')) | ~r1_tarski(A_114, '#skF_6'))), inference(resolution, [status(thm)], [c_193, c_440])).
% 7.41/2.61  tff(c_30, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.41/2.61  tff(c_561, plain, (![C_127, B_128, A_129]: (v5_relat_1(C_127, B_128) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.41/2.61  tff(c_625, plain, (![A_137, B_138, A_139]: (v5_relat_1(A_137, B_138) | ~r1_tarski(A_137, k2_zfmisc_1(A_139, B_138)))), inference(resolution, [status(thm)], [c_30, c_561])).
% 7.41/2.61  tff(c_650, plain, (![A_114]: (v5_relat_1(A_114, '#skF_4') | ~r1_tarski(A_114, '#skF_6'))), inference(resolution, [status(thm)], [c_452, c_625])).
% 7.41/2.61  tff(c_471, plain, (![A_119]: (r1_tarski(A_119, '#skF_5') | ~r1_tarski(A_119, '#skF_4'))), inference(resolution, [status(thm)], [c_96, c_440])).
% 7.41/2.61  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.41/2.61  tff(c_707, plain, (![A_148, A_149]: (r1_tarski(A_148, '#skF_5') | ~r1_tarski(A_148, A_149) | ~r1_tarski(A_149, '#skF_4'))), inference(resolution, [status(thm)], [c_471, c_8])).
% 7.41/2.61  tff(c_4843, plain, (![B_352, A_353]: (r1_tarski(k2_relat_1(B_352), '#skF_5') | ~r1_tarski(A_353, '#skF_4') | ~v5_relat_1(B_352, A_353) | ~v1_relat_1(B_352))), inference(resolution, [status(thm)], [c_38, c_707])).
% 7.41/2.61  tff(c_4869, plain, (![A_114]: (r1_tarski(k2_relat_1(A_114), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1(A_114) | ~r1_tarski(A_114, '#skF_6'))), inference(resolution, [status(thm)], [c_650, c_4843])).
% 7.41/2.61  tff(c_4912, plain, (![A_114]: (r1_tarski(k2_relat_1(A_114), '#skF_5') | ~v1_relat_1(A_114) | ~r1_tarski(A_114, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4869])).
% 7.41/2.61  tff(c_1530, plain, (![A_208, B_209, C_210]: (k2_relset_1(A_208, B_209, C_210)=k2_relat_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.41/2.61  tff(c_1549, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_98, c_1530])).
% 7.41/2.61  tff(c_5059, plain, (![B_356, D_357, A_358, C_359]: (k1_xboole_0=B_356 | v1_funct_2(D_357, A_358, C_359) | ~r1_tarski(k2_relset_1(A_358, B_356, D_357), C_359) | ~m1_subset_1(D_357, k1_zfmisc_1(k2_zfmisc_1(A_358, B_356))) | ~v1_funct_2(D_357, A_358, B_356) | ~v1_funct_1(D_357))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.41/2.61  tff(c_5063, plain, (![C_359]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_6', '#skF_3', C_359) | ~r1_tarski(k2_relat_1('#skF_6'), C_359) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1549, c_5059])).
% 7.41/2.61  tff(c_5076, plain, (![C_359]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_6', '#skF_3', C_359) | ~r1_tarski(k2_relat_1('#skF_6'), C_359))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_5063])).
% 7.41/2.61  tff(c_5083, plain, (![C_360]: (v1_funct_2('#skF_6', '#skF_3', C_360) | ~r1_tarski(k2_relat_1('#skF_6'), C_360))), inference(negUnitSimplification, [status(thm)], [c_130, c_5076])).
% 7.41/2.61  tff(c_5087, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v1_relat_1('#skF_6') | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_4912, c_5083])).
% 7.41/2.61  tff(c_5113, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_212, c_5087])).
% 7.41/2.61  tff(c_5115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_5113])).
% 7.41/2.61  tff(c_5116, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_104])).
% 7.41/2.61  tff(c_9970, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_9911, c_5116])).
% 7.41/2.61  tff(c_9987, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_9970])).
% 7.41/2.61  tff(c_9995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_212, c_7151, c_9987])).
% 7.41/2.61  tff(c_9997, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_94])).
% 7.41/2.61  tff(c_24, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.41/2.61  tff(c_10046, plain, (k1_zfmisc_1('#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9997, c_9997, c_24])).
% 7.41/2.61  tff(c_26, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.41/2.61  tff(c_10052, plain, (![A_648]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_648)))), inference(demodulation, [status(thm), theory('equality')], [c_9997, c_26])).
% 7.41/2.61  tff(c_10054, plain, (m1_subset_1('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10046, c_10052])).
% 7.41/2.61  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.41/2.61  tff(c_10035, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9997, c_9997, c_14])).
% 7.41/2.61  tff(c_10074, plain, (![A_650, B_651]: (~r2_hidden(A_650, k2_zfmisc_1(A_650, B_651)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.41/2.61  tff(c_10080, plain, (![A_7]: (~r2_hidden(A_7, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10035, c_10074])).
% 7.41/2.61  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.41/2.61  tff(c_10055, plain, (![B_8]: (k2_zfmisc_1('#skF_4', B_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9997, c_9997, c_16])).
% 7.41/2.61  tff(c_11070, plain, (![A_772, B_773, C_774]: (r2_hidden('#skF_1'(A_772, B_773, C_774), B_773) | k1_relset_1(B_773, A_772, C_774)=B_773 | ~m1_subset_1(C_774, k1_zfmisc_1(k2_zfmisc_1(B_773, A_772))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.41/2.61  tff(c_11075, plain, (![B_8, C_774]: (r2_hidden('#skF_1'(B_8, '#skF_4', C_774), '#skF_4') | k1_relset_1('#skF_4', B_8, C_774)='#skF_4' | ~m1_subset_1(C_774, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_10055, c_11070])).
% 7.41/2.61  tff(c_11082, plain, (![B_8, C_774]: (r2_hidden('#skF_1'(B_8, '#skF_4', C_774), '#skF_4') | k1_relset_1('#skF_4', B_8, C_774)='#skF_4' | ~m1_subset_1(C_774, k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10046, c_11075])).
% 7.41/2.61  tff(c_11087, plain, (![B_778, C_779]: (k1_relset_1('#skF_4', B_778, C_779)='#skF_4' | ~m1_subset_1(C_779, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_10080, c_11082])).
% 7.41/2.61  tff(c_11093, plain, (![B_778]: (k1_relset_1('#skF_4', B_778, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_10054, c_11087])).
% 7.41/2.61  tff(c_72, plain, (![C_60, B_59]: (v1_funct_2(C_60, k1_xboole_0, B_59) | k1_relset_1(k1_xboole_0, B_59, C_60)!=k1_xboole_0 | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_59))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.41/2.61  tff(c_109, plain, (![C_60, B_59]: (v1_funct_2(C_60, k1_xboole_0, B_59) | k1_relset_1(k1_xboole_0, B_59, C_60)!=k1_xboole_0 | ~m1_subset_1(C_60, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_72])).
% 7.41/2.61  tff(c_113, plain, (![C_60, B_59]: (v1_funct_2(C_60, k1_xboole_0, B_59) | k1_relset_1(k1_xboole_0, B_59, C_60)!=k1_xboole_0 | ~m1_subset_1(C_60, k1_tarski(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_109])).
% 7.41/2.61  tff(c_11095, plain, (![C_780, B_781]: (v1_funct_2(C_780, '#skF_4', B_781) | k1_relset_1('#skF_4', B_781, C_780)!='#skF_4' | ~m1_subset_1(C_780, k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9997, c_9997, c_9997, c_9997, c_113])).
% 7.41/2.61  tff(c_11101, plain, (![B_781]: (v1_funct_2('#skF_4', '#skF_4', B_781) | k1_relset_1('#skF_4', B_781, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_10054, c_11095])).
% 7.41/2.61  tff(c_11261, plain, (![B_781]: (v1_funct_2('#skF_4', '#skF_4', B_781))), inference(demodulation, [status(thm), theory('equality')], [c_11093, c_11101])).
% 7.41/2.61  tff(c_9996, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_94])).
% 7.41/2.61  tff(c_10007, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9997, c_9996])).
% 7.41/2.61  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.41/2.61  tff(c_10002, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_9996, c_10])).
% 7.41/2.61  tff(c_10027, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_10007, c_10002])).
% 7.41/2.61  tff(c_10012, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10007, c_98])).
% 7.41/2.61  tff(c_10082, plain, (m1_subset_1('#skF_6', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10046, c_10035, c_10012])).
% 7.41/2.61  tff(c_10085, plain, (![A_654, B_655]: (r1_tarski(A_654, B_655) | ~m1_subset_1(A_654, k1_zfmisc_1(B_655)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.41/2.61  tff(c_10102, plain, (![A_658]: (r1_tarski(A_658, '#skF_4') | ~m1_subset_1(A_658, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_10046, c_10085])).
% 7.41/2.61  tff(c_10109, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_10082, c_10102])).
% 7.41/2.61  tff(c_10112, plain, (![B_659, A_660]: (B_659=A_660 | ~r1_tarski(B_659, A_660) | ~r1_tarski(A_660, B_659))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.41/2.61  tff(c_10114, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_10109, c_10112])).
% 7.41/2.61  tff(c_10121, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10027, c_10114])).
% 7.41/2.61  tff(c_10138, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10121, c_10007, c_10054, c_10121, c_10046, c_10055, c_10007, c_104])).
% 7.41/2.61  tff(c_11265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11261, c_10138])).
% 7.41/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.61  
% 7.41/2.61  Inference rules
% 7.41/2.61  ----------------------
% 7.41/2.61  #Ref     : 0
% 7.41/2.61  #Sup     : 2518
% 7.41/2.61  #Fact    : 0
% 7.41/2.61  #Define  : 0
% 7.41/2.61  #Split   : 36
% 7.41/2.61  #Chain   : 0
% 7.41/2.61  #Close   : 0
% 7.41/2.61  
% 7.41/2.61  Ordering : KBO
% 7.41/2.61  
% 7.41/2.61  Simplification rules
% 7.41/2.61  ----------------------
% 7.41/2.61  #Subsume      : 582
% 7.41/2.61  #Demod        : 2305
% 7.41/2.61  #Tautology    : 1452
% 7.41/2.61  #SimpNegUnit  : 106
% 7.41/2.61  #BackRed      : 65
% 7.41/2.61  
% 7.41/2.61  #Partial instantiations: 0
% 7.41/2.61  #Strategies tried      : 1
% 7.41/2.61  
% 7.41/2.61  Timing (in seconds)
% 7.41/2.61  ----------------------
% 7.83/2.62  Preprocessing        : 0.35
% 7.83/2.62  Parsing              : 0.19
% 7.83/2.62  CNF conversion       : 0.02
% 7.83/2.62  Main loop            : 1.48
% 7.83/2.62  Inferencing          : 0.44
% 7.83/2.62  Reduction            : 0.53
% 7.83/2.62  Demodulation         : 0.38
% 7.83/2.62  BG Simplification    : 0.05
% 7.83/2.62  Subsumption          : 0.36
% 7.83/2.62  Abstraction          : 0.06
% 7.83/2.62  MUC search           : 0.00
% 7.83/2.62  Cooper               : 0.00
% 7.83/2.62  Total                : 1.88
% 7.83/2.62  Index Insertion      : 0.00
% 7.83/2.62  Index Deletion       : 0.00
% 7.83/2.62  Index Matching       : 0.00
% 7.83/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
