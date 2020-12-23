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
% DateTime   : Thu Dec  3 10:14:47 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 431 expanded)
%              Number of leaves         :   41 ( 168 expanded)
%              Depth                    :   14
%              Number of atoms          :  153 (1107 expanded)
%              Number of equality atoms :   79 ( 510 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_205,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_213,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_205])).

tff(c_44,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_323,plain,(
    ! [B_100,A_101] :
      ( k1_tarski(k1_funct_1(B_100,A_101)) = k2_relat_1(B_100)
      | k1_tarski(A_101) != k1_relat_1(B_100)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_335,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_60])).

tff(c_356,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_68,c_335])).

tff(c_388,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_247,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_257,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_247])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_423,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k1_enumset1(A_120,B_121,C_122) = D_123
      | k2_tarski(A_120,C_122) = D_123
      | k2_tarski(B_121,C_122) = D_123
      | k2_tarski(A_120,B_121) = D_123
      | k1_tarski(C_122) = D_123
      | k1_tarski(B_121) = D_123
      | k1_tarski(A_120) = D_123
      | k1_xboole_0 = D_123
      | ~ r1_tarski(D_123,k1_enumset1(A_120,B_121,C_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_439,plain,(
    ! [A_5,B_6,D_123] :
      ( k1_enumset1(A_5,A_5,B_6) = D_123
      | k2_tarski(A_5,B_6) = D_123
      | k2_tarski(A_5,B_6) = D_123
      | k2_tarski(A_5,A_5) = D_123
      | k1_tarski(B_6) = D_123
      | k1_tarski(A_5) = D_123
      | k1_tarski(A_5) = D_123
      | k1_xboole_0 = D_123
      | ~ r1_tarski(D_123,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_423])).

tff(c_596,plain,(
    ! [A_173,B_174,D_175] :
      ( k2_tarski(A_173,B_174) = D_175
      | k2_tarski(A_173,B_174) = D_175
      | k2_tarski(A_173,B_174) = D_175
      | k1_tarski(A_173) = D_175
      | k1_tarski(B_174) = D_175
      | k1_tarski(A_173) = D_175
      | k1_tarski(A_173) = D_175
      | k1_xboole_0 = D_175
      | ~ r1_tarski(D_175,k2_tarski(A_173,B_174)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_439])).

tff(c_636,plain,(
    ! [A_176,B_177,B_178] :
      ( k2_tarski(A_176,B_177) = k1_relat_1(B_178)
      | k1_tarski(B_177) = k1_relat_1(B_178)
      | k1_tarski(A_176) = k1_relat_1(B_178)
      | k1_relat_1(B_178) = k1_xboole_0
      | ~ v4_relat_1(B_178,k2_tarski(A_176,B_177))
      | ~ v1_relat_1(B_178) ) ),
    inference(resolution,[status(thm)],[c_42,c_596])).

tff(c_639,plain,(
    ! [A_4,B_178] :
      ( k2_tarski(A_4,A_4) = k1_relat_1(B_178)
      | k1_tarski(A_4) = k1_relat_1(B_178)
      | k1_tarski(A_4) = k1_relat_1(B_178)
      | k1_relat_1(B_178) = k1_xboole_0
      | ~ v4_relat_1(B_178,k1_tarski(A_4))
      | ~ v1_relat_1(B_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_636])).

tff(c_641,plain,(
    ! [A_179,B_180] :
      ( k1_tarski(A_179) = k1_relat_1(B_180)
      | k1_tarski(A_179) = k1_relat_1(B_180)
      | k1_tarski(A_179) = k1_relat_1(B_180)
      | k1_relat_1(B_180) = k1_xboole_0
      | ~ v4_relat_1(B_180,k1_tarski(A_179))
      | ~ v1_relat_1(B_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_639])).

tff(c_647,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_257,c_641])).

tff(c_650,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_647])).

tff(c_651,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_650])).

tff(c_302,plain,(
    ! [A_95] :
      ( r1_tarski(A_95,k2_zfmisc_1(k1_relat_1(A_95),k2_relat_1(A_95)))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_310,plain,(
    ! [A_95] :
      ( k2_zfmisc_1(k1_relat_1(A_95),k2_relat_1(A_95)) = A_95
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_95),k2_relat_1(A_95)),A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_302,c_2])).

tff(c_658,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_310])).

tff(c_685,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_8,c_20,c_20,c_651,c_658])).

tff(c_718,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_8])).

tff(c_46,plain,(
    ! [A_20] : k9_relat_1(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_715,plain,(
    ! [A_20] : k9_relat_1('#skF_4',A_20) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_685,c_46])).

tff(c_405,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k7_relset_1(A_115,B_116,C_117,D_118) = k9_relat_1(C_117,D_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_412,plain,(
    ! [D_118] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_118) = k9_relat_1('#skF_4',D_118) ),
    inference(resolution,[status(thm)],[c_64,c_405])).

tff(c_413,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_60])).

tff(c_808,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_413])).

tff(c_812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_808])).

tff(c_814,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_817,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_64])).

tff(c_58,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k7_relset_1(A_30,B_31,C_32,D_33) = k9_relat_1(C_32,D_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_902,plain,(
    ! [D_33] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_33) = k9_relat_1('#skF_4',D_33) ),
    inference(resolution,[status(thm)],[c_817,c_58])).

tff(c_813,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_1045,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_813])).

tff(c_1052,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_1045])).

tff(c_1064,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1052])).

tff(c_1068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_1064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:33:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.54  
% 3.61/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.61/1.54  
% 3.61/1.54  %Foreground sorts:
% 3.61/1.54  
% 3.61/1.54  
% 3.61/1.54  %Background operators:
% 3.61/1.54  
% 3.61/1.54  
% 3.61/1.54  %Foreground operators:
% 3.61/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.61/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.61/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.61/1.54  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.61/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.61/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.61/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.61/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.61/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.61/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.61/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.61/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.61/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.54  
% 3.61/1.56  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.61/1.56  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.61/1.56  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.61/1.56  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.61/1.56  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.61/1.56  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.61/1.56  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.61/1.56  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.61/1.56  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.61/1.56  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.61/1.56  tff(f_72, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.61/1.56  tff(f_88, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.61/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.61/1.56  tff(f_84, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.61/1.56  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.61/1.56  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.61/1.56  tff(c_205, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.61/1.56  tff(c_213, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_205])).
% 3.61/1.56  tff(c_44, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.61/1.56  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.61/1.56  tff(c_20, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.61/1.56  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.61/1.56  tff(c_323, plain, (![B_100, A_101]: (k1_tarski(k1_funct_1(B_100, A_101))=k2_relat_1(B_100) | k1_tarski(A_101)!=k1_relat_1(B_100) | ~v1_funct_1(B_100) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.61/1.56  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.61/1.56  tff(c_335, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_323, c_60])).
% 3.61/1.56  tff(c_356, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_68, c_335])).
% 3.61/1.56  tff(c_388, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_356])).
% 3.61/1.56  tff(c_247, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.61/1.56  tff(c_257, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_247])).
% 3.61/1.56  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.61/1.56  tff(c_42, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.61/1.56  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.61/1.56  tff(c_423, plain, (![A_120, B_121, C_122, D_123]: (k1_enumset1(A_120, B_121, C_122)=D_123 | k2_tarski(A_120, C_122)=D_123 | k2_tarski(B_121, C_122)=D_123 | k2_tarski(A_120, B_121)=D_123 | k1_tarski(C_122)=D_123 | k1_tarski(B_121)=D_123 | k1_tarski(A_120)=D_123 | k1_xboole_0=D_123 | ~r1_tarski(D_123, k1_enumset1(A_120, B_121, C_122)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.61/1.56  tff(c_439, plain, (![A_5, B_6, D_123]: (k1_enumset1(A_5, A_5, B_6)=D_123 | k2_tarski(A_5, B_6)=D_123 | k2_tarski(A_5, B_6)=D_123 | k2_tarski(A_5, A_5)=D_123 | k1_tarski(B_6)=D_123 | k1_tarski(A_5)=D_123 | k1_tarski(A_5)=D_123 | k1_xboole_0=D_123 | ~r1_tarski(D_123, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_423])).
% 3.61/1.56  tff(c_596, plain, (![A_173, B_174, D_175]: (k2_tarski(A_173, B_174)=D_175 | k2_tarski(A_173, B_174)=D_175 | k2_tarski(A_173, B_174)=D_175 | k1_tarski(A_173)=D_175 | k1_tarski(B_174)=D_175 | k1_tarski(A_173)=D_175 | k1_tarski(A_173)=D_175 | k1_xboole_0=D_175 | ~r1_tarski(D_175, k2_tarski(A_173, B_174)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_439])).
% 3.61/1.56  tff(c_636, plain, (![A_176, B_177, B_178]: (k2_tarski(A_176, B_177)=k1_relat_1(B_178) | k1_tarski(B_177)=k1_relat_1(B_178) | k1_tarski(A_176)=k1_relat_1(B_178) | k1_relat_1(B_178)=k1_xboole_0 | ~v4_relat_1(B_178, k2_tarski(A_176, B_177)) | ~v1_relat_1(B_178))), inference(resolution, [status(thm)], [c_42, c_596])).
% 3.61/1.56  tff(c_639, plain, (![A_4, B_178]: (k2_tarski(A_4, A_4)=k1_relat_1(B_178) | k1_tarski(A_4)=k1_relat_1(B_178) | k1_tarski(A_4)=k1_relat_1(B_178) | k1_relat_1(B_178)=k1_xboole_0 | ~v4_relat_1(B_178, k1_tarski(A_4)) | ~v1_relat_1(B_178))), inference(superposition, [status(thm), theory('equality')], [c_10, c_636])).
% 3.61/1.56  tff(c_641, plain, (![A_179, B_180]: (k1_tarski(A_179)=k1_relat_1(B_180) | k1_tarski(A_179)=k1_relat_1(B_180) | k1_tarski(A_179)=k1_relat_1(B_180) | k1_relat_1(B_180)=k1_xboole_0 | ~v4_relat_1(B_180, k1_tarski(A_179)) | ~v1_relat_1(B_180))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_639])).
% 3.61/1.56  tff(c_647, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_257, c_641])).
% 3.61/1.56  tff(c_650, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_213, c_647])).
% 3.61/1.56  tff(c_651, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_388, c_650])).
% 3.61/1.56  tff(c_302, plain, (![A_95]: (r1_tarski(A_95, k2_zfmisc_1(k1_relat_1(A_95), k2_relat_1(A_95))) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.61/1.56  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.61/1.56  tff(c_310, plain, (![A_95]: (k2_zfmisc_1(k1_relat_1(A_95), k2_relat_1(A_95))=A_95 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_95), k2_relat_1(A_95)), A_95) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_302, c_2])).
% 3.61/1.56  tff(c_658, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_651, c_310])).
% 3.61/1.56  tff(c_685, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_213, c_8, c_20, c_20, c_651, c_658])).
% 3.61/1.56  tff(c_718, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_685, c_8])).
% 3.61/1.56  tff(c_46, plain, (![A_20]: (k9_relat_1(k1_xboole_0, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.61/1.56  tff(c_715, plain, (![A_20]: (k9_relat_1('#skF_4', A_20)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_685, c_685, c_46])).
% 3.61/1.56  tff(c_405, plain, (![A_115, B_116, C_117, D_118]: (k7_relset_1(A_115, B_116, C_117, D_118)=k9_relat_1(C_117, D_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.61/1.56  tff(c_412, plain, (![D_118]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_118)=k9_relat_1('#skF_4', D_118))), inference(resolution, [status(thm)], [c_64, c_405])).
% 3.61/1.56  tff(c_413, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_412, c_60])).
% 3.61/1.56  tff(c_808, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_715, c_413])).
% 3.61/1.56  tff(c_812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_718, c_808])).
% 3.61/1.56  tff(c_814, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_356])).
% 3.61/1.56  tff(c_817, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_814, c_64])).
% 3.61/1.56  tff(c_58, plain, (![A_30, B_31, C_32, D_33]: (k7_relset_1(A_30, B_31, C_32, D_33)=k9_relat_1(C_32, D_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.61/1.56  tff(c_902, plain, (![D_33]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_33)=k9_relat_1('#skF_4', D_33))), inference(resolution, [status(thm)], [c_817, c_58])).
% 3.61/1.56  tff(c_813, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_356])).
% 3.61/1.56  tff(c_1045, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_814, c_813])).
% 3.61/1.56  tff(c_1052, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_902, c_1045])).
% 3.61/1.56  tff(c_1064, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1052])).
% 3.61/1.56  tff(c_1068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_213, c_1064])).
% 3.61/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.56  
% 3.61/1.56  Inference rules
% 3.61/1.56  ----------------------
% 3.61/1.56  #Ref     : 0
% 3.61/1.56  #Sup     : 212
% 3.61/1.56  #Fact    : 0
% 3.61/1.56  #Define  : 0
% 3.61/1.56  #Split   : 1
% 3.61/1.56  #Chain   : 0
% 3.61/1.56  #Close   : 0
% 3.61/1.56  
% 3.61/1.56  Ordering : KBO
% 3.61/1.56  
% 3.61/1.56  Simplification rules
% 3.61/1.56  ----------------------
% 3.61/1.56  #Subsume      : 29
% 3.61/1.56  #Demod        : 193
% 3.61/1.56  #Tautology    : 97
% 3.61/1.56  #SimpNegUnit  : 1
% 3.61/1.56  #BackRed      : 29
% 3.61/1.56  
% 3.61/1.56  #Partial instantiations: 0
% 3.61/1.56  #Strategies tried      : 1
% 3.61/1.56  
% 3.61/1.56  Timing (in seconds)
% 3.61/1.56  ----------------------
% 3.61/1.56  Preprocessing        : 0.32
% 3.61/1.56  Parsing              : 0.17
% 3.61/1.56  CNF conversion       : 0.02
% 3.61/1.56  Main loop            : 0.47
% 3.61/1.56  Inferencing          : 0.17
% 3.61/1.56  Reduction            : 0.15
% 3.61/1.56  Demodulation         : 0.11
% 3.61/1.56  BG Simplification    : 0.03
% 3.61/1.56  Subsumption          : 0.09
% 3.61/1.56  Abstraction          : 0.02
% 3.61/1.56  MUC search           : 0.00
% 3.61/1.56  Cooper               : 0.00
% 3.61/1.56  Total                : 0.83
% 3.61/1.56  Index Insertion      : 0.00
% 3.61/1.56  Index Deletion       : 0.00
% 3.61/1.56  Index Matching       : 0.00
% 3.61/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
