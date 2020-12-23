%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:31 EST 2020

% Result     : Theorem 7.28s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 241 expanded)
%              Number of leaves         :   47 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 ( 512 expanded)
%              Number of equality atoms :  116 ( 250 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_71,axiom,(
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

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_150,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_161,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_169,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_161])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_46,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_177,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_169,c_46])).

tff(c_198,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_408,plain,(
    ! [B_139,A_140] :
      ( k1_tarski(k1_funct_1(B_139,A_140)) = k2_relat_1(B_139)
      | k1_tarski(A_140) != k1_relat_1(B_139)
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_381,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_relset_1(A_134,B_135,C_136) = k2_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_394,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_381])).

tff(c_78,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_403,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_78])).

tff(c_414,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_403])).

tff(c_436,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_86,c_414])).

tff(c_261,plain,(
    ! [C_110,A_111,B_112] :
      ( v4_relat_1(C_110,A_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_269,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_261])).

tff(c_42,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_981,plain,(
    ! [A_234,B_235,C_236,D_237] :
      ( k1_enumset1(A_234,B_235,C_236) = D_237
      | k2_tarski(A_234,C_236) = D_237
      | k2_tarski(B_235,C_236) = D_237
      | k2_tarski(A_234,B_235) = D_237
      | k1_tarski(C_236) = D_237
      | k1_tarski(B_235) = D_237
      | k1_tarski(A_234) = D_237
      | k1_xboole_0 = D_237
      | ~ r1_tarski(D_237,k1_enumset1(A_234,B_235,C_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1011,plain,(
    ! [A_9,B_10,D_237] :
      ( k1_enumset1(A_9,A_9,B_10) = D_237
      | k2_tarski(A_9,B_10) = D_237
      | k2_tarski(A_9,B_10) = D_237
      | k2_tarski(A_9,A_9) = D_237
      | k1_tarski(B_10) = D_237
      | k1_tarski(A_9) = D_237
      | k1_tarski(A_9) = D_237
      | k1_xboole_0 = D_237
      | ~ r1_tarski(D_237,k2_tarski(A_9,B_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_981])).

tff(c_1773,plain,(
    ! [A_468,B_469,D_470] :
      ( k2_tarski(A_468,B_469) = D_470
      | k2_tarski(A_468,B_469) = D_470
      | k2_tarski(A_468,B_469) = D_470
      | k1_tarski(A_468) = D_470
      | k1_tarski(B_469) = D_470
      | k1_tarski(A_468) = D_470
      | k1_tarski(A_468) = D_470
      | k1_xboole_0 = D_470
      | ~ r1_tarski(D_470,k2_tarski(A_468,B_469)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_1011])).

tff(c_1806,plain,(
    ! [A_8,D_470] :
      ( k2_tarski(A_8,A_8) = D_470
      | k2_tarski(A_8,A_8) = D_470
      | k2_tarski(A_8,A_8) = D_470
      | k1_tarski(A_8) = D_470
      | k1_tarski(A_8) = D_470
      | k1_tarski(A_8) = D_470
      | k1_tarski(A_8) = D_470
      | k1_xboole_0 = D_470
      | ~ r1_tarski(D_470,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1773])).

tff(c_3115,plain,(
    ! [A_678,D_679] :
      ( k1_tarski(A_678) = D_679
      | k1_tarski(A_678) = D_679
      | k1_tarski(A_678) = D_679
      | k1_tarski(A_678) = D_679
      | k1_tarski(A_678) = D_679
      | k1_tarski(A_678) = D_679
      | k1_tarski(A_678) = D_679
      | k1_xboole_0 = D_679
      | ~ r1_tarski(D_679,k1_tarski(A_678)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_12,c_1806])).

tff(c_3145,plain,(
    ! [A_680,B_681] :
      ( k1_tarski(A_680) = k1_relat_1(B_681)
      | k1_relat_1(B_681) = k1_xboole_0
      | ~ v4_relat_1(B_681,k1_tarski(A_680))
      | ~ v1_relat_1(B_681) ) ),
    inference(resolution,[status(thm)],[c_42,c_3115])).

tff(c_3151,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_269,c_3145])).

tff(c_3158,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_3151])).

tff(c_3160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_436,c_3158])).

tff(c_3161,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_3162,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_3177,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3161,c_3162])).

tff(c_3363,plain,(
    ! [B_731,A_732] :
      ( k1_tarski(k1_funct_1(B_731,A_732)) = k2_relat_1(B_731)
      | k1_tarski(A_732) != k1_relat_1(B_731)
      | ~ v1_funct_1(B_731)
      | ~ v1_relat_1(B_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3168,plain,(
    ! [A_18] : m1_subset_1('#skF_6',k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3161,c_36])).

tff(c_3332,plain,(
    ! [A_723,B_724,C_725] :
      ( k2_relset_1(A_723,B_724,C_725) = k2_relat_1(C_725)
      | ~ m1_subset_1(C_725,k1_zfmisc_1(k2_zfmisc_1(A_723,B_724))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3337,plain,(
    ! [A_723,B_724] : k2_relset_1(A_723,B_724,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3168,c_3332])).

tff(c_3338,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3337,c_78])).

tff(c_3369,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3363,c_3338])).

tff(c_3391,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_86,c_3177,c_3369])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3170,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3161,c_80])).

tff(c_84,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_76,plain,(
    ! [B_52,A_51,C_53] :
      ( k1_xboole_0 = B_52
      | k1_relset_1(A_51,B_52,C_53) = A_51
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3720,plain,(
    ! [B_786,A_787,C_788] :
      ( B_786 = '#skF_6'
      | k1_relset_1(A_787,B_786,C_788) = A_787
      | ~ v1_funct_2(C_788,A_787,B_786)
      | ~ m1_subset_1(C_788,k1_zfmisc_1(k2_zfmisc_1(A_787,B_786))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3161,c_76])).

tff(c_3727,plain,(
    ! [B_790,A_791] :
      ( B_790 = '#skF_6'
      | k1_relset_1(A_791,B_790,'#skF_6') = A_791
      | ~ v1_funct_2('#skF_6',A_791,B_790) ) ),
    inference(resolution,[status(thm)],[c_3168,c_3720])).

tff(c_3736,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_3727])).

tff(c_3743,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3170,c_3736])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3169,plain,(
    ! [A_6] : r1_tarski('#skF_6',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3161,c_8])).

tff(c_3824,plain,(
    ! [D_816,A_817,B_818,C_819] :
      ( r2_hidden(k4_tarski(D_816,'#skF_3'(A_817,B_818,C_819,D_816)),C_819)
      | ~ r2_hidden(D_816,B_818)
      | k1_relset_1(B_818,A_817,C_819) != B_818
      | ~ m1_subset_1(C_819,k1_zfmisc_1(k2_zfmisc_1(B_818,A_817))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    ! [B_28,A_27] :
      ( ~ r1_tarski(B_28,A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4421,plain,(
    ! [C_976,D_977,A_978,B_979] :
      ( ~ r1_tarski(C_976,k4_tarski(D_977,'#skF_3'(A_978,B_979,C_976,D_977)))
      | ~ r2_hidden(D_977,B_979)
      | k1_relset_1(B_979,A_978,C_976) != B_979
      | ~ m1_subset_1(C_976,k1_zfmisc_1(k2_zfmisc_1(B_979,A_978))) ) ),
    inference(resolution,[status(thm)],[c_3824,c_50])).

tff(c_4433,plain,(
    ! [D_977,B_979,A_978] :
      ( ~ r2_hidden(D_977,B_979)
      | k1_relset_1(B_979,A_978,'#skF_6') != B_979
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_979,A_978))) ) ),
    inference(resolution,[status(thm)],[c_3169,c_4421])).

tff(c_4439,plain,(
    ! [D_980,B_981,A_982] :
      ( ~ r2_hidden(D_980,B_981)
      | k1_relset_1(B_981,A_982,'#skF_6') != B_981 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_4433])).

tff(c_4479,plain,(
    ! [A_983,A_984,B_985] :
      ( k1_relset_1(A_983,A_984,'#skF_6') != A_983
      | r1_tarski(A_983,B_985) ) ),
    inference(resolution,[status(thm)],[c_6,c_4439])).

tff(c_4490,plain,(
    ! [B_986] : r1_tarski(k1_tarski('#skF_4'),B_986) ),
    inference(superposition,[status(thm),theory(equality)],[c_3743,c_4479])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3167,plain,(
    ! [A_7] :
      ( A_7 = '#skF_6'
      | ~ r1_tarski(A_7,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3161,c_3161,c_10])).

tff(c_4532,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4490,c_3167])).

tff(c_4552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3391,c_4532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:19:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.28/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.28/2.52  
% 7.28/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.28/2.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.28/2.52  
% 7.28/2.52  %Foreground sorts:
% 7.28/2.52  
% 7.28/2.52  
% 7.28/2.52  %Background operators:
% 7.28/2.52  
% 7.28/2.52  
% 7.28/2.52  %Foreground operators:
% 7.28/2.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.28/2.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.28/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.28/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.28/2.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.28/2.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.28/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.28/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.28/2.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.28/2.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.28/2.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.28/2.52  tff('#skF_5', type, '#skF_5': $i).
% 7.28/2.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.28/2.52  tff('#skF_6', type, '#skF_6': $i).
% 7.28/2.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.28/2.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.28/2.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.28/2.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.28/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.28/2.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.28/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.28/2.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.28/2.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.28/2.52  tff('#skF_4', type, '#skF_4': $i).
% 7.28/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.28/2.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.28/2.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.28/2.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.28/2.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.28/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.28/2.52  
% 7.44/2.54  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 7.44/2.54  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.44/2.54  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.44/2.54  tff(f_101, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 7.44/2.54  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.44/2.54  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.44/2.54  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.44/2.54  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.44/2.54  tff(f_42, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.44/2.54  tff(f_71, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 7.44/2.54  tff(f_73, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.44/2.54  tff(f_150, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.44/2.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.44/2.54  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.44/2.54  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 7.44/2.54  tff(f_106, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.44/2.54  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.44/2.54  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.44/2.54  tff(c_161, plain, (![C_84, A_85, B_86]: (v1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.44/2.54  tff(c_169, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_161])).
% 7.44/2.54  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.44/2.54  tff(c_46, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.44/2.54  tff(c_177, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_169, c_46])).
% 7.44/2.54  tff(c_198, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_177])).
% 7.44/2.54  tff(c_408, plain, (![B_139, A_140]: (k1_tarski(k1_funct_1(B_139, A_140))=k2_relat_1(B_139) | k1_tarski(A_140)!=k1_relat_1(B_139) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.44/2.54  tff(c_381, plain, (![A_134, B_135, C_136]: (k2_relset_1(A_134, B_135, C_136)=k2_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.44/2.54  tff(c_394, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_381])).
% 7.44/2.54  tff(c_78, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.44/2.54  tff(c_403, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_394, c_78])).
% 7.44/2.54  tff(c_414, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_408, c_403])).
% 7.44/2.54  tff(c_436, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_86, c_414])).
% 7.44/2.54  tff(c_261, plain, (![C_110, A_111, B_112]: (v4_relat_1(C_110, A_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.44/2.54  tff(c_269, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_82, c_261])).
% 7.44/2.54  tff(c_42, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(B_23), A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.44/2.54  tff(c_12, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.44/2.54  tff(c_14, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.44/2.54  tff(c_981, plain, (![A_234, B_235, C_236, D_237]: (k1_enumset1(A_234, B_235, C_236)=D_237 | k2_tarski(A_234, C_236)=D_237 | k2_tarski(B_235, C_236)=D_237 | k2_tarski(A_234, B_235)=D_237 | k1_tarski(C_236)=D_237 | k1_tarski(B_235)=D_237 | k1_tarski(A_234)=D_237 | k1_xboole_0=D_237 | ~r1_tarski(D_237, k1_enumset1(A_234, B_235, C_236)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.44/2.54  tff(c_1011, plain, (![A_9, B_10, D_237]: (k1_enumset1(A_9, A_9, B_10)=D_237 | k2_tarski(A_9, B_10)=D_237 | k2_tarski(A_9, B_10)=D_237 | k2_tarski(A_9, A_9)=D_237 | k1_tarski(B_10)=D_237 | k1_tarski(A_9)=D_237 | k1_tarski(A_9)=D_237 | k1_xboole_0=D_237 | ~r1_tarski(D_237, k2_tarski(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_981])).
% 7.44/2.54  tff(c_1773, plain, (![A_468, B_469, D_470]: (k2_tarski(A_468, B_469)=D_470 | k2_tarski(A_468, B_469)=D_470 | k2_tarski(A_468, B_469)=D_470 | k1_tarski(A_468)=D_470 | k1_tarski(B_469)=D_470 | k1_tarski(A_468)=D_470 | k1_tarski(A_468)=D_470 | k1_xboole_0=D_470 | ~r1_tarski(D_470, k2_tarski(A_468, B_469)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_1011])).
% 7.44/2.54  tff(c_1806, plain, (![A_8, D_470]: (k2_tarski(A_8, A_8)=D_470 | k2_tarski(A_8, A_8)=D_470 | k2_tarski(A_8, A_8)=D_470 | k1_tarski(A_8)=D_470 | k1_tarski(A_8)=D_470 | k1_tarski(A_8)=D_470 | k1_tarski(A_8)=D_470 | k1_xboole_0=D_470 | ~r1_tarski(D_470, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1773])).
% 7.44/2.54  tff(c_3115, plain, (![A_678, D_679]: (k1_tarski(A_678)=D_679 | k1_tarski(A_678)=D_679 | k1_tarski(A_678)=D_679 | k1_tarski(A_678)=D_679 | k1_tarski(A_678)=D_679 | k1_tarski(A_678)=D_679 | k1_tarski(A_678)=D_679 | k1_xboole_0=D_679 | ~r1_tarski(D_679, k1_tarski(A_678)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_12, c_1806])).
% 7.44/2.54  tff(c_3145, plain, (![A_680, B_681]: (k1_tarski(A_680)=k1_relat_1(B_681) | k1_relat_1(B_681)=k1_xboole_0 | ~v4_relat_1(B_681, k1_tarski(A_680)) | ~v1_relat_1(B_681))), inference(resolution, [status(thm)], [c_42, c_3115])).
% 7.44/2.54  tff(c_3151, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_269, c_3145])).
% 7.44/2.54  tff(c_3158, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_169, c_3151])).
% 7.44/2.54  tff(c_3160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_436, c_3158])).
% 7.44/2.54  tff(c_3161, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_177])).
% 7.44/2.54  tff(c_3162, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_177])).
% 7.44/2.54  tff(c_3177, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3161, c_3162])).
% 7.44/2.54  tff(c_3363, plain, (![B_731, A_732]: (k1_tarski(k1_funct_1(B_731, A_732))=k2_relat_1(B_731) | k1_tarski(A_732)!=k1_relat_1(B_731) | ~v1_funct_1(B_731) | ~v1_relat_1(B_731))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.44/2.54  tff(c_36, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.44/2.54  tff(c_3168, plain, (![A_18]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_3161, c_36])).
% 7.44/2.54  tff(c_3332, plain, (![A_723, B_724, C_725]: (k2_relset_1(A_723, B_724, C_725)=k2_relat_1(C_725) | ~m1_subset_1(C_725, k1_zfmisc_1(k2_zfmisc_1(A_723, B_724))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.44/2.54  tff(c_3337, plain, (![A_723, B_724]: (k2_relset_1(A_723, B_724, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_3168, c_3332])).
% 7.44/2.54  tff(c_3338, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3337, c_78])).
% 7.44/2.54  tff(c_3369, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3363, c_3338])).
% 7.44/2.54  tff(c_3391, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_86, c_3177, c_3369])).
% 7.44/2.54  tff(c_80, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.44/2.54  tff(c_3170, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3161, c_80])).
% 7.44/2.54  tff(c_84, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.44/2.54  tff(c_76, plain, (![B_52, A_51, C_53]: (k1_xboole_0=B_52 | k1_relset_1(A_51, B_52, C_53)=A_51 | ~v1_funct_2(C_53, A_51, B_52) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.44/2.54  tff(c_3720, plain, (![B_786, A_787, C_788]: (B_786='#skF_6' | k1_relset_1(A_787, B_786, C_788)=A_787 | ~v1_funct_2(C_788, A_787, B_786) | ~m1_subset_1(C_788, k1_zfmisc_1(k2_zfmisc_1(A_787, B_786))))), inference(demodulation, [status(thm), theory('equality')], [c_3161, c_76])).
% 7.44/2.54  tff(c_3727, plain, (![B_790, A_791]: (B_790='#skF_6' | k1_relset_1(A_791, B_790, '#skF_6')=A_791 | ~v1_funct_2('#skF_6', A_791, B_790))), inference(resolution, [status(thm)], [c_3168, c_3720])).
% 7.44/2.54  tff(c_3736, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_84, c_3727])).
% 7.44/2.54  tff(c_3743, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3170, c_3736])).
% 7.44/2.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.44/2.54  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.44/2.54  tff(c_3169, plain, (![A_6]: (r1_tarski('#skF_6', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_3161, c_8])).
% 7.44/2.54  tff(c_3824, plain, (![D_816, A_817, B_818, C_819]: (r2_hidden(k4_tarski(D_816, '#skF_3'(A_817, B_818, C_819, D_816)), C_819) | ~r2_hidden(D_816, B_818) | k1_relset_1(B_818, A_817, C_819)!=B_818 | ~m1_subset_1(C_819, k1_zfmisc_1(k2_zfmisc_1(B_818, A_817))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.44/2.54  tff(c_50, plain, (![B_28, A_27]: (~r1_tarski(B_28, A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.44/2.54  tff(c_4421, plain, (![C_976, D_977, A_978, B_979]: (~r1_tarski(C_976, k4_tarski(D_977, '#skF_3'(A_978, B_979, C_976, D_977))) | ~r2_hidden(D_977, B_979) | k1_relset_1(B_979, A_978, C_976)!=B_979 | ~m1_subset_1(C_976, k1_zfmisc_1(k2_zfmisc_1(B_979, A_978))))), inference(resolution, [status(thm)], [c_3824, c_50])).
% 7.44/2.54  tff(c_4433, plain, (![D_977, B_979, A_978]: (~r2_hidden(D_977, B_979) | k1_relset_1(B_979, A_978, '#skF_6')!=B_979 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_979, A_978))))), inference(resolution, [status(thm)], [c_3169, c_4421])).
% 7.44/2.54  tff(c_4439, plain, (![D_980, B_981, A_982]: (~r2_hidden(D_980, B_981) | k1_relset_1(B_981, A_982, '#skF_6')!=B_981)), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_4433])).
% 7.44/2.54  tff(c_4479, plain, (![A_983, A_984, B_985]: (k1_relset_1(A_983, A_984, '#skF_6')!=A_983 | r1_tarski(A_983, B_985))), inference(resolution, [status(thm)], [c_6, c_4439])).
% 7.44/2.54  tff(c_4490, plain, (![B_986]: (r1_tarski(k1_tarski('#skF_4'), B_986))), inference(superposition, [status(thm), theory('equality')], [c_3743, c_4479])).
% 7.44/2.54  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.44/2.54  tff(c_3167, plain, (![A_7]: (A_7='#skF_6' | ~r1_tarski(A_7, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3161, c_3161, c_10])).
% 7.44/2.54  tff(c_4532, plain, (k1_tarski('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_4490, c_3167])).
% 7.44/2.54  tff(c_4552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3391, c_4532])).
% 7.44/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/2.54  
% 7.44/2.54  Inference rules
% 7.44/2.54  ----------------------
% 7.44/2.54  #Ref     : 0
% 7.44/2.54  #Sup     : 1083
% 7.44/2.54  #Fact    : 0
% 7.44/2.54  #Define  : 0
% 7.44/2.54  #Split   : 3
% 7.44/2.54  #Chain   : 0
% 7.44/2.54  #Close   : 0
% 7.44/2.54  
% 7.44/2.54  Ordering : KBO
% 7.44/2.54  
% 7.44/2.54  Simplification rules
% 7.44/2.54  ----------------------
% 7.44/2.54  #Subsume      : 244
% 7.44/2.54  #Demod        : 329
% 7.44/2.54  #Tautology    : 220
% 7.44/2.54  #SimpNegUnit  : 6
% 7.44/2.54  #BackRed      : 12
% 7.44/2.54  
% 7.44/2.54  #Partial instantiations: 0
% 7.44/2.54  #Strategies tried      : 1
% 7.44/2.54  
% 7.44/2.54  Timing (in seconds)
% 7.44/2.54  ----------------------
% 7.44/2.54  Preprocessing        : 0.39
% 7.44/2.54  Parsing              : 0.21
% 7.44/2.54  CNF conversion       : 0.03
% 7.44/2.54  Main loop            : 1.33
% 7.44/2.54  Inferencing          : 0.45
% 7.44/2.54  Reduction            : 0.35
% 7.44/2.54  Demodulation         : 0.25
% 7.44/2.54  BG Simplification    : 0.05
% 7.44/2.54  Subsumption          : 0.38
% 7.44/2.54  Abstraction          : 0.06
% 7.44/2.54  MUC search           : 0.00
% 7.44/2.54  Cooper               : 0.00
% 7.44/2.55  Total                : 1.75
% 7.44/2.55  Index Insertion      : 0.00
% 7.44/2.55  Index Deletion       : 0.00
% 7.44/2.55  Index Matching       : 0.00
% 7.44/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
