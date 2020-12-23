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
% DateTime   : Thu Dec  3 10:14:48 EST 2020

% Result     : Theorem 8.93s
% Output     : CNFRefutation 9.11s
% Verified   : 
% Statistics : Number of formulae       :  106 (1384 expanded)
%              Number of leaves         :   44 ( 503 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 (3425 expanded)
%              Number of equality atoms :   91 (1187 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

tff(f_124,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_237,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_250,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_237])).

tff(c_44,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5269,plain,(
    ! [A_404,B_405,C_406,D_407] :
      ( k7_relset_1(A_404,B_405,C_406,D_407) = k9_relat_1(C_406,D_407)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(A_404,B_405))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5283,plain,(
    ! [D_407] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_407) = k9_relat_1('#skF_4',D_407) ),
    inference(resolution,[status(thm)],[c_72,c_5269])).

tff(c_5305,plain,(
    ! [B_410,A_411] :
      ( k1_tarski(k1_funct_1(B_410,A_411)) = k2_relat_1(B_410)
      | k1_tarski(A_411) != k1_relat_1(B_410)
      | ~ v1_funct_1(B_410)
      | ~ v1_relat_1(B_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_68,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5311,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5305,c_68])).

tff(c_5332,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_76,c_5311])).

tff(c_5624,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5283,c_5332])).

tff(c_5625,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5624])).

tff(c_387,plain,(
    ! [C_101,A_102,B_103] :
      ( v4_relat_1(C_101,A_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_402,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_387])).

tff(c_404,plain,(
    ! [B_106,A_107] :
      ( k7_relat_1(B_106,A_107) = B_106
      | ~ v4_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_407,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_402,c_404])).

tff(c_410,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_407])).

tff(c_50,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,A_23)),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_414,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_50])).

tff(c_418,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_414])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5496,plain,(
    ! [A_429,B_430,C_431,D_432] :
      ( k1_enumset1(A_429,B_430,C_431) = D_432
      | k2_tarski(A_429,C_431) = D_432
      | k2_tarski(B_430,C_431) = D_432
      | k2_tarski(A_429,B_430) = D_432
      | k1_tarski(C_431) = D_432
      | k1_tarski(B_430) = D_432
      | k1_tarski(A_429) = D_432
      | k1_xboole_0 = D_432
      | ~ r1_tarski(D_432,k1_enumset1(A_429,B_430,C_431)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5522,plain,(
    ! [A_5,B_6,D_432] :
      ( k1_enumset1(A_5,A_5,B_6) = D_432
      | k2_tarski(A_5,B_6) = D_432
      | k2_tarski(A_5,B_6) = D_432
      | k2_tarski(A_5,A_5) = D_432
      | k1_tarski(B_6) = D_432
      | k1_tarski(A_5) = D_432
      | k1_tarski(A_5) = D_432
      | k1_xboole_0 = D_432
      | ~ r1_tarski(D_432,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5496])).

tff(c_6865,plain,(
    ! [A_571,B_572,D_573] :
      ( k2_tarski(A_571,B_572) = D_573
      | k2_tarski(A_571,B_572) = D_573
      | k2_tarski(A_571,B_572) = D_573
      | k1_tarski(A_571) = D_573
      | k1_tarski(B_572) = D_573
      | k1_tarski(A_571) = D_573
      | k1_tarski(A_571) = D_573
      | k1_xboole_0 = D_573
      | ~ r1_tarski(D_573,k2_tarski(A_571,B_572)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_5522])).

tff(c_6892,plain,(
    ! [A_4,D_573] :
      ( k2_tarski(A_4,A_4) = D_573
      | k2_tarski(A_4,A_4) = D_573
      | k2_tarski(A_4,A_4) = D_573
      | k1_tarski(A_4) = D_573
      | k1_tarski(A_4) = D_573
      | k1_tarski(A_4) = D_573
      | k1_tarski(A_4) = D_573
      | k1_xboole_0 = D_573
      | ~ r1_tarski(D_573,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_6865])).

tff(c_9613,plain,(
    ! [A_684,D_685] :
      ( k1_tarski(A_684) = D_685
      | k1_tarski(A_684) = D_685
      | k1_tarski(A_684) = D_685
      | k1_tarski(A_684) = D_685
      | k1_tarski(A_684) = D_685
      | k1_tarski(A_684) = D_685
      | k1_tarski(A_684) = D_685
      | k1_xboole_0 = D_685
      | ~ r1_tarski(D_685,k1_tarski(A_684)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_6892])).

tff(c_9638,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_418,c_9613])).

tff(c_9658,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_5625,c_5625,c_5625,c_5625,c_5625,c_5625,c_5625,c_9638])).

tff(c_534,plain,(
    ! [A_122] :
      ( m1_subset_1(A_122,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_122),k2_relat_1(A_122))))
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5699,plain,(
    ! [A_446] :
      ( r1_tarski(A_446,k2_zfmisc_1(k1_relat_1(A_446),k2_relat_1(A_446)))
      | ~ v1_funct_1(A_446)
      | ~ v1_relat_1(A_446) ) ),
    inference(resolution,[status(thm)],[c_534,c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5720,plain,(
    ! [A_446] :
      ( k2_zfmisc_1(k1_relat_1(A_446),k2_relat_1(A_446)) = A_446
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_446),k2_relat_1(A_446)),A_446)
      | ~ v1_funct_1(A_446)
      | ~ v1_relat_1(A_446) ) ),
    inference(resolution,[status(thm)],[c_5699,c_2])).

tff(c_9671,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9658,c_5720])).

tff(c_9696,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_76,c_8,c_20,c_20,c_9658,c_9671])).

tff(c_9778,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9696,c_8])).

tff(c_46,plain,(
    ! [A_20] : k9_relat_1(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_9777,plain,(
    ! [A_20] : k9_relat_1('#skF_4',A_20) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9696,c_9696,c_46])).

tff(c_5384,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5283,c_68])).

tff(c_10160,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9777,c_5384])).

tff(c_10164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9778,c_10160])).

tff(c_10166,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5624])).

tff(c_422,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_1'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_418,c_2])).

tff(c_482,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_422])).

tff(c_10168,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10166,c_482])).

tff(c_10178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10168])).

tff(c_10179,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_422])).

tff(c_52,plain,(
    ! [B_26,A_25] :
      ( k1_tarski(k1_funct_1(B_26,A_25)) = k2_relat_1(B_26)
      | k1_tarski(A_25) != k1_relat_1(B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10211,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10179,c_72])).

tff(c_10345,plain,(
    ! [A_703,B_704,C_705,D_706] :
      ( k7_relset_1(A_703,B_704,C_705,D_706) = k9_relat_1(C_705,D_706)
      | ~ m1_subset_1(C_705,k1_zfmisc_1(k2_zfmisc_1(A_703,B_704))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10357,plain,(
    ! [D_706] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_706) = k9_relat_1('#skF_4',D_706) ),
    inference(resolution,[status(thm)],[c_10211,c_10345])).

tff(c_10209,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10179,c_68])).

tff(c_10476,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10357,c_10209])).

tff(c_10573,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_10476])).

tff(c_10575,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_76,c_10179,c_10573])).

tff(c_10650,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_10575])).

tff(c_10654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_10650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.93/3.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.93/3.19  
% 8.93/3.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.93/3.19  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.93/3.19  
% 8.93/3.19  %Foreground sorts:
% 8.93/3.19  
% 8.93/3.19  
% 8.93/3.19  %Background operators:
% 8.93/3.19  
% 8.93/3.19  
% 8.93/3.19  %Foreground operators:
% 8.93/3.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.93/3.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.93/3.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.93/3.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.93/3.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.93/3.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.93/3.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.93/3.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.93/3.19  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.93/3.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.93/3.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.93/3.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.93/3.19  tff('#skF_2', type, '#skF_2': $i).
% 8.93/3.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.93/3.19  tff('#skF_3', type, '#skF_3': $i).
% 8.93/3.19  tff('#skF_1', type, '#skF_1': $i).
% 8.93/3.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.93/3.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.93/3.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.93/3.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.93/3.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.93/3.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.93/3.19  tff('#skF_4', type, '#skF_4': $i).
% 8.93/3.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.93/3.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.93/3.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.93/3.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.93/3.19  
% 9.11/3.21  tff(f_136, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 9.11/3.21  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.11/3.21  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 9.11/3.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.11/3.21  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.11/3.21  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.11/3.21  tff(f_114, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.11/3.21  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 9.11/3.21  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.11/3.21  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 9.11/3.21  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 9.11/3.21  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.11/3.21  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 9.11/3.21  tff(f_72, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 9.11/3.21  tff(f_124, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 9.11/3.21  tff(f_76, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.11/3.21  tff(f_82, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 9.11/3.21  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.11/3.21  tff(c_237, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.11/3.21  tff(c_250, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_237])).
% 9.11/3.21  tff(c_44, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.11/3.21  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.11/3.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.11/3.21  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.11/3.21  tff(c_20, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.11/3.21  tff(c_5269, plain, (![A_404, B_405, C_406, D_407]: (k7_relset_1(A_404, B_405, C_406, D_407)=k9_relat_1(C_406, D_407) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(A_404, B_405))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.11/3.21  tff(c_5283, plain, (![D_407]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_407)=k9_relat_1('#skF_4', D_407))), inference(resolution, [status(thm)], [c_72, c_5269])).
% 9.11/3.21  tff(c_5305, plain, (![B_410, A_411]: (k1_tarski(k1_funct_1(B_410, A_411))=k2_relat_1(B_410) | k1_tarski(A_411)!=k1_relat_1(B_410) | ~v1_funct_1(B_410) | ~v1_relat_1(B_410))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.11/3.21  tff(c_68, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.11/3.21  tff(c_5311, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5305, c_68])).
% 9.11/3.21  tff(c_5332, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_76, c_5311])).
% 9.11/3.21  tff(c_5624, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5283, c_5332])).
% 9.11/3.21  tff(c_5625, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_5624])).
% 9.11/3.21  tff(c_387, plain, (![C_101, A_102, B_103]: (v4_relat_1(C_101, A_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.11/3.21  tff(c_402, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_72, c_387])).
% 9.11/3.21  tff(c_404, plain, (![B_106, A_107]: (k7_relat_1(B_106, A_107)=B_106 | ~v4_relat_1(B_106, A_107) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.11/3.21  tff(c_407, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_402, c_404])).
% 9.11/3.21  tff(c_410, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_407])).
% 9.11/3.21  tff(c_50, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, A_23)), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.11/3.21  tff(c_414, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_410, c_50])).
% 9.11/3.21  tff(c_418, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_414])).
% 9.11/3.21  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.11/3.21  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.11/3.21  tff(c_5496, plain, (![A_429, B_430, C_431, D_432]: (k1_enumset1(A_429, B_430, C_431)=D_432 | k2_tarski(A_429, C_431)=D_432 | k2_tarski(B_430, C_431)=D_432 | k2_tarski(A_429, B_430)=D_432 | k1_tarski(C_431)=D_432 | k1_tarski(B_430)=D_432 | k1_tarski(A_429)=D_432 | k1_xboole_0=D_432 | ~r1_tarski(D_432, k1_enumset1(A_429, B_430, C_431)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.11/3.21  tff(c_5522, plain, (![A_5, B_6, D_432]: (k1_enumset1(A_5, A_5, B_6)=D_432 | k2_tarski(A_5, B_6)=D_432 | k2_tarski(A_5, B_6)=D_432 | k2_tarski(A_5, A_5)=D_432 | k1_tarski(B_6)=D_432 | k1_tarski(A_5)=D_432 | k1_tarski(A_5)=D_432 | k1_xboole_0=D_432 | ~r1_tarski(D_432, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5496])).
% 9.11/3.21  tff(c_6865, plain, (![A_571, B_572, D_573]: (k2_tarski(A_571, B_572)=D_573 | k2_tarski(A_571, B_572)=D_573 | k2_tarski(A_571, B_572)=D_573 | k1_tarski(A_571)=D_573 | k1_tarski(B_572)=D_573 | k1_tarski(A_571)=D_573 | k1_tarski(A_571)=D_573 | k1_xboole_0=D_573 | ~r1_tarski(D_573, k2_tarski(A_571, B_572)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_5522])).
% 9.11/3.21  tff(c_6892, plain, (![A_4, D_573]: (k2_tarski(A_4, A_4)=D_573 | k2_tarski(A_4, A_4)=D_573 | k2_tarski(A_4, A_4)=D_573 | k1_tarski(A_4)=D_573 | k1_tarski(A_4)=D_573 | k1_tarski(A_4)=D_573 | k1_tarski(A_4)=D_573 | k1_xboole_0=D_573 | ~r1_tarski(D_573, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_6865])).
% 9.11/3.21  tff(c_9613, plain, (![A_684, D_685]: (k1_tarski(A_684)=D_685 | k1_tarski(A_684)=D_685 | k1_tarski(A_684)=D_685 | k1_tarski(A_684)=D_685 | k1_tarski(A_684)=D_685 | k1_tarski(A_684)=D_685 | k1_tarski(A_684)=D_685 | k1_xboole_0=D_685 | ~r1_tarski(D_685, k1_tarski(A_684)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_10, c_6892])).
% 9.11/3.21  tff(c_9638, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_418, c_9613])).
% 9.11/3.21  tff(c_9658, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_5625, c_5625, c_5625, c_5625, c_5625, c_5625, c_5625, c_9638])).
% 9.11/3.21  tff(c_534, plain, (![A_122]: (m1_subset_1(A_122, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_122), k2_relat_1(A_122)))) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.11/3.21  tff(c_40, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.11/3.21  tff(c_5699, plain, (![A_446]: (r1_tarski(A_446, k2_zfmisc_1(k1_relat_1(A_446), k2_relat_1(A_446))) | ~v1_funct_1(A_446) | ~v1_relat_1(A_446))), inference(resolution, [status(thm)], [c_534, c_40])).
% 9.11/3.21  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.11/3.21  tff(c_5720, plain, (![A_446]: (k2_zfmisc_1(k1_relat_1(A_446), k2_relat_1(A_446))=A_446 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_446), k2_relat_1(A_446)), A_446) | ~v1_funct_1(A_446) | ~v1_relat_1(A_446))), inference(resolution, [status(thm)], [c_5699, c_2])).
% 9.11/3.21  tff(c_9671, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')), '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9658, c_5720])).
% 9.11/3.21  tff(c_9696, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_76, c_8, c_20, c_20, c_9658, c_9671])).
% 9.11/3.21  tff(c_9778, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9696, c_8])).
% 9.11/3.21  tff(c_46, plain, (![A_20]: (k9_relat_1(k1_xboole_0, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.11/3.21  tff(c_9777, plain, (![A_20]: (k9_relat_1('#skF_4', A_20)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9696, c_9696, c_46])).
% 9.11/3.21  tff(c_5384, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5283, c_68])).
% 9.11/3.21  tff(c_10160, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9777, c_5384])).
% 9.11/3.21  tff(c_10164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9778, c_10160])).
% 9.11/3.21  tff(c_10166, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_5624])).
% 9.11/3.21  tff(c_422, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | ~r1_tarski(k1_tarski('#skF_1'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_418, c_2])).
% 9.11/3.21  tff(c_482, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_422])).
% 9.11/3.21  tff(c_10168, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10166, c_482])).
% 9.11/3.21  tff(c_10178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10168])).
% 9.11/3.21  tff(c_10179, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_422])).
% 9.11/3.21  tff(c_52, plain, (![B_26, A_25]: (k1_tarski(k1_funct_1(B_26, A_25))=k2_relat_1(B_26) | k1_tarski(A_25)!=k1_relat_1(B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.11/3.21  tff(c_10211, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10179, c_72])).
% 9.11/3.21  tff(c_10345, plain, (![A_703, B_704, C_705, D_706]: (k7_relset_1(A_703, B_704, C_705, D_706)=k9_relat_1(C_705, D_706) | ~m1_subset_1(C_705, k1_zfmisc_1(k2_zfmisc_1(A_703, B_704))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.11/3.21  tff(c_10357, plain, (![D_706]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_706)=k9_relat_1('#skF_4', D_706))), inference(resolution, [status(thm)], [c_10211, c_10345])).
% 9.11/3.21  tff(c_10209, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10179, c_68])).
% 9.11/3.21  tff(c_10476, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10357, c_10209])).
% 9.11/3.21  tff(c_10573, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_52, c_10476])).
% 9.11/3.21  tff(c_10575, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_76, c_10179, c_10573])).
% 9.11/3.21  tff(c_10650, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_10575])).
% 9.11/3.21  tff(c_10654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_250, c_10650])).
% 9.11/3.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.11/3.21  
% 9.11/3.21  Inference rules
% 9.11/3.21  ----------------------
% 9.11/3.21  #Ref     : 0
% 9.11/3.21  #Sup     : 2414
% 9.11/3.21  #Fact    : 17
% 9.11/3.21  #Define  : 0
% 9.11/3.21  #Split   : 34
% 9.11/3.21  #Chain   : 0
% 9.11/3.21  #Close   : 0
% 9.11/3.21  
% 9.11/3.21  Ordering : KBO
% 9.11/3.21  
% 9.11/3.21  Simplification rules
% 9.11/3.21  ----------------------
% 9.11/3.21  #Subsume      : 594
% 9.11/3.21  #Demod        : 4686
% 9.11/3.21  #Tautology    : 865
% 9.11/3.21  #SimpNegUnit  : 4
% 9.11/3.21  #BackRed      : 175
% 9.11/3.21  
% 9.11/3.21  #Partial instantiations: 0
% 9.11/3.21  #Strategies tried      : 1
% 9.11/3.21  
% 9.11/3.21  Timing (in seconds)
% 9.11/3.21  ----------------------
% 9.11/3.21  Preprocessing        : 0.39
% 9.11/3.21  Parsing              : 0.21
% 9.11/3.21  CNF conversion       : 0.02
% 9.11/3.21  Main loop            : 1.99
% 9.11/3.21  Inferencing          : 0.63
% 9.11/3.21  Reduction            : 0.78
% 9.11/3.21  Demodulation         : 0.60
% 9.11/3.21  BG Simplification    : 0.07
% 9.11/3.21  Subsumption          : 0.38
% 9.11/3.21  Abstraction          : 0.11
% 9.11/3.21  MUC search           : 0.00
% 9.11/3.21  Cooper               : 0.00
% 9.11/3.21  Total                : 2.41
% 9.11/3.21  Index Insertion      : 0.00
% 9.11/3.21  Index Deletion       : 0.00
% 9.11/3.21  Index Matching       : 0.00
% 9.11/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
