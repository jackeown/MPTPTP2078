%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:53 EST 2020

% Result     : Theorem 11.95s
% Output     : CNFRefutation 12.25s
% Verified   : 
% Statistics : Number of formulae       :  100 (1292 expanded)
%              Number of leaves         :   41 ( 471 expanded)
%              Depth                    :   14
%              Number of atoms          :  179 (3172 expanded)
%              Number of equality atoms :   89 (1124 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_94,axiom,(
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

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

tff(f_116,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_82,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_254,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_267,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_254])).

tff(c_44,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_550,plain,(
    ! [B_119,A_120] :
      ( k1_tarski(k1_funct_1(B_119,A_120)) = k2_relat_1(B_119)
      | k1_tarski(A_120) != k1_relat_1(B_119)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_442,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k7_relset_1(A_112,B_113,C_114,D_115) = k9_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_460,plain,(
    ! [D_115] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_115) = k9_relat_1('#skF_4',D_115) ),
    inference(resolution,[status(thm)],[c_68,c_442])).

tff(c_64,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_479,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_64])).

tff(c_556,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_479])).

tff(c_583,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_72,c_556])).

tff(c_674,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_583])).

tff(c_354,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_373,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_354])).

tff(c_52,plain,(
    ! [A_26,B_27,C_28] :
      ( m1_subset_1(k1_relset_1(A_26,B_27,C_28),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_398,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_52])).

tff(c_402,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_398])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_407,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_402,c_40])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_720,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( k1_enumset1(A_127,B_128,C_129) = D_130
      | k2_tarski(A_127,C_129) = D_130
      | k2_tarski(B_128,C_129) = D_130
      | k2_tarski(A_127,B_128) = D_130
      | k1_tarski(C_129) = D_130
      | k1_tarski(B_128) = D_130
      | k1_tarski(A_127) = D_130
      | k1_xboole_0 = D_130
      | ~ r1_tarski(D_130,k1_enumset1(A_127,B_128,C_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_735,plain,(
    ! [A_5,B_6,D_130] :
      ( k1_enumset1(A_5,A_5,B_6) = D_130
      | k2_tarski(A_5,B_6) = D_130
      | k2_tarski(A_5,B_6) = D_130
      | k2_tarski(A_5,A_5) = D_130
      | k1_tarski(B_6) = D_130
      | k1_tarski(A_5) = D_130
      | k1_tarski(A_5) = D_130
      | k1_xboole_0 = D_130
      | ~ r1_tarski(D_130,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_720])).

tff(c_14994,plain,(
    ! [A_748,B_749,D_750] :
      ( k2_tarski(A_748,B_749) = D_750
      | k2_tarski(A_748,B_749) = D_750
      | k2_tarski(A_748,B_749) = D_750
      | k1_tarski(A_748) = D_750
      | k1_tarski(B_749) = D_750
      | k1_tarski(A_748) = D_750
      | k1_tarski(A_748) = D_750
      | k1_xboole_0 = D_750
      | ~ r1_tarski(D_750,k2_tarski(A_748,B_749)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_735])).

tff(c_15037,plain,(
    ! [A_4,D_750] :
      ( k2_tarski(A_4,A_4) = D_750
      | k2_tarski(A_4,A_4) = D_750
      | k2_tarski(A_4,A_4) = D_750
      | k1_tarski(A_4) = D_750
      | k1_tarski(A_4) = D_750
      | k1_tarski(A_4) = D_750
      | k1_tarski(A_4) = D_750
      | k1_xboole_0 = D_750
      | ~ r1_tarski(D_750,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_14994])).

tff(c_22047,plain,(
    ! [A_914,D_915] :
      ( k1_tarski(A_914) = D_915
      | k1_tarski(A_914) = D_915
      | k1_tarski(A_914) = D_915
      | k1_tarski(A_914) = D_915
      | k1_tarski(A_914) = D_915
      | k1_tarski(A_914) = D_915
      | k1_tarski(A_914) = D_915
      | k1_xboole_0 = D_915
      | ~ r1_tarski(D_915,k1_tarski(A_914)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_15037])).

tff(c_22112,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_407,c_22047])).

tff(c_22138,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_674,c_674,c_674,c_674,c_674,c_674,c_674,c_22112])).

tff(c_337,plain,(
    ! [A_96] :
      ( m1_subset_1(A_96,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_96),k2_relat_1(A_96))))
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_346,plain,(
    ! [A_97] :
      ( r1_tarski(A_97,k2_zfmisc_1(k1_relat_1(A_97),k2_relat_1(A_97)))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_337,c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_353,plain,(
    ! [A_97] :
      ( k2_zfmisc_1(k1_relat_1(A_97),k2_relat_1(A_97)) = A_97
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_97),k2_relat_1(A_97)),A_97)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_346,c_2])).

tff(c_22159,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22138,c_353])).

tff(c_22188,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_72,c_8,c_20,c_20,c_22138,c_22159])).

tff(c_22305,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22188,c_8])).

tff(c_46,plain,(
    ! [A_20] : k9_relat_1(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22302,plain,(
    ! [A_20] : k9_relat_1('#skF_4',A_20) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22188,c_22188,c_46])).

tff(c_22638,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22302,c_479])).

tff(c_22642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22305,c_22638])).

tff(c_22644,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_583])).

tff(c_410,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_1'),k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_407,c_2])).

tff(c_411,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_22646,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22644,c_411])).

tff(c_22656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22646])).

tff(c_22657,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_48,plain,(
    ! [B_22,A_21] :
      ( k1_tarski(k1_funct_1(B_22,A_21)) = k2_relat_1(B_22)
      | k1_tarski(A_21) != k1_relat_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22665,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22657,c_68])).

tff(c_56,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( k7_relset_1(A_32,B_33,C_34,D_35) = k9_relat_1(C_34,D_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22736,plain,(
    ! [D_35] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_35) = k9_relat_1('#skF_4',D_35) ),
    inference(resolution,[status(thm)],[c_22665,c_56])).

tff(c_22663,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22657,c_64])).

tff(c_22843,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22736,c_22663])).

tff(c_22855,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_22843])).

tff(c_22857,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_72,c_22657,c_22855])).

tff(c_22860,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_22857])).

tff(c_22864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_22860])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.95/4.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.95/4.73  
% 11.95/4.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.95/4.73  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.95/4.73  
% 11.95/4.73  %Foreground sorts:
% 11.95/4.73  
% 11.95/4.73  
% 11.95/4.73  %Background operators:
% 11.95/4.73  
% 11.95/4.73  
% 11.95/4.73  %Foreground operators:
% 11.95/4.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.95/4.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.95/4.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.95/4.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.95/4.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.95/4.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.95/4.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.95/4.73  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 11.95/4.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.95/4.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.95/4.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.95/4.73  tff('#skF_2', type, '#skF_2': $i).
% 11.95/4.73  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.95/4.73  tff('#skF_3', type, '#skF_3': $i).
% 11.95/4.73  tff('#skF_1', type, '#skF_1': $i).
% 11.95/4.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.95/4.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.95/4.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.95/4.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.95/4.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.95/4.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.95/4.73  tff('#skF_4', type, '#skF_4': $i).
% 11.95/4.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.95/4.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.95/4.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.95/4.73  
% 12.25/4.75  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 12.25/4.75  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.25/4.75  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 12.25/4.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.25/4.75  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.25/4.75  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.25/4.75  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 12.25/4.75  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 12.25/4.75  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.25/4.75  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 12.25/4.75  tff(f_76, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.25/4.75  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 12.25/4.75  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 12.25/4.75  tff(f_72, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 12.25/4.75  tff(f_116, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 12.25/4.75  tff(f_82, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 12.25/4.75  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.25/4.75  tff(c_254, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.25/4.75  tff(c_267, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_254])).
% 12.25/4.75  tff(c_44, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.25/4.75  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.25/4.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.25/4.75  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.25/4.75  tff(c_20, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.25/4.75  tff(c_550, plain, (![B_119, A_120]: (k1_tarski(k1_funct_1(B_119, A_120))=k2_relat_1(B_119) | k1_tarski(A_120)!=k1_relat_1(B_119) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.25/4.75  tff(c_442, plain, (![A_112, B_113, C_114, D_115]: (k7_relset_1(A_112, B_113, C_114, D_115)=k9_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.25/4.75  tff(c_460, plain, (![D_115]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_115)=k9_relat_1('#skF_4', D_115))), inference(resolution, [status(thm)], [c_68, c_442])).
% 12.25/4.75  tff(c_64, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.25/4.75  tff(c_479, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_64])).
% 12.25/4.75  tff(c_556, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_550, c_479])).
% 12.25/4.75  tff(c_583, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_267, c_72, c_556])).
% 12.25/4.75  tff(c_674, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_583])).
% 12.25/4.75  tff(c_354, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.25/4.75  tff(c_373, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_354])).
% 12.25/4.75  tff(c_52, plain, (![A_26, B_27, C_28]: (m1_subset_1(k1_relset_1(A_26, B_27, C_28), k1_zfmisc_1(A_26)) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.25/4.75  tff(c_398, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_373, c_52])).
% 12.25/4.75  tff(c_402, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_398])).
% 12.25/4.75  tff(c_40, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.25/4.75  tff(c_407, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_402, c_40])).
% 12.25/4.75  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.25/4.75  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.25/4.75  tff(c_720, plain, (![A_127, B_128, C_129, D_130]: (k1_enumset1(A_127, B_128, C_129)=D_130 | k2_tarski(A_127, C_129)=D_130 | k2_tarski(B_128, C_129)=D_130 | k2_tarski(A_127, B_128)=D_130 | k1_tarski(C_129)=D_130 | k1_tarski(B_128)=D_130 | k1_tarski(A_127)=D_130 | k1_xboole_0=D_130 | ~r1_tarski(D_130, k1_enumset1(A_127, B_128, C_129)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.25/4.75  tff(c_735, plain, (![A_5, B_6, D_130]: (k1_enumset1(A_5, A_5, B_6)=D_130 | k2_tarski(A_5, B_6)=D_130 | k2_tarski(A_5, B_6)=D_130 | k2_tarski(A_5, A_5)=D_130 | k1_tarski(B_6)=D_130 | k1_tarski(A_5)=D_130 | k1_tarski(A_5)=D_130 | k1_xboole_0=D_130 | ~r1_tarski(D_130, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_720])).
% 12.25/4.75  tff(c_14994, plain, (![A_748, B_749, D_750]: (k2_tarski(A_748, B_749)=D_750 | k2_tarski(A_748, B_749)=D_750 | k2_tarski(A_748, B_749)=D_750 | k1_tarski(A_748)=D_750 | k1_tarski(B_749)=D_750 | k1_tarski(A_748)=D_750 | k1_tarski(A_748)=D_750 | k1_xboole_0=D_750 | ~r1_tarski(D_750, k2_tarski(A_748, B_749)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_735])).
% 12.25/4.75  tff(c_15037, plain, (![A_4, D_750]: (k2_tarski(A_4, A_4)=D_750 | k2_tarski(A_4, A_4)=D_750 | k2_tarski(A_4, A_4)=D_750 | k1_tarski(A_4)=D_750 | k1_tarski(A_4)=D_750 | k1_tarski(A_4)=D_750 | k1_tarski(A_4)=D_750 | k1_xboole_0=D_750 | ~r1_tarski(D_750, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_14994])).
% 12.25/4.75  tff(c_22047, plain, (![A_914, D_915]: (k1_tarski(A_914)=D_915 | k1_tarski(A_914)=D_915 | k1_tarski(A_914)=D_915 | k1_tarski(A_914)=D_915 | k1_tarski(A_914)=D_915 | k1_tarski(A_914)=D_915 | k1_tarski(A_914)=D_915 | k1_xboole_0=D_915 | ~r1_tarski(D_915, k1_tarski(A_914)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_10, c_15037])).
% 12.25/4.75  tff(c_22112, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_407, c_22047])).
% 12.25/4.75  tff(c_22138, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_674, c_674, c_674, c_674, c_674, c_674, c_674, c_22112])).
% 12.25/4.75  tff(c_337, plain, (![A_96]: (m1_subset_1(A_96, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_96), k2_relat_1(A_96)))) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_116])).
% 12.25/4.75  tff(c_346, plain, (![A_97]: (r1_tarski(A_97, k2_zfmisc_1(k1_relat_1(A_97), k2_relat_1(A_97))) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_337, c_40])).
% 12.25/4.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.25/4.75  tff(c_353, plain, (![A_97]: (k2_zfmisc_1(k1_relat_1(A_97), k2_relat_1(A_97))=A_97 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_97), k2_relat_1(A_97)), A_97) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_346, c_2])).
% 12.25/4.75  tff(c_22159, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')), '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22138, c_353])).
% 12.25/4.75  tff(c_22188, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_267, c_72, c_8, c_20, c_20, c_22138, c_22159])).
% 12.25/4.75  tff(c_22305, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_22188, c_8])).
% 12.25/4.75  tff(c_46, plain, (![A_20]: (k9_relat_1(k1_xboole_0, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.25/4.75  tff(c_22302, plain, (![A_20]: (k9_relat_1('#skF_4', A_20)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22188, c_22188, c_46])).
% 12.25/4.75  tff(c_22638, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22302, c_479])).
% 12.25/4.75  tff(c_22642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22305, c_22638])).
% 12.25/4.75  tff(c_22644, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_583])).
% 12.25/4.75  tff(c_410, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | ~r1_tarski(k1_tarski('#skF_1'), k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_407, c_2])).
% 12.25/4.75  tff(c_411, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_410])).
% 12.25/4.75  tff(c_22646, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22644, c_411])).
% 12.25/4.75  tff(c_22656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_22646])).
% 12.25/4.75  tff(c_22657, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_410])).
% 12.25/4.75  tff(c_48, plain, (![B_22, A_21]: (k1_tarski(k1_funct_1(B_22, A_21))=k2_relat_1(B_22) | k1_tarski(A_21)!=k1_relat_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.25/4.75  tff(c_22665, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22657, c_68])).
% 12.25/4.75  tff(c_56, plain, (![A_32, B_33, C_34, D_35]: (k7_relset_1(A_32, B_33, C_34, D_35)=k9_relat_1(C_34, D_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.25/4.75  tff(c_22736, plain, (![D_35]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_35)=k9_relat_1('#skF_4', D_35))), inference(resolution, [status(thm)], [c_22665, c_56])).
% 12.25/4.75  tff(c_22663, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22657, c_64])).
% 12.25/4.75  tff(c_22843, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22736, c_22663])).
% 12.25/4.75  tff(c_22855, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_22843])).
% 12.25/4.75  tff(c_22857, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_267, c_72, c_22657, c_22855])).
% 12.25/4.75  tff(c_22860, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_22857])).
% 12.25/4.75  tff(c_22864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_267, c_22860])).
% 12.25/4.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.25/4.75  
% 12.25/4.75  Inference rules
% 12.25/4.75  ----------------------
% 12.25/4.75  #Ref     : 0
% 12.25/4.75  #Sup     : 5057
% 12.25/4.75  #Fact    : 0
% 12.25/4.75  #Define  : 0
% 12.25/4.75  #Split   : 6
% 12.25/4.75  #Chain   : 0
% 12.25/4.75  #Close   : 0
% 12.25/4.75  
% 12.25/4.75  Ordering : KBO
% 12.25/4.75  
% 12.25/4.75  Simplification rules
% 12.25/4.75  ----------------------
% 12.25/4.75  #Subsume      : 744
% 12.25/4.75  #Demod        : 9640
% 12.25/4.75  #Tautology    : 2084
% 12.25/4.75  #SimpNegUnit  : 4
% 12.25/4.75  #BackRed      : 249
% 12.25/4.75  
% 12.25/4.75  #Partial instantiations: 0
% 12.25/4.75  #Strategies tried      : 1
% 12.25/4.75  
% 12.25/4.75  Timing (in seconds)
% 12.25/4.75  ----------------------
% 12.25/4.75  Preprocessing        : 0.35
% 12.25/4.75  Parsing              : 0.19
% 12.25/4.75  CNF conversion       : 0.02
% 12.25/4.75  Main loop            : 3.61
% 12.25/4.75  Inferencing          : 0.87
% 12.25/4.75  Reduction            : 1.46
% 12.25/4.75  Demodulation         : 1.18
% 12.25/4.75  BG Simplification    : 0.12
% 12.25/4.75  Subsumption          : 0.96
% 12.25/4.75  Abstraction          : 0.20
% 12.25/4.75  MUC search           : 0.00
% 12.25/4.75  Cooper               : 0.00
% 12.25/4.75  Total                : 4.01
% 12.25/4.75  Index Insertion      : 0.00
% 12.25/4.75  Index Deletion       : 0.00
% 12.25/4.75  Index Matching       : 0.00
% 12.25/4.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
