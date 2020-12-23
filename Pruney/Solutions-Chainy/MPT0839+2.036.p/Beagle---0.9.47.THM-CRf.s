%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:26 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 636 expanded)
%              Number of leaves         :   45 ( 230 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 (1422 expanded)
%              Number of equality atoms :   36 ( 260 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,(
    ! [A_41,B_42] : v1_relat_1(k2_zfmisc_1(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_62,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_116,plain,(
    ! [B_87,A_88] :
      ( v1_relat_1(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88))
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_122,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_62,c_116])).

tff(c_129,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_122])).

tff(c_229,plain,(
    ! [C_111,A_112,B_113] :
      ( v4_relat_1(C_111,A_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_247,plain,(
    v4_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_229])).

tff(c_30,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(B_21),A_20)
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_249,plain,(
    ! [C_114,B_115,A_116] :
      ( r2_hidden(C_114,B_115)
      | ~ r2_hidden(C_114,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10541,plain,(
    ! [A_819,B_820,B_821] :
      ( r2_hidden('#skF_1'(A_819,B_820),B_821)
      | ~ r1_tarski(A_819,B_821)
      | r1_tarski(A_819,B_820) ) ),
    inference(resolution,[status(thm)],[c_6,c_249])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_11154,plain,(
    ! [A_859,B_860,B_861] :
      ( m1_subset_1('#skF_1'(A_859,B_860),B_861)
      | ~ r1_tarski(A_859,B_861)
      | r1_tarski(A_859,B_860) ) ),
    inference(resolution,[status(thm)],[c_10541,c_18])).

tff(c_8583,plain,(
    ! [A_673,B_674,C_675] :
      ( k1_relset_1(A_673,B_674,C_675) = k1_relat_1(C_675)
      | ~ m1_subset_1(C_675,k1_zfmisc_1(k2_zfmisc_1(A_673,B_674))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8601,plain,(
    k1_relset_1('#skF_9','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_8583])).

tff(c_154,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_1'(A_91,B_92),A_91)
      | r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [D_69] :
      ( ~ r2_hidden(D_69,k1_relset_1('#skF_9','#skF_8','#skF_10'))
      | ~ m1_subset_1(D_69,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_168,plain,(
    ! [B_92] :
      ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_9','#skF_8','#skF_10'),B_92),'#skF_9')
      | r1_tarski(k1_relset_1('#skF_9','#skF_8','#skF_10'),B_92) ) ),
    inference(resolution,[status(thm)],[c_154,c_58])).

tff(c_8612,plain,(
    ! [B_92] :
      ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_10'),B_92),'#skF_9')
      | r1_tarski(k1_relat_1('#skF_10'),B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8601,c_8601,c_168])).

tff(c_11228,plain,(
    ! [B_860] :
      ( ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9')
      | r1_tarski(k1_relat_1('#skF_10'),B_860) ) ),
    inference(resolution,[status(thm)],[c_11154,c_8612])).

tff(c_11303,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_11228])).

tff(c_11306,plain,
    ( ~ v4_relat_1('#skF_10','#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_11303])).

tff(c_11310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_247,c_11306])).

tff(c_11311,plain,(
    ! [B_860] : r1_tarski(k1_relat_1('#skF_10'),B_860) ),
    inference(splitRight,[status(thm)],[c_11228])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_334,plain,(
    ! [A_126,C_127,B_128] :
      ( m1_subset_1(A_126,C_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(C_127))
      | ~ r2_hidden(A_126,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_347,plain,(
    ! [A_126,A_9] :
      ( m1_subset_1(A_126,A_9)
      | ~ r2_hidden(A_126,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_334])).

tff(c_11031,plain,(
    ! [A_854,B_855,A_856] :
      ( m1_subset_1('#skF_1'(A_854,B_855),A_856)
      | ~ r1_tarski(A_854,k1_xboole_0)
      | r1_tarski(A_854,B_855) ) ),
    inference(resolution,[status(thm)],[c_10541,c_347])).

tff(c_11105,plain,(
    ! [B_855] :
      ( ~ r1_tarski(k1_relat_1('#skF_10'),k1_xboole_0)
      | r1_tarski(k1_relat_1('#skF_10'),B_855) ) ),
    inference(resolution,[status(thm)],[c_11031,c_8612])).

tff(c_11115,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11105])).

tff(c_11316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11311,c_11115])).

tff(c_11348,plain,(
    ! [B_866] : r1_tarski(k1_relat_1('#skF_10'),B_866) ),
    inference(splitRight,[status(thm)],[c_11105])).

tff(c_89,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(B_82,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_101,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_89])).

tff(c_11417,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11348,c_101])).

tff(c_454,plain,(
    ! [A_141] :
      ( k1_xboole_0 = A_141
      | r2_hidden(k4_tarski('#skF_6'(A_141),'#skF_7'(A_141)),A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    ! [C_37,A_22,D_40] :
      ( r2_hidden(C_37,k1_relat_1(A_22))
      | ~ r2_hidden(k4_tarski(C_37,D_40),A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8549,plain,(
    ! [A_671] :
      ( r2_hidden('#skF_6'(A_671),k1_relat_1(A_671))
      | k1_xboole_0 = A_671
      | ~ v1_relat_1(A_671) ) ),
    inference(resolution,[status(thm)],[c_454,c_34])).

tff(c_8565,plain,(
    ! [A_671] :
      ( m1_subset_1('#skF_6'(A_671),k1_relat_1(A_671))
      | k1_xboole_0 = A_671
      | ~ v1_relat_1(A_671) ) ),
    inference(resolution,[status(thm)],[c_8549,c_18])).

tff(c_11481,plain,
    ( m1_subset_1('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_11417,c_8565])).

tff(c_11506,plain,
    ( m1_subset_1('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_11481])).

tff(c_11628,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_11506])).

tff(c_8431,plain,(
    ! [A_663,B_664,C_665] :
      ( k2_relset_1(A_663,B_664,C_665) = k2_relat_1(C_665)
      | ~ m1_subset_1(C_665,k1_zfmisc_1(k2_zfmisc_1(A_663,B_664))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8450,plain,(
    ! [A_663,B_664] : k2_relset_1(A_663,B_664,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_8431])).

tff(c_8727,plain,(
    ! [A_690,B_691,C_692] :
      ( m1_subset_1(k2_relset_1(A_690,B_691,C_692),k1_zfmisc_1(B_691))
      | ~ m1_subset_1(C_692,k1_zfmisc_1(k2_zfmisc_1(A_690,B_691))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8754,plain,(
    ! [B_664,A_663] :
      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_664))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_663,B_664))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8450,c_8727])).

tff(c_8769,plain,(
    ! [B_693] : m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_693)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8754])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8822,plain,(
    ! [B_696] : r1_tarski(k2_relat_1(k1_xboole_0),B_696) ),
    inference(resolution,[status(thm)],[c_8769,c_20])).

tff(c_8845,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8822,c_101])).

tff(c_11699,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11628,c_11628,c_8845])).

tff(c_8449,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_8431])).

tff(c_60,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8451,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8449,c_60])).

tff(c_11707,plain,(
    k2_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11628,c_8451])).

tff(c_11776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11699,c_11707])).

tff(c_11778,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_11506])).

tff(c_478,plain,(
    ! [A_141] :
      ( r2_hidden('#skF_6'(A_141),k1_relat_1(A_141))
      | k1_xboole_0 = A_141
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_454,c_34])).

tff(c_11484,plain,
    ( r2_hidden('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_11417,c_478])).

tff(c_11508,plain,
    ( r2_hidden('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_11484])).

tff(c_11779,plain,(
    r2_hidden('#skF_6'('#skF_10'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_11778,c_11508])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_345,plain,(
    ! [A_126,B_13,A_12] :
      ( m1_subset_1(A_126,B_13)
      | ~ r2_hidden(A_126,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_334])).

tff(c_11784,plain,(
    ! [B_13] :
      ( m1_subset_1('#skF_6'('#skF_10'),B_13)
      | ~ r1_tarski(k1_xboole_0,B_13) ) ),
    inference(resolution,[status(thm)],[c_11779,c_345])).

tff(c_11795,plain,(
    ! [B_13] : m1_subset_1('#skF_6'('#skF_10'),B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_11784])).

tff(c_8618,plain,(
    ! [D_678] :
      ( ~ r2_hidden(D_678,k1_relat_1('#skF_10'))
      | ~ m1_subset_1(D_678,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8601,c_58])).

tff(c_8622,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9')
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_478,c_8618])).

tff(c_8633,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9')
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_8622])).

tff(c_8638,plain,(
    ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_8633])).

tff(c_11805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11795,c_8638])).

tff(c_11806,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_8633])).

tff(c_11815,plain,(
    k2_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11806,c_8451])).

tff(c_11832,plain,(
    ! [A_9] : m1_subset_1('#skF_10',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11806,c_16])).

tff(c_12118,plain,(
    ! [A_896,B_897] : k2_relset_1(A_896,B_897,'#skF_10') = k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11806,c_11806,c_8450])).

tff(c_52,plain,(
    ! [A_49,B_50,C_51] :
      ( m1_subset_1(k2_relset_1(A_49,B_50,C_51),k1_zfmisc_1(B_50))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12123,plain,(
    ! [B_897,A_896] :
      ( m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(B_897))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(A_896,B_897))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12118,c_52])).

tff(c_12131,plain,(
    ! [B_898] : m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(B_898)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11832,c_12123])).

tff(c_12166,plain,(
    ! [B_900] : r1_tarski(k2_relat_1('#skF_10'),B_900) ),
    inference(resolution,[status(thm)],[c_12131,c_20])).

tff(c_11831,plain,(
    ! [A_8] :
      ( A_8 = '#skF_10'
      | ~ r1_tarski(A_8,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11806,c_11806,c_101])).

tff(c_12170,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_12166,c_11831])).

tff(c_12187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11815,c_12170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.58/2.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.58/2.82  
% 7.58/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.83  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 7.91/2.83  
% 7.91/2.83  %Foreground sorts:
% 7.91/2.83  
% 7.91/2.83  
% 7.91/2.83  %Background operators:
% 7.91/2.83  
% 7.91/2.83  
% 7.91/2.83  %Foreground operators:
% 7.91/2.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.91/2.83  tff('#skF_7', type, '#skF_7': $i > $i).
% 7.91/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.91/2.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.91/2.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.91/2.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.91/2.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.91/2.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.91/2.83  tff('#skF_10', type, '#skF_10': $i).
% 7.91/2.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.91/2.83  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.91/2.83  tff('#skF_9', type, '#skF_9': $i).
% 7.91/2.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.91/2.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.91/2.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.91/2.83  tff('#skF_8', type, '#skF_8': $i).
% 7.91/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.91/2.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.91/2.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.91/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.91/2.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.91/2.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.91/2.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.91/2.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.91/2.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.91/2.83  tff('#skF_6', type, '#skF_6': $i > $i).
% 7.91/2.83  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.91/2.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.91/2.83  
% 7.91/2.84  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.91/2.84  tff(f_79, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.91/2.84  tff(f_126, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 7.91/2.84  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.91/2.84  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.91/2.84  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.91/2.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.91/2.84  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 7.91/2.84  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.91/2.84  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.91/2.84  tff(f_56, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.91/2.84  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.91/2.84  tff(f_87, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 7.91/2.84  tff(f_77, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 7.91/2.84  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.91/2.84  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 7.91/2.84  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.91/2.84  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.91/2.84  tff(c_44, plain, (![A_41, B_42]: (v1_relat_1(k2_zfmisc_1(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.91/2.84  tff(c_62, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.91/2.84  tff(c_116, plain, (![B_87, A_88]: (v1_relat_1(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.91/2.84  tff(c_122, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_62, c_116])).
% 7.91/2.84  tff(c_129, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_122])).
% 7.91/2.84  tff(c_229, plain, (![C_111, A_112, B_113]: (v4_relat_1(C_111, A_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.91/2.84  tff(c_247, plain, (v4_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_62, c_229])).
% 7.91/2.84  tff(c_30, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(B_21), A_20) | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.91/2.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.91/2.84  tff(c_249, plain, (![C_114, B_115, A_116]: (r2_hidden(C_114, B_115) | ~r2_hidden(C_114, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.91/2.84  tff(c_10541, plain, (![A_819, B_820, B_821]: (r2_hidden('#skF_1'(A_819, B_820), B_821) | ~r1_tarski(A_819, B_821) | r1_tarski(A_819, B_820))), inference(resolution, [status(thm)], [c_6, c_249])).
% 7.91/2.84  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.91/2.84  tff(c_11154, plain, (![A_859, B_860, B_861]: (m1_subset_1('#skF_1'(A_859, B_860), B_861) | ~r1_tarski(A_859, B_861) | r1_tarski(A_859, B_860))), inference(resolution, [status(thm)], [c_10541, c_18])).
% 7.91/2.84  tff(c_8583, plain, (![A_673, B_674, C_675]: (k1_relset_1(A_673, B_674, C_675)=k1_relat_1(C_675) | ~m1_subset_1(C_675, k1_zfmisc_1(k2_zfmisc_1(A_673, B_674))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.91/2.84  tff(c_8601, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_62, c_8583])).
% 7.91/2.84  tff(c_154, plain, (![A_91, B_92]: (r2_hidden('#skF_1'(A_91, B_92), A_91) | r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.91/2.84  tff(c_58, plain, (![D_69]: (~r2_hidden(D_69, k1_relset_1('#skF_9', '#skF_8', '#skF_10')) | ~m1_subset_1(D_69, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.91/2.84  tff(c_168, plain, (![B_92]: (~m1_subset_1('#skF_1'(k1_relset_1('#skF_9', '#skF_8', '#skF_10'), B_92), '#skF_9') | r1_tarski(k1_relset_1('#skF_9', '#skF_8', '#skF_10'), B_92))), inference(resolution, [status(thm)], [c_154, c_58])).
% 7.91/2.84  tff(c_8612, plain, (![B_92]: (~m1_subset_1('#skF_1'(k1_relat_1('#skF_10'), B_92), '#skF_9') | r1_tarski(k1_relat_1('#skF_10'), B_92))), inference(demodulation, [status(thm), theory('equality')], [c_8601, c_8601, c_168])).
% 7.91/2.84  tff(c_11228, plain, (![B_860]: (~r1_tarski(k1_relat_1('#skF_10'), '#skF_9') | r1_tarski(k1_relat_1('#skF_10'), B_860))), inference(resolution, [status(thm)], [c_11154, c_8612])).
% 7.91/2.84  tff(c_11303, plain, (~r1_tarski(k1_relat_1('#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_11228])).
% 7.91/2.84  tff(c_11306, plain, (~v4_relat_1('#skF_10', '#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_30, c_11303])).
% 7.91/2.84  tff(c_11310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_247, c_11306])).
% 7.91/2.84  tff(c_11311, plain, (![B_860]: (r1_tarski(k1_relat_1('#skF_10'), B_860))), inference(splitRight, [status(thm)], [c_11228])).
% 7.91/2.84  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.91/2.84  tff(c_334, plain, (![A_126, C_127, B_128]: (m1_subset_1(A_126, C_127) | ~m1_subset_1(B_128, k1_zfmisc_1(C_127)) | ~r2_hidden(A_126, B_128))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.91/2.84  tff(c_347, plain, (![A_126, A_9]: (m1_subset_1(A_126, A_9) | ~r2_hidden(A_126, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_334])).
% 7.91/2.84  tff(c_11031, plain, (![A_854, B_855, A_856]: (m1_subset_1('#skF_1'(A_854, B_855), A_856) | ~r1_tarski(A_854, k1_xboole_0) | r1_tarski(A_854, B_855))), inference(resolution, [status(thm)], [c_10541, c_347])).
% 7.91/2.84  tff(c_11105, plain, (![B_855]: (~r1_tarski(k1_relat_1('#skF_10'), k1_xboole_0) | r1_tarski(k1_relat_1('#skF_10'), B_855))), inference(resolution, [status(thm)], [c_11031, c_8612])).
% 7.91/2.84  tff(c_11115, plain, (~r1_tarski(k1_relat_1('#skF_10'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11105])).
% 7.91/2.84  tff(c_11316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11311, c_11115])).
% 7.91/2.84  tff(c_11348, plain, (![B_866]: (r1_tarski(k1_relat_1('#skF_10'), B_866))), inference(splitRight, [status(thm)], [c_11105])).
% 7.91/2.84  tff(c_89, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(B_82, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.91/2.84  tff(c_101, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_89])).
% 7.91/2.84  tff(c_11417, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_11348, c_101])).
% 7.91/2.84  tff(c_454, plain, (![A_141]: (k1_xboole_0=A_141 | r2_hidden(k4_tarski('#skF_6'(A_141), '#skF_7'(A_141)), A_141) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.91/2.84  tff(c_34, plain, (![C_37, A_22, D_40]: (r2_hidden(C_37, k1_relat_1(A_22)) | ~r2_hidden(k4_tarski(C_37, D_40), A_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.91/2.84  tff(c_8549, plain, (![A_671]: (r2_hidden('#skF_6'(A_671), k1_relat_1(A_671)) | k1_xboole_0=A_671 | ~v1_relat_1(A_671))), inference(resolution, [status(thm)], [c_454, c_34])).
% 7.91/2.84  tff(c_8565, plain, (![A_671]: (m1_subset_1('#skF_6'(A_671), k1_relat_1(A_671)) | k1_xboole_0=A_671 | ~v1_relat_1(A_671))), inference(resolution, [status(thm)], [c_8549, c_18])).
% 7.91/2.84  tff(c_11481, plain, (m1_subset_1('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_11417, c_8565])).
% 7.91/2.84  tff(c_11506, plain, (m1_subset_1('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_11481])).
% 7.91/2.84  tff(c_11628, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_11506])).
% 7.91/2.84  tff(c_8431, plain, (![A_663, B_664, C_665]: (k2_relset_1(A_663, B_664, C_665)=k2_relat_1(C_665) | ~m1_subset_1(C_665, k1_zfmisc_1(k2_zfmisc_1(A_663, B_664))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.91/2.84  tff(c_8450, plain, (![A_663, B_664]: (k2_relset_1(A_663, B_664, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_8431])).
% 7.91/2.84  tff(c_8727, plain, (![A_690, B_691, C_692]: (m1_subset_1(k2_relset_1(A_690, B_691, C_692), k1_zfmisc_1(B_691)) | ~m1_subset_1(C_692, k1_zfmisc_1(k2_zfmisc_1(A_690, B_691))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.91/2.84  tff(c_8754, plain, (![B_664, A_663]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_664)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_663, B_664))))), inference(superposition, [status(thm), theory('equality')], [c_8450, c_8727])).
% 7.91/2.84  tff(c_8769, plain, (![B_693]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_693)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8754])).
% 7.91/2.84  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.91/2.84  tff(c_8822, plain, (![B_696]: (r1_tarski(k2_relat_1(k1_xboole_0), B_696))), inference(resolution, [status(thm)], [c_8769, c_20])).
% 7.91/2.84  tff(c_8845, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8822, c_101])).
% 7.91/2.84  tff(c_11699, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_11628, c_11628, c_8845])).
% 7.91/2.84  tff(c_8449, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_62, c_8431])).
% 7.91/2.84  tff(c_60, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.91/2.84  tff(c_8451, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8449, c_60])).
% 7.91/2.84  tff(c_11707, plain, (k2_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_11628, c_8451])).
% 7.91/2.84  tff(c_11776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11699, c_11707])).
% 7.91/2.84  tff(c_11778, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_11506])).
% 7.91/2.84  tff(c_478, plain, (![A_141]: (r2_hidden('#skF_6'(A_141), k1_relat_1(A_141)) | k1_xboole_0=A_141 | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_454, c_34])).
% 7.91/2.84  tff(c_11484, plain, (r2_hidden('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_11417, c_478])).
% 7.91/2.84  tff(c_11508, plain, (r2_hidden('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_11484])).
% 7.91/2.84  tff(c_11779, plain, (r2_hidden('#skF_6'('#skF_10'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_11778, c_11508])).
% 7.91/2.84  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.91/2.84  tff(c_345, plain, (![A_126, B_13, A_12]: (m1_subset_1(A_126, B_13) | ~r2_hidden(A_126, A_12) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_22, c_334])).
% 7.91/2.84  tff(c_11784, plain, (![B_13]: (m1_subset_1('#skF_6'('#skF_10'), B_13) | ~r1_tarski(k1_xboole_0, B_13))), inference(resolution, [status(thm)], [c_11779, c_345])).
% 7.91/2.84  tff(c_11795, plain, (![B_13]: (m1_subset_1('#skF_6'('#skF_10'), B_13))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_11784])).
% 7.91/2.84  tff(c_8618, plain, (![D_678]: (~r2_hidden(D_678, k1_relat_1('#skF_10')) | ~m1_subset_1(D_678, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_8601, c_58])).
% 7.91/2.84  tff(c_8622, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9') | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_478, c_8618])).
% 7.91/2.84  tff(c_8633, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9') | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_8622])).
% 7.91/2.84  tff(c_8638, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_8633])).
% 7.91/2.84  tff(c_11805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11795, c_8638])).
% 7.91/2.84  tff(c_11806, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_8633])).
% 7.91/2.84  tff(c_11815, plain, (k2_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_11806, c_8451])).
% 7.91/2.84  tff(c_11832, plain, (![A_9]: (m1_subset_1('#skF_10', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_11806, c_16])).
% 7.91/2.84  tff(c_12118, plain, (![A_896, B_897]: (k2_relset_1(A_896, B_897, '#skF_10')=k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_11806, c_11806, c_8450])).
% 7.91/2.84  tff(c_52, plain, (![A_49, B_50, C_51]: (m1_subset_1(k2_relset_1(A_49, B_50, C_51), k1_zfmisc_1(B_50)) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.91/2.84  tff(c_12123, plain, (![B_897, A_896]: (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(B_897)) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(A_896, B_897))))), inference(superposition, [status(thm), theory('equality')], [c_12118, c_52])).
% 7.91/2.84  tff(c_12131, plain, (![B_898]: (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(B_898)))), inference(demodulation, [status(thm), theory('equality')], [c_11832, c_12123])).
% 7.91/2.85  tff(c_12166, plain, (![B_900]: (r1_tarski(k2_relat_1('#skF_10'), B_900))), inference(resolution, [status(thm)], [c_12131, c_20])).
% 7.91/2.85  tff(c_11831, plain, (![A_8]: (A_8='#skF_10' | ~r1_tarski(A_8, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_11806, c_11806, c_101])).
% 7.91/2.85  tff(c_12170, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_12166, c_11831])).
% 7.91/2.85  tff(c_12187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11815, c_12170])).
% 7.91/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.85  
% 7.91/2.85  Inference rules
% 7.91/2.85  ----------------------
% 7.91/2.85  #Ref     : 0
% 7.91/2.85  #Sup     : 2469
% 7.91/2.85  #Fact    : 0
% 7.91/2.85  #Define  : 0
% 7.91/2.85  #Split   : 54
% 7.91/2.85  #Chain   : 0
% 7.91/2.85  #Close   : 0
% 7.91/2.85  
% 7.91/2.85  Ordering : KBO
% 7.91/2.85  
% 7.91/2.85  Simplification rules
% 7.91/2.85  ----------------------
% 7.91/2.85  #Subsume      : 302
% 7.91/2.85  #Demod        : 2205
% 7.91/2.85  #Tautology    : 1002
% 7.91/2.85  #SimpNegUnit  : 135
% 7.91/2.85  #BackRed      : 318
% 7.91/2.85  
% 7.91/2.85  #Partial instantiations: 0
% 7.91/2.85  #Strategies tried      : 1
% 7.91/2.85  
% 7.91/2.85  Timing (in seconds)
% 7.91/2.85  ----------------------
% 7.91/2.85  Preprocessing        : 0.33
% 7.91/2.85  Parsing              : 0.17
% 7.91/2.85  CNF conversion       : 0.03
% 7.91/2.85  Main loop            : 1.69
% 7.91/2.85  Inferencing          : 0.55
% 7.91/2.85  Reduction            : 0.58
% 7.91/2.85  Demodulation         : 0.41
% 7.91/2.85  BG Simplification    : 0.06
% 7.91/2.85  Subsumption          : 0.33
% 7.91/2.85  Abstraction          : 0.08
% 7.91/2.85  MUC search           : 0.00
% 7.91/2.85  Cooper               : 0.00
% 7.91/2.85  Total                : 2.06
% 7.91/2.85  Index Insertion      : 0.00
% 7.91/2.85  Index Deletion       : 0.00
% 7.91/2.85  Index Matching       : 0.00
% 7.91/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
