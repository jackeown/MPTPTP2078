%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:28 EST 2020

% Result     : Theorem 8.80s
% Output     : CNFRefutation 8.80s
% Verified   : 
% Statistics : Number of formulae       :  253 (2333 expanded)
%              Number of leaves         :   44 ( 784 expanded)
%              Depth                    :   17
%              Number of atoms          :  377 (5257 expanded)
%              Number of equality atoms :  108 (1093 expanded)
%              Maximal formula depth    :   13 (   3 average)
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

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_122,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
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
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    ! [A_38,B_39] : v1_relat_1(k2_zfmisc_1(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_60,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_147,plain,(
    ! [B_87,A_88] :
      ( v1_relat_1(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88))
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_153,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_60,c_147])).

tff(c_157,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_153])).

tff(c_259,plain,(
    ! [C_110,A_111,B_112] :
      ( v4_relat_1(C_110,A_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_279,plain,(
    v4_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_259])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_355,plain,(
    ! [C_127,B_128,A_129] :
      ( r2_hidden(C_127,B_128)
      | ~ r2_hidden(C_127,A_129)
      | ~ r1_tarski(A_129,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10017,plain,(
    ! [A_858,B_859,B_860] :
      ( r2_hidden('#skF_1'(A_858,B_859),B_860)
      | ~ r1_tarski(A_858,B_860)
      | r1_tarski(A_858,B_859) ) ),
    inference(resolution,[status(thm)],[c_6,c_355])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10823,plain,(
    ! [A_922,B_923,B_924] :
      ( m1_subset_1('#skF_1'(A_922,B_923),B_924)
      | ~ r1_tarski(A_922,B_924)
      | r1_tarski(A_922,B_923) ) ),
    inference(resolution,[status(thm)],[c_10017,c_18])).

tff(c_8150,plain,(
    ! [A_692,B_693,C_694] :
      ( k1_relset_1(A_692,B_693,C_694) = k1_relat_1(C_694)
      | ~ m1_subset_1(C_694,k1_zfmisc_1(k2_zfmisc_1(A_692,B_693))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8170,plain,(
    k1_relset_1('#skF_9','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_8150])).

tff(c_141,plain,(
    ! [D_86] :
      ( ~ r2_hidden(D_86,k1_relset_1('#skF_9','#skF_8','#skF_10'))
      | ~ m1_subset_1(D_86,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_146,plain,(
    ! [B_2] :
      ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_9','#skF_8','#skF_10'),B_2),'#skF_9')
      | r1_tarski(k1_relset_1('#skF_9','#skF_8','#skF_10'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_141])).

tff(c_8180,plain,(
    ! [B_2] :
      ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_10'),B_2),'#skF_9')
      | r1_tarski(k1_relat_1('#skF_10'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8170,c_8170,c_146])).

tff(c_10897,plain,(
    ! [B_923] :
      ( ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9')
      | r1_tarski(k1_relat_1('#skF_10'),B_923) ) ),
    inference(resolution,[status(thm)],[c_10823,c_8180])).

tff(c_10907,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_10897])).

tff(c_10910,plain,
    ( ~ v4_relat_1('#skF_10','#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_28,c_10907])).

tff(c_10914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_279,c_10910])).

tff(c_10918,plain,(
    ! [B_925] : r1_tarski(k1_relat_1('#skF_10'),B_925) ),
    inference(splitRight,[status(thm)],[c_10897])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10986,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10918,c_10])).

tff(c_8098,plain,(
    ! [A_685] :
      ( k1_xboole_0 = A_685
      | r2_hidden(k4_tarski('#skF_6'(A_685),'#skF_7'(A_685)),A_685)
      | ~ v1_relat_1(A_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ! [C_34,A_19,D_37] :
      ( r2_hidden(C_34,k1_relat_1(A_19))
      | ~ r2_hidden(k4_tarski(C_34,D_37),A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8247,plain,(
    ! [A_699] :
      ( r2_hidden('#skF_6'(A_699),k1_relat_1(A_699))
      | k1_xboole_0 = A_699
      | ~ v1_relat_1(A_699) ) ),
    inference(resolution,[status(thm)],[c_8098,c_32])).

tff(c_8264,plain,(
    ! [A_699] :
      ( m1_subset_1('#skF_6'(A_699),k1_relat_1(A_699))
      | k1_xboole_0 = A_699
      | ~ v1_relat_1(A_699) ) ),
    inference(resolution,[status(thm)],[c_8247,c_18])).

tff(c_11050,plain,
    ( m1_subset_1('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_10986,c_8264])).

tff(c_11083,plain,
    ( m1_subset_1('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_11050])).

tff(c_11293,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_11083])).

tff(c_8268,plain,(
    ! [A_700,B_701,C_702] :
      ( k2_relset_1(A_700,B_701,C_702) = k2_relat_1(C_702)
      | ~ m1_subset_1(C_702,k1_zfmisc_1(k2_zfmisc_1(A_700,B_701))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8288,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_8268])).

tff(c_58,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_8291,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8288,c_58])).

tff(c_11329,plain,(
    k2_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11293,c_8291])).

tff(c_7104,plain,(
    ! [A_597,B_598,C_599] :
      ( k2_relset_1(A_597,B_598,C_599) = k2_relat_1(C_599)
      | ~ m1_subset_1(C_599,k1_zfmisc_1(k2_zfmisc_1(A_597,B_598))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7118,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_7104])).

tff(c_5971,plain,(
    ! [A_539,B_540,B_541] :
      ( r2_hidden('#skF_1'(A_539,B_540),B_541)
      | ~ r1_tarski(A_539,B_541)
      | r1_tarski(A_539,B_540) ) ),
    inference(resolution,[status(thm)],[c_6,c_355])).

tff(c_6447,plain,(
    ! [A_572,B_573,B_574] :
      ( m1_subset_1('#skF_1'(A_572,B_573),B_574)
      | ~ r1_tarski(A_572,B_574)
      | r1_tarski(A_572,B_573) ) ),
    inference(resolution,[status(thm)],[c_5971,c_18])).

tff(c_5044,plain,(
    ! [A_464,B_465,C_466] :
      ( k1_relset_1(A_464,B_465,C_466) = k1_relat_1(C_466)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_464,B_465))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5064,plain,(
    k1_relset_1('#skF_9','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_5044])).

tff(c_5066,plain,(
    ! [B_2] :
      ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_10'),B_2),'#skF_9')
      | r1_tarski(k1_relat_1('#skF_10'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5064,c_5064,c_146])).

tff(c_6524,plain,(
    ! [B_573] :
      ( ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9')
      | r1_tarski(k1_relat_1('#skF_10'),B_573) ) ),
    inference(resolution,[status(thm)],[c_6447,c_5066])).

tff(c_6595,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_6524])).

tff(c_6598,plain,
    ( ~ v4_relat_1('#skF_10','#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_28,c_6595])).

tff(c_6602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_279,c_6598])).

tff(c_6606,plain,(
    ! [B_579] : r1_tarski(k1_relat_1('#skF_10'),B_579) ),
    inference(splitRight,[status(thm)],[c_6524])).

tff(c_6669,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6606,c_10])).

tff(c_472,plain,(
    ! [A_139] :
      ( k1_xboole_0 = A_139
      | r2_hidden(k4_tarski('#skF_6'(A_139),'#skF_7'(A_139)),A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5137,plain,(
    ! [A_471] :
      ( r2_hidden('#skF_6'(A_471),k1_relat_1(A_471))
      | k1_xboole_0 = A_471
      | ~ v1_relat_1(A_471) ) ),
    inference(resolution,[status(thm)],[c_472,c_32])).

tff(c_5154,plain,(
    ! [A_471] :
      ( m1_subset_1('#skF_6'(A_471),k1_relat_1(A_471))
      | k1_xboole_0 = A_471
      | ~ v1_relat_1(A_471) ) ),
    inference(resolution,[status(thm)],[c_5137,c_18])).

tff(c_6736,plain,
    ( m1_subset_1('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_6669,c_5154])).

tff(c_6756,plain,
    ( m1_subset_1('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_6736])).

tff(c_6840,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_6756])).

tff(c_5159,plain,(
    ! [A_472,B_473,C_474] :
      ( k2_relset_1(A_472,B_473,C_474) = k2_relat_1(C_474)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(A_472,B_473))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5179,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_5159])).

tff(c_5180,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5179,c_58])).

tff(c_6873,plain,(
    k2_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6840,c_5180])).

tff(c_3668,plain,(
    ! [A_391,B_392,B_393] :
      ( r2_hidden('#skF_1'(A_391,B_392),B_393)
      | ~ r1_tarski(A_391,B_393)
      | r1_tarski(A_391,B_392) ) ),
    inference(resolution,[status(thm)],[c_6,c_355])).

tff(c_4211,plain,(
    ! [A_436,B_437,B_438] :
      ( m1_subset_1('#skF_1'(A_436,B_437),B_438)
      | ~ r1_tarski(A_436,B_438)
      | r1_tarski(A_436,B_437) ) ),
    inference(resolution,[status(thm)],[c_3668,c_18])).

tff(c_2764,plain,(
    ! [A_314,B_315,C_316] :
      ( k1_relset_1(A_314,B_315,C_316) = k1_relat_1(C_316)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2784,plain,(
    k1_relset_1('#skF_9','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_2764])).

tff(c_2830,plain,(
    ! [B_2] :
      ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_10'),B_2),'#skF_9')
      | r1_tarski(k1_relat_1('#skF_10'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2784,c_2784,c_146])).

tff(c_4283,plain,(
    ! [B_437] :
      ( ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9')
      | r1_tarski(k1_relat_1('#skF_10'),B_437) ) ),
    inference(resolution,[status(thm)],[c_4211,c_2830])).

tff(c_4346,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4283])).

tff(c_4349,plain,
    ( ~ v4_relat_1('#skF_10','#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_28,c_4346])).

tff(c_4353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_279,c_4349])).

tff(c_4357,plain,(
    ! [B_442] : r1_tarski(k1_relat_1('#skF_10'),B_442) ),
    inference(splitRight,[status(thm)],[c_4283])).

tff(c_4421,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4357,c_10])).

tff(c_485,plain,(
    ! [A_139] :
      ( r2_hidden('#skF_6'(A_139),k1_relat_1(A_139))
      | k1_xboole_0 = A_139
      | ~ v1_relat_1(A_139) ) ),
    inference(resolution,[status(thm)],[c_472,c_32])).

tff(c_4506,plain,
    ( r2_hidden('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_4421,c_485])).

tff(c_4541,plain,
    ( r2_hidden('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_4506])).

tff(c_4670,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_4541])).

tff(c_2867,plain,(
    ! [A_322,B_323,C_324] :
      ( k2_relset_1(A_322,B_323,C_324) = k2_relat_1(C_324)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_322,B_323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2887,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60,c_2867])).

tff(c_2890,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2887,c_58])).

tff(c_4716,plain,(
    k2_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4670,c_2890])).

tff(c_113,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81,B_82),A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_174,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1('#skF_1'(A_91,B_92),A_91)
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_113,c_18])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_421,plain,(
    ! [B_136,B_137] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(B_136),B_137),B_136)
      | r1_tarski(k1_zfmisc_1(B_136),B_137) ) ),
    inference(resolution,[status(thm)],[c_174,c_20])).

tff(c_446,plain,(
    ! [B_138] :
      ( '#skF_1'(k1_zfmisc_1(k1_xboole_0),B_138) = k1_xboole_0
      | r1_tarski(k1_zfmisc_1(k1_xboole_0),B_138) ) ),
    inference(resolution,[status(thm)],[c_421,c_10])).

tff(c_470,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | '#skF_1'(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_446,c_10])).

tff(c_471,plain,(
    '#skF_1'(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_501,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_6])).

tff(c_2763,plain,(
    r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_2798,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2763,c_10])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2895,plain,(
    ! [A_325] :
      ( m1_subset_1(A_325,k1_xboole_0)
      | ~ r1_tarski(A_325,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2798,c_22])).

tff(c_2916,plain,(
    m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_2895])).

tff(c_14,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2881,plain,(
    ! [A_8,C_324] :
      ( k2_relset_1(A_8,k1_xboole_0,C_324) = k2_relat_1(C_324)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2867])).

tff(c_3039,plain,(
    ! [A_335,C_336] :
      ( k2_relset_1(A_335,k1_xboole_0,C_336) = k2_relat_1(C_336)
      | ~ m1_subset_1(C_336,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2798,c_2881])).

tff(c_3099,plain,(
    ! [A_340] : k2_relset_1(A_340,k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2916,c_3039])).

tff(c_50,plain,(
    ! [A_46,B_47,C_48] :
      ( m1_subset_1(k2_relset_1(A_46,B_47,C_48),k1_zfmisc_1(B_47))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3104,plain,(
    ! [A_340] :
      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_340,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3099,c_50])).

tff(c_3109,plain,(
    m1_subset_1(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2916,c_2798,c_14,c_2798,c_3104])).

tff(c_2936,plain,(
    ! [A_327] :
      ( r1_tarski(A_327,k1_xboole_0)
      | ~ m1_subset_1(A_327,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2798,c_20])).

tff(c_2959,plain,(
    ! [A_327] :
      ( k1_xboole_0 = A_327
      | ~ m1_subset_1(A_327,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2936,c_10])).

tff(c_3124,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3109,c_2959])).

tff(c_4707,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4670,c_4670,c_3124])).

tff(c_4860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4716,c_4707])).

tff(c_4862,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_4541])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_504,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_4])).

tff(c_510,plain,(
    ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_504])).

tff(c_4861,plain,(
    r2_hidden('#skF_6'('#skF_10'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4541])).

tff(c_4915,plain,(
    m1_subset_1('#skF_6'('#skF_10'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4861,c_18])).

tff(c_4956,plain,(
    '#skF_6'('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4915,c_2959])).

tff(c_4992,plain,
    ( r2_hidden(k1_xboole_0,k1_relat_1('#skF_10'))
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_4956,c_485])).

tff(c_5008,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_4421,c_4992])).

tff(c_5010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4862,c_510,c_5008])).

tff(c_5011,plain,(
    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_5024,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_5011,c_18])).

tff(c_16,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5192,plain,(
    ! [B_476,C_477] :
      ( k2_relset_1(k1_xboole_0,B_476,C_477) = k2_relat_1(C_477)
      | ~ m1_subset_1(C_477,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_5159])).

tff(c_5201,plain,(
    ! [B_476] : k2_relset_1(k1_xboole_0,B_476,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5024,c_5192])).

tff(c_5484,plain,(
    ! [A_510,B_511,C_512] :
      ( m1_subset_1(k2_relset_1(A_510,B_511,C_512),k1_zfmisc_1(B_511))
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(A_510,B_511))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5530,plain,(
    ! [B_476] :
      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_476))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_476))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5201,c_5484])).

tff(c_5571,plain,(
    ! [B_513] : m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_513)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5024,c_16,c_5530])).

tff(c_5637,plain,(
    ! [B_519] : r1_tarski(k2_relat_1(k1_xboole_0),B_519) ),
    inference(resolution,[status(thm)],[c_5571,c_20])).

tff(c_5679,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5637,c_10])).

tff(c_6860,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6840,c_6840,c_5679])).

tff(c_7015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6873,c_6860])).

tff(c_7017,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_6756])).

tff(c_6739,plain,
    ( r2_hidden('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_6669,c_485])).

tff(c_6758,plain,
    ( r2_hidden('#skF_6'('#skF_10'),k1_xboole_0)
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_6739])).

tff(c_7036,plain,(
    r2_hidden('#skF_6'('#skF_10'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_7017,c_6758])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7041,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_6'('#skF_10'),B_2)
      | ~ r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_7036,c_2])).

tff(c_7052,plain,(
    ! [B_596] : r2_hidden('#skF_6'('#skF_10'),B_596) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7041])).

tff(c_7065,plain,(
    ! [B_596] : m1_subset_1('#skF_6'('#skF_10'),B_596) ),
    inference(resolution,[status(thm)],[c_7052,c_18])).

tff(c_56,plain,(
    ! [D_66] :
      ( ~ r2_hidden(D_66,k1_relset_1('#skF_9','#skF_8','#skF_10'))
      | ~ m1_subset_1(D_66,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5067,plain,(
    ! [D_66] :
      ( ~ r2_hidden(D_66,k1_relat_1('#skF_10'))
      | ~ m1_subset_1(D_66,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5064,c_56])).

tff(c_5141,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9')
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_5137,c_5067])).

tff(c_5152,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9')
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_5141])).

tff(c_5158,plain,(
    ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5152])).

tff(c_7069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7065,c_5158])).

tff(c_7070,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_5152])).

tff(c_7094,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7070,c_58])).

tff(c_7283,plain,(
    k2_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7118,c_7094])).

tff(c_7076,plain,(
    r2_hidden('#skF_10',k1_zfmisc_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7070,c_7070,c_5011])).

tff(c_7282,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_7076,c_18])).

tff(c_7097,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_10',B_9) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7070,c_7070,c_16])).

tff(c_7232,plain,(
    ! [B_607] : k2_zfmisc_1('#skF_10',B_607) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7070,c_7070,c_16])).

tff(c_54,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_relset_1(A_52,B_53,C_54) = k2_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7846,plain,(
    ! [B_669,C_670] :
      ( k2_relset_1('#skF_10',B_669,C_670) = k2_relat_1(C_670)
      | ~ m1_subset_1(C_670,k1_zfmisc_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7232,c_54])).

tff(c_7888,plain,(
    ! [B_674] : k2_relset_1('#skF_10',B_674,'#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_7282,c_7846])).

tff(c_7897,plain,(
    ! [B_674] :
      ( m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(B_674))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_10',B_674))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7888,c_50])).

tff(c_7908,plain,(
    ! [B_676] : m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1(B_676)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7282,c_7097,c_7897])).

tff(c_7982,plain,(
    ! [B_680] : r1_tarski(k2_relat_1('#skF_10'),B_680) ),
    inference(resolution,[status(thm)],[c_7908,c_20])).

tff(c_7093,plain,(
    ! [A_7] :
      ( A_7 = '#skF_10'
      | ~ r1_tarski(A_7,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7070,c_7070,c_10])).

tff(c_8000,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_7982,c_7093])).

tff(c_8019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7283,c_8000])).

tff(c_8021,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_8023,plain,(
    ! [B_2] :
      ( r2_hidden(k1_xboole_0,B_2)
      | ~ r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_8021,c_2])).

tff(c_8032,plain,(
    ! [B_681] : r2_hidden(k1_xboole_0,B_681) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8023])).

tff(c_8045,plain,(
    ! [B_681] : m1_subset_1(k1_xboole_0,B_681) ),
    inference(resolution,[status(thm)],[c_8032,c_18])).

tff(c_8044,plain,(
    ~ m1_subset_1(k1_xboole_0,'#skF_9') ),
    inference(resolution,[status(thm)],[c_8032,c_56])).

tff(c_8070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8045,c_8044])).

tff(c_8071,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_8186,plain,(
    ! [A_696] :
      ( m1_subset_1(A_696,k1_xboole_0)
      | ~ r1_tarski(A_696,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8071,c_22])).

tff(c_8211,plain,(
    m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_8186])).

tff(c_8282,plain,(
    ! [A_8,C_702] :
      ( k2_relset_1(A_8,k1_xboole_0,C_702) = k2_relat_1(C_702)
      | ~ m1_subset_1(C_702,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_8268])).

tff(c_9596,plain,(
    ! [A_811,C_812] :
      ( k2_relset_1(A_811,k1_xboole_0,C_812) = k2_relat_1(C_812)
      | ~ m1_subset_1(C_812,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8071,c_8282])).

tff(c_9626,plain,(
    ! [A_815] : k2_relset_1(A_815,k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8211,c_9596])).

tff(c_9631,plain,(
    ! [A_815] :
      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_815,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9626,c_50])).

tff(c_9636,plain,(
    m1_subset_1(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8211,c_8071,c_14,c_8071,c_9631])).

tff(c_8130,plain,(
    ! [A_691] :
      ( r1_tarski(A_691,k1_xboole_0)
      | ~ m1_subset_1(A_691,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8071,c_20])).

tff(c_8149,plain,(
    ! [A_691] :
      ( k1_xboole_0 = A_691
      | ~ m1_subset_1(A_691,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8130,c_10])).

tff(c_9651,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9636,c_8149])).

tff(c_11326,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11293,c_11293,c_9651])).

tff(c_11498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11329,c_11326])).

tff(c_11500,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_11083])).

tff(c_11499,plain,(
    m1_subset_1('#skF_6'('#skF_10'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11083])).

tff(c_11526,plain,(
    '#skF_6'('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11499,c_8149])).

tff(c_8111,plain,(
    ! [A_685] :
      ( r2_hidden('#skF_6'(A_685),k1_relat_1(A_685))
      | k1_xboole_0 = A_685
      | ~ v1_relat_1(A_685) ) ),
    inference(resolution,[status(thm)],[c_8098,c_32])).

tff(c_11556,plain,
    ( r2_hidden(k1_xboole_0,k1_relat_1('#skF_10'))
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_11526,c_8111])).

tff(c_11572,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_10986,c_11556])).

tff(c_11573,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_11500,c_11572])).

tff(c_11582,plain,(
    ! [B_2] :
      ( r2_hidden(k1_xboole_0,B_2)
      | ~ r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_11573,c_2])).

tff(c_11593,plain,(
    ! [B_944] : r2_hidden(k1_xboole_0,B_944) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11582])).

tff(c_11606,plain,(
    ! [B_944] : m1_subset_1(k1_xboole_0,B_944) ),
    inference(resolution,[status(thm)],[c_11593,c_18])).

tff(c_8181,plain,(
    ! [D_66] :
      ( ~ r2_hidden(D_66,k1_relat_1('#skF_10'))
      | ~ m1_subset_1(D_66,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8170,c_56])).

tff(c_8251,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9')
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_8247,c_8181])).

tff(c_8262,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9')
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_8251])).

tff(c_8296,plain,(
    ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_8262])).

tff(c_11541,plain,(
    ~ m1_subset_1(k1_xboole_0,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11526,c_8296])).

tff(c_11646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11606,c_11541])).

tff(c_11647,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_8262])).

tff(c_11649,plain,(
    k2_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11647,c_8291])).

tff(c_11652,plain,(
    m1_subset_1('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11647,c_11647,c_8211])).

tff(c_11673,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_10',B_9) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11647,c_11647,c_16])).

tff(c_121,plain,(
    ! [A_81] : r1_tarski(A_81,A_81) ),
    inference(resolution,[status(thm)],[c_113,c_4])).

tff(c_12177,plain,(
    ! [A_993,B_994,A_995] :
      ( k2_relset_1(A_993,B_994,A_995) = k2_relat_1(A_995)
      | ~ r1_tarski(A_995,k2_zfmisc_1(A_993,B_994)) ) ),
    inference(resolution,[status(thm)],[c_22,c_8268])).

tff(c_12203,plain,(
    ! [A_993,B_994] : k2_relset_1(A_993,B_994,k2_zfmisc_1(A_993,B_994)) = k2_relat_1(k2_zfmisc_1(A_993,B_994)) ),
    inference(resolution,[status(thm)],[c_121,c_12177])).

tff(c_11661,plain,(
    k1_zfmisc_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11647,c_11647,c_8071])).

tff(c_11711,plain,(
    ! [A_950,B_951,C_952] :
      ( m1_subset_1(k2_relset_1(A_950,B_951,C_952),k1_zfmisc_1(B_951))
      | ~ m1_subset_1(C_952,k1_zfmisc_1(k2_zfmisc_1(A_950,B_951))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12628,plain,(
    ! [A_1039,B_1040,C_1041] :
      ( r1_tarski(k2_relset_1(A_1039,B_1040,C_1041),B_1040)
      | ~ m1_subset_1(C_1041,k1_zfmisc_1(k2_zfmisc_1(A_1039,B_1040))) ) ),
    inference(resolution,[status(thm)],[c_11711,c_20])).

tff(c_12633,plain,(
    ! [B_9,C_1041] :
      ( r1_tarski(k2_relset_1('#skF_10',B_9,C_1041),B_9)
      | ~ m1_subset_1(C_1041,k1_zfmisc_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11673,c_12628])).

tff(c_12655,plain,(
    ! [B_1042,C_1043] :
      ( r1_tarski(k2_relset_1('#skF_10',B_1042,C_1043),B_1042)
      | ~ m1_subset_1(C_1043,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11661,c_12633])).

tff(c_12702,plain,(
    ! [B_994] :
      ( r1_tarski(k2_relat_1(k2_zfmisc_1('#skF_10',B_994)),B_994)
      | ~ m1_subset_1(k2_zfmisc_1('#skF_10',B_994),'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12203,c_12655])).

tff(c_12724,plain,(
    ! [B_1044] : r1_tarski(k2_relat_1('#skF_10'),B_1044) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11652,c_11673,c_11673,c_12702])).

tff(c_11670,plain,(
    ! [A_7] :
      ( A_7 = '#skF_10'
      | ~ r1_tarski(A_7,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11647,c_11647,c_10])).

tff(c_12756,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_12724,c_11670])).

tff(c_12779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11649,c_12756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.80/3.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.80/3.04  
% 8.80/3.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.80/3.04  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 8.80/3.04  
% 8.80/3.04  %Foreground sorts:
% 8.80/3.04  
% 8.80/3.04  
% 8.80/3.04  %Background operators:
% 8.80/3.04  
% 8.80/3.04  
% 8.80/3.04  %Foreground operators:
% 8.80/3.04  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.80/3.04  tff('#skF_7', type, '#skF_7': $i > $i).
% 8.80/3.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.80/3.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.80/3.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.80/3.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.80/3.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.80/3.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.80/3.04  tff('#skF_10', type, '#skF_10': $i).
% 8.80/3.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.80/3.04  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.80/3.04  tff('#skF_9', type, '#skF_9': $i).
% 8.80/3.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.80/3.04  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.80/3.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.80/3.04  tff('#skF_8', type, '#skF_8': $i).
% 8.80/3.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.80/3.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.80/3.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.80/3.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.80/3.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.80/3.04  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.80/3.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.80/3.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.80/3.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.80/3.04  tff('#skF_6', type, '#skF_6': $i > $i).
% 8.80/3.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.80/3.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.80/3.04  
% 8.80/3.07  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.80/3.07  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.80/3.07  tff(f_122, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 8.80/3.07  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.80/3.07  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.80/3.07  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.80/3.07  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.80/3.07  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 8.80/3.07  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.80/3.07  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.80/3.07  tff(f_83, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 8.80/3.07  tff(f_73, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 8.80/3.07  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.80/3.07  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.80/3.07  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.80/3.07  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 8.80/3.07  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.80/3.07  tff(c_42, plain, (![A_38, B_39]: (v1_relat_1(k2_zfmisc_1(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.80/3.07  tff(c_60, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.80/3.07  tff(c_147, plain, (![B_87, A_88]: (v1_relat_1(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.80/3.07  tff(c_153, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_60, c_147])).
% 8.80/3.07  tff(c_157, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_153])).
% 8.80/3.07  tff(c_259, plain, (![C_110, A_111, B_112]: (v4_relat_1(C_110, A_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.80/3.07  tff(c_279, plain, (v4_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_60, c_259])).
% 8.80/3.07  tff(c_28, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.80/3.07  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.80/3.07  tff(c_355, plain, (![C_127, B_128, A_129]: (r2_hidden(C_127, B_128) | ~r2_hidden(C_127, A_129) | ~r1_tarski(A_129, B_128))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.80/3.07  tff(c_10017, plain, (![A_858, B_859, B_860]: (r2_hidden('#skF_1'(A_858, B_859), B_860) | ~r1_tarski(A_858, B_860) | r1_tarski(A_858, B_859))), inference(resolution, [status(thm)], [c_6, c_355])).
% 8.80/3.07  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.80/3.07  tff(c_10823, plain, (![A_922, B_923, B_924]: (m1_subset_1('#skF_1'(A_922, B_923), B_924) | ~r1_tarski(A_922, B_924) | r1_tarski(A_922, B_923))), inference(resolution, [status(thm)], [c_10017, c_18])).
% 8.80/3.07  tff(c_8150, plain, (![A_692, B_693, C_694]: (k1_relset_1(A_692, B_693, C_694)=k1_relat_1(C_694) | ~m1_subset_1(C_694, k1_zfmisc_1(k2_zfmisc_1(A_692, B_693))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.80/3.07  tff(c_8170, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_8150])).
% 8.80/3.07  tff(c_141, plain, (![D_86]: (~r2_hidden(D_86, k1_relset_1('#skF_9', '#skF_8', '#skF_10')) | ~m1_subset_1(D_86, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.80/3.07  tff(c_146, plain, (![B_2]: (~m1_subset_1('#skF_1'(k1_relset_1('#skF_9', '#skF_8', '#skF_10'), B_2), '#skF_9') | r1_tarski(k1_relset_1('#skF_9', '#skF_8', '#skF_10'), B_2))), inference(resolution, [status(thm)], [c_6, c_141])).
% 8.80/3.07  tff(c_8180, plain, (![B_2]: (~m1_subset_1('#skF_1'(k1_relat_1('#skF_10'), B_2), '#skF_9') | r1_tarski(k1_relat_1('#skF_10'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_8170, c_8170, c_146])).
% 8.80/3.07  tff(c_10897, plain, (![B_923]: (~r1_tarski(k1_relat_1('#skF_10'), '#skF_9') | r1_tarski(k1_relat_1('#skF_10'), B_923))), inference(resolution, [status(thm)], [c_10823, c_8180])).
% 8.80/3.07  tff(c_10907, plain, (~r1_tarski(k1_relat_1('#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_10897])).
% 8.80/3.07  tff(c_10910, plain, (~v4_relat_1('#skF_10', '#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_28, c_10907])).
% 8.80/3.07  tff(c_10914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_279, c_10910])).
% 8.80/3.07  tff(c_10918, plain, (![B_925]: (r1_tarski(k1_relat_1('#skF_10'), B_925))), inference(splitRight, [status(thm)], [c_10897])).
% 8.80/3.07  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.80/3.07  tff(c_10986, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_10918, c_10])).
% 8.80/3.07  tff(c_8098, plain, (![A_685]: (k1_xboole_0=A_685 | r2_hidden(k4_tarski('#skF_6'(A_685), '#skF_7'(A_685)), A_685) | ~v1_relat_1(A_685))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.80/3.07  tff(c_32, plain, (![C_34, A_19, D_37]: (r2_hidden(C_34, k1_relat_1(A_19)) | ~r2_hidden(k4_tarski(C_34, D_37), A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.80/3.07  tff(c_8247, plain, (![A_699]: (r2_hidden('#skF_6'(A_699), k1_relat_1(A_699)) | k1_xboole_0=A_699 | ~v1_relat_1(A_699))), inference(resolution, [status(thm)], [c_8098, c_32])).
% 8.80/3.07  tff(c_8264, plain, (![A_699]: (m1_subset_1('#skF_6'(A_699), k1_relat_1(A_699)) | k1_xboole_0=A_699 | ~v1_relat_1(A_699))), inference(resolution, [status(thm)], [c_8247, c_18])).
% 8.80/3.07  tff(c_11050, plain, (m1_subset_1('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_10986, c_8264])).
% 8.80/3.07  tff(c_11083, plain, (m1_subset_1('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_11050])).
% 8.80/3.07  tff(c_11293, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_11083])).
% 8.80/3.07  tff(c_8268, plain, (![A_700, B_701, C_702]: (k2_relset_1(A_700, B_701, C_702)=k2_relat_1(C_702) | ~m1_subset_1(C_702, k1_zfmisc_1(k2_zfmisc_1(A_700, B_701))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.80/3.07  tff(c_8288, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_8268])).
% 8.80/3.07  tff(c_58, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.80/3.07  tff(c_8291, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8288, c_58])).
% 8.80/3.07  tff(c_11329, plain, (k2_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_11293, c_8291])).
% 8.80/3.07  tff(c_7104, plain, (![A_597, B_598, C_599]: (k2_relset_1(A_597, B_598, C_599)=k2_relat_1(C_599) | ~m1_subset_1(C_599, k1_zfmisc_1(k2_zfmisc_1(A_597, B_598))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.80/3.07  tff(c_7118, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_7104])).
% 8.80/3.07  tff(c_5971, plain, (![A_539, B_540, B_541]: (r2_hidden('#skF_1'(A_539, B_540), B_541) | ~r1_tarski(A_539, B_541) | r1_tarski(A_539, B_540))), inference(resolution, [status(thm)], [c_6, c_355])).
% 8.80/3.07  tff(c_6447, plain, (![A_572, B_573, B_574]: (m1_subset_1('#skF_1'(A_572, B_573), B_574) | ~r1_tarski(A_572, B_574) | r1_tarski(A_572, B_573))), inference(resolution, [status(thm)], [c_5971, c_18])).
% 8.80/3.07  tff(c_5044, plain, (![A_464, B_465, C_466]: (k1_relset_1(A_464, B_465, C_466)=k1_relat_1(C_466) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_464, B_465))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.80/3.07  tff(c_5064, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_5044])).
% 8.80/3.07  tff(c_5066, plain, (![B_2]: (~m1_subset_1('#skF_1'(k1_relat_1('#skF_10'), B_2), '#skF_9') | r1_tarski(k1_relat_1('#skF_10'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_5064, c_5064, c_146])).
% 8.80/3.07  tff(c_6524, plain, (![B_573]: (~r1_tarski(k1_relat_1('#skF_10'), '#skF_9') | r1_tarski(k1_relat_1('#skF_10'), B_573))), inference(resolution, [status(thm)], [c_6447, c_5066])).
% 8.80/3.07  tff(c_6595, plain, (~r1_tarski(k1_relat_1('#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_6524])).
% 8.80/3.07  tff(c_6598, plain, (~v4_relat_1('#skF_10', '#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_28, c_6595])).
% 8.80/3.07  tff(c_6602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_279, c_6598])).
% 8.80/3.07  tff(c_6606, plain, (![B_579]: (r1_tarski(k1_relat_1('#skF_10'), B_579))), inference(splitRight, [status(thm)], [c_6524])).
% 8.80/3.07  tff(c_6669, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_6606, c_10])).
% 8.80/3.07  tff(c_472, plain, (![A_139]: (k1_xboole_0=A_139 | r2_hidden(k4_tarski('#skF_6'(A_139), '#skF_7'(A_139)), A_139) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.80/3.07  tff(c_5137, plain, (![A_471]: (r2_hidden('#skF_6'(A_471), k1_relat_1(A_471)) | k1_xboole_0=A_471 | ~v1_relat_1(A_471))), inference(resolution, [status(thm)], [c_472, c_32])).
% 8.80/3.07  tff(c_5154, plain, (![A_471]: (m1_subset_1('#skF_6'(A_471), k1_relat_1(A_471)) | k1_xboole_0=A_471 | ~v1_relat_1(A_471))), inference(resolution, [status(thm)], [c_5137, c_18])).
% 8.80/3.07  tff(c_6736, plain, (m1_subset_1('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_6669, c_5154])).
% 8.80/3.07  tff(c_6756, plain, (m1_subset_1('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_6736])).
% 8.80/3.07  tff(c_6840, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_6756])).
% 8.80/3.07  tff(c_5159, plain, (![A_472, B_473, C_474]: (k2_relset_1(A_472, B_473, C_474)=k2_relat_1(C_474) | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(A_472, B_473))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.80/3.07  tff(c_5179, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_5159])).
% 8.80/3.07  tff(c_5180, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5179, c_58])).
% 8.80/3.07  tff(c_6873, plain, (k2_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_6840, c_5180])).
% 8.80/3.07  tff(c_3668, plain, (![A_391, B_392, B_393]: (r2_hidden('#skF_1'(A_391, B_392), B_393) | ~r1_tarski(A_391, B_393) | r1_tarski(A_391, B_392))), inference(resolution, [status(thm)], [c_6, c_355])).
% 8.80/3.07  tff(c_4211, plain, (![A_436, B_437, B_438]: (m1_subset_1('#skF_1'(A_436, B_437), B_438) | ~r1_tarski(A_436, B_438) | r1_tarski(A_436, B_437))), inference(resolution, [status(thm)], [c_3668, c_18])).
% 8.80/3.07  tff(c_2764, plain, (![A_314, B_315, C_316]: (k1_relset_1(A_314, B_315, C_316)=k1_relat_1(C_316) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.80/3.07  tff(c_2784, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_2764])).
% 8.80/3.07  tff(c_2830, plain, (![B_2]: (~m1_subset_1('#skF_1'(k1_relat_1('#skF_10'), B_2), '#skF_9') | r1_tarski(k1_relat_1('#skF_10'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2784, c_2784, c_146])).
% 8.80/3.07  tff(c_4283, plain, (![B_437]: (~r1_tarski(k1_relat_1('#skF_10'), '#skF_9') | r1_tarski(k1_relat_1('#skF_10'), B_437))), inference(resolution, [status(thm)], [c_4211, c_2830])).
% 8.80/3.07  tff(c_4346, plain, (~r1_tarski(k1_relat_1('#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_4283])).
% 8.80/3.07  tff(c_4349, plain, (~v4_relat_1('#skF_10', '#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_28, c_4346])).
% 8.80/3.07  tff(c_4353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_279, c_4349])).
% 8.80/3.07  tff(c_4357, plain, (![B_442]: (r1_tarski(k1_relat_1('#skF_10'), B_442))), inference(splitRight, [status(thm)], [c_4283])).
% 8.80/3.07  tff(c_4421, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_4357, c_10])).
% 8.80/3.07  tff(c_485, plain, (![A_139]: (r2_hidden('#skF_6'(A_139), k1_relat_1(A_139)) | k1_xboole_0=A_139 | ~v1_relat_1(A_139))), inference(resolution, [status(thm)], [c_472, c_32])).
% 8.80/3.07  tff(c_4506, plain, (r2_hidden('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_4421, c_485])).
% 8.80/3.07  tff(c_4541, plain, (r2_hidden('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_4506])).
% 8.80/3.07  tff(c_4670, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_4541])).
% 8.80/3.07  tff(c_2867, plain, (![A_322, B_323, C_324]: (k2_relset_1(A_322, B_323, C_324)=k2_relat_1(C_324) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_322, B_323))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.80/3.07  tff(c_2887, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60, c_2867])).
% 8.80/3.07  tff(c_2890, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2887, c_58])).
% 8.80/3.07  tff(c_4716, plain, (k2_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_4670, c_2890])).
% 8.80/3.07  tff(c_113, plain, (![A_81, B_82]: (r2_hidden('#skF_1'(A_81, B_82), A_81) | r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.80/3.07  tff(c_174, plain, (![A_91, B_92]: (m1_subset_1('#skF_1'(A_91, B_92), A_91) | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_113, c_18])).
% 8.80/3.07  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.80/3.07  tff(c_421, plain, (![B_136, B_137]: (r1_tarski('#skF_1'(k1_zfmisc_1(B_136), B_137), B_136) | r1_tarski(k1_zfmisc_1(B_136), B_137))), inference(resolution, [status(thm)], [c_174, c_20])).
% 8.80/3.07  tff(c_446, plain, (![B_138]: ('#skF_1'(k1_zfmisc_1(k1_xboole_0), B_138)=k1_xboole_0 | r1_tarski(k1_zfmisc_1(k1_xboole_0), B_138))), inference(resolution, [status(thm)], [c_421, c_10])).
% 8.80/3.07  tff(c_470, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0 | '#skF_1'(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_446, c_10])).
% 8.80/3.07  tff(c_471, plain, ('#skF_1'(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_470])).
% 8.80/3.07  tff(c_501, plain, (r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_471, c_6])).
% 8.80/3.07  tff(c_2763, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_501])).
% 8.80/3.07  tff(c_2798, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2763, c_10])).
% 8.80/3.07  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.80/3.07  tff(c_2895, plain, (![A_325]: (m1_subset_1(A_325, k1_xboole_0) | ~r1_tarski(A_325, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2798, c_22])).
% 8.80/3.07  tff(c_2916, plain, (m1_subset_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_2895])).
% 8.80/3.07  tff(c_14, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.80/3.07  tff(c_2881, plain, (![A_8, C_324]: (k2_relset_1(A_8, k1_xboole_0, C_324)=k2_relat_1(C_324) | ~m1_subset_1(C_324, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2867])).
% 8.80/3.07  tff(c_3039, plain, (![A_335, C_336]: (k2_relset_1(A_335, k1_xboole_0, C_336)=k2_relat_1(C_336) | ~m1_subset_1(C_336, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2798, c_2881])).
% 8.80/3.07  tff(c_3099, plain, (![A_340]: (k2_relset_1(A_340, k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2916, c_3039])).
% 8.80/3.07  tff(c_50, plain, (![A_46, B_47, C_48]: (m1_subset_1(k2_relset_1(A_46, B_47, C_48), k1_zfmisc_1(B_47)) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.80/3.07  tff(c_3104, plain, (![A_340]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_340, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_3099, c_50])).
% 8.80/3.07  tff(c_3109, plain, (m1_subset_1(k2_relat_1(k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2916, c_2798, c_14, c_2798, c_3104])).
% 8.80/3.07  tff(c_2936, plain, (![A_327]: (r1_tarski(A_327, k1_xboole_0) | ~m1_subset_1(A_327, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2798, c_20])).
% 8.80/3.07  tff(c_2959, plain, (![A_327]: (k1_xboole_0=A_327 | ~m1_subset_1(A_327, k1_xboole_0))), inference(resolution, [status(thm)], [c_2936, c_10])).
% 8.80/3.07  tff(c_3124, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_3109, c_2959])).
% 8.80/3.07  tff(c_4707, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_4670, c_4670, c_3124])).
% 8.80/3.07  tff(c_4860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4716, c_4707])).
% 8.80/3.07  tff(c_4862, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_4541])).
% 8.80/3.07  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.80/3.07  tff(c_504, plain, (~r2_hidden(k1_xboole_0, k1_xboole_0) | r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_471, c_4])).
% 8.80/3.07  tff(c_510, plain, (~r2_hidden(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_504])).
% 8.80/3.07  tff(c_4861, plain, (r2_hidden('#skF_6'('#skF_10'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_4541])).
% 8.80/3.07  tff(c_4915, plain, (m1_subset_1('#skF_6'('#skF_10'), k1_xboole_0)), inference(resolution, [status(thm)], [c_4861, c_18])).
% 8.80/3.07  tff(c_4956, plain, ('#skF_6'('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_4915, c_2959])).
% 8.80/3.07  tff(c_4992, plain, (r2_hidden(k1_xboole_0, k1_relat_1('#skF_10')) | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_4956, c_485])).
% 8.80/3.07  tff(c_5008, plain, (r2_hidden(k1_xboole_0, k1_xboole_0) | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_4421, c_4992])).
% 8.80/3.07  tff(c_5010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4862, c_510, c_5008])).
% 8.80/3.07  tff(c_5011, plain, (r2_hidden(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_501])).
% 8.80/3.07  tff(c_5024, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_5011, c_18])).
% 8.80/3.07  tff(c_16, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.80/3.07  tff(c_5192, plain, (![B_476, C_477]: (k2_relset_1(k1_xboole_0, B_476, C_477)=k2_relat_1(C_477) | ~m1_subset_1(C_477, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_5159])).
% 8.80/3.07  tff(c_5201, plain, (![B_476]: (k2_relset_1(k1_xboole_0, B_476, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_5024, c_5192])).
% 8.80/3.07  tff(c_5484, plain, (![A_510, B_511, C_512]: (m1_subset_1(k2_relset_1(A_510, B_511, C_512), k1_zfmisc_1(B_511)) | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(A_510, B_511))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.80/3.07  tff(c_5530, plain, (![B_476]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_476)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_476))))), inference(superposition, [status(thm), theory('equality')], [c_5201, c_5484])).
% 8.80/3.07  tff(c_5571, plain, (![B_513]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_513)))), inference(demodulation, [status(thm), theory('equality')], [c_5024, c_16, c_5530])).
% 8.80/3.07  tff(c_5637, plain, (![B_519]: (r1_tarski(k2_relat_1(k1_xboole_0), B_519))), inference(resolution, [status(thm)], [c_5571, c_20])).
% 8.80/3.07  tff(c_5679, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_5637, c_10])).
% 8.80/3.07  tff(c_6860, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_6840, c_6840, c_5679])).
% 8.80/3.07  tff(c_7015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6873, c_6860])).
% 8.80/3.07  tff(c_7017, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_6756])).
% 8.80/3.07  tff(c_6739, plain, (r2_hidden('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_6669, c_485])).
% 8.80/3.07  tff(c_6758, plain, (r2_hidden('#skF_6'('#skF_10'), k1_xboole_0) | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_6739])).
% 8.80/3.07  tff(c_7036, plain, (r2_hidden('#skF_6'('#skF_10'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_7017, c_6758])).
% 8.80/3.07  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.80/3.07  tff(c_7041, plain, (![B_2]: (r2_hidden('#skF_6'('#skF_10'), B_2) | ~r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_7036, c_2])).
% 8.80/3.07  tff(c_7052, plain, (![B_596]: (r2_hidden('#skF_6'('#skF_10'), B_596))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_7041])).
% 8.80/3.07  tff(c_7065, plain, (![B_596]: (m1_subset_1('#skF_6'('#skF_10'), B_596))), inference(resolution, [status(thm)], [c_7052, c_18])).
% 8.80/3.07  tff(c_56, plain, (![D_66]: (~r2_hidden(D_66, k1_relset_1('#skF_9', '#skF_8', '#skF_10')) | ~m1_subset_1(D_66, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.80/3.07  tff(c_5067, plain, (![D_66]: (~r2_hidden(D_66, k1_relat_1('#skF_10')) | ~m1_subset_1(D_66, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_5064, c_56])).
% 8.80/3.07  tff(c_5141, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9') | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_5137, c_5067])).
% 8.80/3.07  tff(c_5152, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9') | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_5141])).
% 8.80/3.07  tff(c_5158, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_5152])).
% 8.80/3.07  tff(c_7069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7065, c_5158])).
% 8.80/3.07  tff(c_7070, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_5152])).
% 8.80/3.07  tff(c_7094, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_7070, c_58])).
% 8.80/3.07  tff(c_7283, plain, (k2_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_7118, c_7094])).
% 8.80/3.07  tff(c_7076, plain, (r2_hidden('#skF_10', k1_zfmisc_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_7070, c_7070, c_5011])).
% 8.80/3.07  tff(c_7282, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_10'))), inference(resolution, [status(thm)], [c_7076, c_18])).
% 8.80/3.07  tff(c_7097, plain, (![B_9]: (k2_zfmisc_1('#skF_10', B_9)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_7070, c_7070, c_16])).
% 8.80/3.07  tff(c_7232, plain, (![B_607]: (k2_zfmisc_1('#skF_10', B_607)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_7070, c_7070, c_16])).
% 8.80/3.07  tff(c_54, plain, (![A_52, B_53, C_54]: (k2_relset_1(A_52, B_53, C_54)=k2_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.80/3.07  tff(c_7846, plain, (![B_669, C_670]: (k2_relset_1('#skF_10', B_669, C_670)=k2_relat_1(C_670) | ~m1_subset_1(C_670, k1_zfmisc_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_7232, c_54])).
% 8.80/3.07  tff(c_7888, plain, (![B_674]: (k2_relset_1('#skF_10', B_674, '#skF_10')=k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_7282, c_7846])).
% 8.80/3.07  tff(c_7897, plain, (![B_674]: (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(B_674)) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_10', B_674))))), inference(superposition, [status(thm), theory('equality')], [c_7888, c_50])).
% 8.80/3.07  tff(c_7908, plain, (![B_676]: (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1(B_676)))), inference(demodulation, [status(thm), theory('equality')], [c_7282, c_7097, c_7897])).
% 8.80/3.07  tff(c_7982, plain, (![B_680]: (r1_tarski(k2_relat_1('#skF_10'), B_680))), inference(resolution, [status(thm)], [c_7908, c_20])).
% 8.80/3.07  tff(c_7093, plain, (![A_7]: (A_7='#skF_10' | ~r1_tarski(A_7, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_7070, c_7070, c_10])).
% 8.80/3.07  tff(c_8000, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_7982, c_7093])).
% 8.80/3.07  tff(c_8019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7283, c_8000])).
% 8.80/3.07  tff(c_8021, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_504])).
% 8.80/3.07  tff(c_8023, plain, (![B_2]: (r2_hidden(k1_xboole_0, B_2) | ~r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_8021, c_2])).
% 8.80/3.07  tff(c_8032, plain, (![B_681]: (r2_hidden(k1_xboole_0, B_681))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8023])).
% 8.80/3.07  tff(c_8045, plain, (![B_681]: (m1_subset_1(k1_xboole_0, B_681))), inference(resolution, [status(thm)], [c_8032, c_18])).
% 8.80/3.07  tff(c_8044, plain, (~m1_subset_1(k1_xboole_0, '#skF_9')), inference(resolution, [status(thm)], [c_8032, c_56])).
% 8.80/3.07  tff(c_8070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8045, c_8044])).
% 8.80/3.07  tff(c_8071, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_470])).
% 8.80/3.07  tff(c_8186, plain, (![A_696]: (m1_subset_1(A_696, k1_xboole_0) | ~r1_tarski(A_696, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8071, c_22])).
% 8.80/3.07  tff(c_8211, plain, (m1_subset_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_8186])).
% 8.80/3.07  tff(c_8282, plain, (![A_8, C_702]: (k2_relset_1(A_8, k1_xboole_0, C_702)=k2_relat_1(C_702) | ~m1_subset_1(C_702, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_8268])).
% 8.80/3.07  tff(c_9596, plain, (![A_811, C_812]: (k2_relset_1(A_811, k1_xboole_0, C_812)=k2_relat_1(C_812) | ~m1_subset_1(C_812, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8071, c_8282])).
% 8.80/3.07  tff(c_9626, plain, (![A_815]: (k2_relset_1(A_815, k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8211, c_9596])).
% 8.80/3.07  tff(c_9631, plain, (![A_815]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_815, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_9626, c_50])).
% 8.80/3.07  tff(c_9636, plain, (m1_subset_1(k2_relat_1(k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8211, c_8071, c_14, c_8071, c_9631])).
% 8.80/3.07  tff(c_8130, plain, (![A_691]: (r1_tarski(A_691, k1_xboole_0) | ~m1_subset_1(A_691, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8071, c_20])).
% 8.80/3.07  tff(c_8149, plain, (![A_691]: (k1_xboole_0=A_691 | ~m1_subset_1(A_691, k1_xboole_0))), inference(resolution, [status(thm)], [c_8130, c_10])).
% 8.80/3.07  tff(c_9651, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_9636, c_8149])).
% 8.80/3.07  tff(c_11326, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_11293, c_11293, c_9651])).
% 8.80/3.07  tff(c_11498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11329, c_11326])).
% 8.80/3.07  tff(c_11500, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_11083])).
% 8.80/3.07  tff(c_11499, plain, (m1_subset_1('#skF_6'('#skF_10'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_11083])).
% 8.80/3.07  tff(c_11526, plain, ('#skF_6'('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_11499, c_8149])).
% 8.80/3.07  tff(c_8111, plain, (![A_685]: (r2_hidden('#skF_6'(A_685), k1_relat_1(A_685)) | k1_xboole_0=A_685 | ~v1_relat_1(A_685))), inference(resolution, [status(thm)], [c_8098, c_32])).
% 8.80/3.07  tff(c_11556, plain, (r2_hidden(k1_xboole_0, k1_relat_1('#skF_10')) | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_11526, c_8111])).
% 8.80/3.07  tff(c_11572, plain, (r2_hidden(k1_xboole_0, k1_xboole_0) | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_10986, c_11556])).
% 8.80/3.07  tff(c_11573, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_11500, c_11572])).
% 8.80/3.07  tff(c_11582, plain, (![B_2]: (r2_hidden(k1_xboole_0, B_2) | ~r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_11573, c_2])).
% 8.80/3.07  tff(c_11593, plain, (![B_944]: (r2_hidden(k1_xboole_0, B_944))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_11582])).
% 8.80/3.07  tff(c_11606, plain, (![B_944]: (m1_subset_1(k1_xboole_0, B_944))), inference(resolution, [status(thm)], [c_11593, c_18])).
% 8.80/3.07  tff(c_8181, plain, (![D_66]: (~r2_hidden(D_66, k1_relat_1('#skF_10')) | ~m1_subset_1(D_66, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_8170, c_56])).
% 8.80/3.07  tff(c_8251, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9') | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_8247, c_8181])).
% 8.80/3.07  tff(c_8262, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9') | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_8251])).
% 8.80/3.07  tff(c_8296, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_8262])).
% 8.80/3.07  tff(c_11541, plain, (~m1_subset_1(k1_xboole_0, '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_11526, c_8296])).
% 8.80/3.07  tff(c_11646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11606, c_11541])).
% 8.80/3.07  tff(c_11647, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_8262])).
% 8.80/3.07  tff(c_11649, plain, (k2_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_11647, c_8291])).
% 8.80/3.07  tff(c_11652, plain, (m1_subset_1('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_11647, c_11647, c_8211])).
% 8.80/3.07  tff(c_11673, plain, (![B_9]: (k2_zfmisc_1('#skF_10', B_9)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_11647, c_11647, c_16])).
% 8.80/3.07  tff(c_121, plain, (![A_81]: (r1_tarski(A_81, A_81))), inference(resolution, [status(thm)], [c_113, c_4])).
% 8.80/3.07  tff(c_12177, plain, (![A_993, B_994, A_995]: (k2_relset_1(A_993, B_994, A_995)=k2_relat_1(A_995) | ~r1_tarski(A_995, k2_zfmisc_1(A_993, B_994)))), inference(resolution, [status(thm)], [c_22, c_8268])).
% 8.80/3.07  tff(c_12203, plain, (![A_993, B_994]: (k2_relset_1(A_993, B_994, k2_zfmisc_1(A_993, B_994))=k2_relat_1(k2_zfmisc_1(A_993, B_994)))), inference(resolution, [status(thm)], [c_121, c_12177])).
% 8.80/3.07  tff(c_11661, plain, (k1_zfmisc_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_11647, c_11647, c_8071])).
% 8.80/3.07  tff(c_11711, plain, (![A_950, B_951, C_952]: (m1_subset_1(k2_relset_1(A_950, B_951, C_952), k1_zfmisc_1(B_951)) | ~m1_subset_1(C_952, k1_zfmisc_1(k2_zfmisc_1(A_950, B_951))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.80/3.07  tff(c_12628, plain, (![A_1039, B_1040, C_1041]: (r1_tarski(k2_relset_1(A_1039, B_1040, C_1041), B_1040) | ~m1_subset_1(C_1041, k1_zfmisc_1(k2_zfmisc_1(A_1039, B_1040))))), inference(resolution, [status(thm)], [c_11711, c_20])).
% 8.80/3.07  tff(c_12633, plain, (![B_9, C_1041]: (r1_tarski(k2_relset_1('#skF_10', B_9, C_1041), B_9) | ~m1_subset_1(C_1041, k1_zfmisc_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_11673, c_12628])).
% 8.80/3.07  tff(c_12655, plain, (![B_1042, C_1043]: (r1_tarski(k2_relset_1('#skF_10', B_1042, C_1043), B_1042) | ~m1_subset_1(C_1043, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_11661, c_12633])).
% 8.80/3.07  tff(c_12702, plain, (![B_994]: (r1_tarski(k2_relat_1(k2_zfmisc_1('#skF_10', B_994)), B_994) | ~m1_subset_1(k2_zfmisc_1('#skF_10', B_994), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_12203, c_12655])).
% 8.80/3.07  tff(c_12724, plain, (![B_1044]: (r1_tarski(k2_relat_1('#skF_10'), B_1044))), inference(demodulation, [status(thm), theory('equality')], [c_11652, c_11673, c_11673, c_12702])).
% 8.80/3.07  tff(c_11670, plain, (![A_7]: (A_7='#skF_10' | ~r1_tarski(A_7, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_11647, c_11647, c_10])).
% 8.80/3.07  tff(c_12756, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_12724, c_11670])).
% 8.80/3.07  tff(c_12779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11649, c_12756])).
% 8.80/3.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.80/3.07  
% 8.80/3.07  Inference rules
% 8.80/3.07  ----------------------
% 8.80/3.07  #Ref     : 0
% 8.80/3.07  #Sup     : 2582
% 8.80/3.07  #Fact    : 0
% 8.80/3.07  #Define  : 0
% 8.80/3.07  #Split   : 48
% 8.80/3.07  #Chain   : 0
% 8.80/3.07  #Close   : 0
% 8.80/3.07  
% 8.80/3.07  Ordering : KBO
% 8.80/3.07  
% 8.80/3.07  Simplification rules
% 8.80/3.07  ----------------------
% 8.80/3.07  #Subsume      : 423
% 8.80/3.07  #Demod        : 2753
% 8.80/3.07  #Tautology    : 1178
% 8.80/3.07  #SimpNegUnit  : 177
% 8.80/3.07  #BackRed      : 399
% 8.80/3.07  
% 8.80/3.07  #Partial instantiations: 0
% 8.80/3.07  #Strategies tried      : 1
% 8.80/3.07  
% 8.80/3.07  Timing (in seconds)
% 8.80/3.07  ----------------------
% 8.80/3.07  Preprocessing        : 0.34
% 8.80/3.07  Parsing              : 0.18
% 8.80/3.07  CNF conversion       : 0.03
% 8.80/3.07  Main loop            : 1.92
% 8.80/3.07  Inferencing          : 0.66
% 8.80/3.07  Reduction            : 0.65
% 8.80/3.07  Demodulation         : 0.45
% 8.80/3.07  BG Simplification    : 0.07
% 8.80/3.07  Subsumption          : 0.36
% 8.80/3.07  Abstraction          : 0.09
% 8.80/3.07  MUC search           : 0.00
% 8.80/3.07  Cooper               : 0.00
% 8.80/3.07  Total                : 2.33
% 8.80/3.07  Index Insertion      : 0.00
% 8.80/3.07  Index Deletion       : 0.00
% 8.80/3.08  Index Matching       : 0.00
% 8.80/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
