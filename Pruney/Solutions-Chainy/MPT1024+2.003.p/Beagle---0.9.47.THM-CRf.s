%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:21 EST 2020

% Result     : Theorem 10.22s
% Output     : CNFRefutation 10.47s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 394 expanded)
%              Number of leaves         :   41 ( 151 expanded)
%              Depth                    :   14
%              Number of atoms          :  242 (1014 expanded)
%              Number of equality atoms :   24 ( 108 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_102,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_116,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_102])).

tff(c_184,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_198,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_184])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8614,plain,(
    ! [A_4881,B_4882,C_4883] :
      ( r2_hidden('#skF_4'(A_4881,B_4882,C_4883),k1_relat_1(C_4883))
      | ~ r2_hidden(A_4881,k9_relat_1(C_4883,B_4882))
      | ~ v1_relat_1(C_4883) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8626,plain,(
    ! [C_4884,A_4885,B_4886] :
      ( ~ v1_xboole_0(k1_relat_1(C_4884))
      | ~ r2_hidden(A_4885,k9_relat_1(C_4884,B_4886))
      | ~ v1_relat_1(C_4884) ) ),
    inference(resolution,[status(thm)],[c_8614,c_2])).

tff(c_8651,plain,(
    ! [C_4884,B_4886] :
      ( ~ v1_xboole_0(k1_relat_1(C_4884))
      | ~ v1_relat_1(C_4884)
      | v1_xboole_0(k9_relat_1(C_4884,B_4886)) ) ),
    inference(resolution,[status(thm)],[c_4,c_8626])).

tff(c_8760,plain,(
    ! [A_4895,B_4896,C_4897,D_4898] :
      ( k7_relset_1(A_4895,B_4896,C_4897,D_4898) = k9_relat_1(C_4897,D_4898)
      | ~ m1_subset_1(C_4897,k1_zfmisc_1(k2_zfmisc_1(A_4895,B_4896))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8783,plain,(
    ! [D_4898] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_4898) = k9_relat_1('#skF_8',D_4898) ),
    inference(resolution,[status(thm)],[c_56,c_8760])).

tff(c_54,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_90,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_8786,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8783,c_90])).

tff(c_8799,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8651,c_8786])).

tff(c_8805,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_8799])).

tff(c_8787,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8783,c_54])).

tff(c_36,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden('#skF_4'(A_22,B_23,C_24),k1_relat_1(C_24))
      | ~ r2_hidden(A_22,k9_relat_1(C_24,B_23))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8943,plain,(
    ! [A_4905,B_4906,C_4907] :
      ( r2_hidden(k4_tarski('#skF_4'(A_4905,B_4906,C_4907),A_4905),C_4907)
      | ~ r2_hidden(A_4905,k9_relat_1(C_4907,B_4906))
      | ~ v1_relat_1(C_4907) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    ! [C_30,A_28,B_29] :
      ( k1_funct_1(C_30,A_28) = B_29
      | ~ r2_hidden(k4_tarski(A_28,B_29),C_30)
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10114,plain,(
    ! [C_5015,A_5016,B_5017] :
      ( k1_funct_1(C_5015,'#skF_4'(A_5016,B_5017,C_5015)) = A_5016
      | ~ v1_funct_1(C_5015)
      | ~ r2_hidden(A_5016,k9_relat_1(C_5015,B_5017))
      | ~ v1_relat_1(C_5015) ) ),
    inference(resolution,[status(thm)],[c_8943,c_40])).

tff(c_10124,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8787,c_10114])).

tff(c_10148,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_9','#skF_7','#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_60,c_10124])).

tff(c_8809,plain,(
    ! [A_4900,C_4901] :
      ( r2_hidden(k4_tarski(A_4900,k1_funct_1(C_4901,A_4900)),C_4901)
      | ~ r2_hidden(A_4900,k1_relat_1(C_4901))
      | ~ v1_funct_1(C_4901)
      | ~ v1_relat_1(C_4901) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8871,plain,(
    ! [A_4900,C_4901] :
      ( m1_subset_1(k4_tarski(A_4900,k1_funct_1(C_4901,A_4900)),C_4901)
      | ~ r2_hidden(A_4900,k1_relat_1(C_4901))
      | ~ v1_funct_1(C_4901)
      | ~ v1_relat_1(C_4901) ) ),
    inference(resolution,[status(thm)],[c_8809,c_20])).

tff(c_10158,plain,
    ( m1_subset_1(k4_tarski('#skF_4'('#skF_9','#skF_7','#skF_8'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_10148,c_8871])).

tff(c_10165,plain,
    ( m1_subset_1(k4_tarski('#skF_4'('#skF_9','#skF_7','#skF_8'),'#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_60,c_10158])).

tff(c_10169,plain,(
    ~ r2_hidden('#skF_4'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_10165])).

tff(c_10172,plain,
    ( ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_10169])).

tff(c_10179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_8787,c_10172])).

tff(c_10181,plain,(
    r2_hidden('#skF_4'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_10165])).

tff(c_10201,plain,(
    m1_subset_1('#skF_4'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_10181,c_20])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(B_21),A_20)
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_73,plain,(
    ! [C_52,A_53] :
      ( r2_hidden(C_52,k1_zfmisc_1(A_53))
      | ~ r1_tarski(C_52,A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [C_52,A_53] :
      ( m1_subset_1(C_52,k1_zfmisc_1(A_53))
      | ~ r1_tarski(C_52,A_53) ) ),
    inference(resolution,[status(thm)],[c_73,c_20])).

tff(c_243,plain,(
    ! [A_91,C_92,B_93] :
      ( m1_subset_1(A_91,C_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(C_92))
      | ~ r2_hidden(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_255,plain,(
    ! [A_95,A_96,C_97] :
      ( m1_subset_1(A_95,A_96)
      | ~ r2_hidden(A_95,C_97)
      | ~ r1_tarski(C_97,A_96) ) ),
    inference(resolution,[status(thm)],[c_80,c_243])).

tff(c_7370,plain,(
    ! [A_4741,A_4742,B_4743] :
      ( m1_subset_1(A_4741,A_4742)
      | ~ r1_tarski(B_4743,A_4742)
      | v1_xboole_0(B_4743)
      | ~ m1_subset_1(A_4741,B_4743) ) ),
    inference(resolution,[status(thm)],[c_22,c_255])).

tff(c_7384,plain,(
    ! [A_4741,A_20,B_21] :
      ( m1_subset_1(A_4741,A_20)
      | v1_xboole_0(k1_relat_1(B_21))
      | ~ m1_subset_1(A_4741,k1_relat_1(B_21))
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_28,c_7370])).

tff(c_10204,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_4'('#skF_9','#skF_7','#skF_8'),A_20)
      | v1_xboole_0(k1_relat_1('#skF_8'))
      | ~ v4_relat_1('#skF_8',A_20)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10201,c_7384])).

tff(c_10207,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_4'('#skF_9','#skF_7','#skF_8'),A_20)
      | v1_xboole_0(k1_relat_1('#skF_8'))
      | ~ v4_relat_1('#skF_8',A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_10204])).

tff(c_10222,plain,(
    ! [A_5018] :
      ( m1_subset_1('#skF_4'('#skF_9','#skF_7','#skF_8'),A_5018)
      | ~ v4_relat_1('#skF_8',A_5018) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8805,c_10207])).

tff(c_8286,plain,(
    ! [A_4839,B_4840,C_4841] :
      ( r2_hidden('#skF_4'(A_4839,B_4840,C_4841),B_4840)
      | ~ r2_hidden(A_4839,k9_relat_1(C_4841,B_4840))
      | ~ v1_relat_1(C_4841) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8316,plain,(
    ! [A_4839,B_4840,C_4841] :
      ( m1_subset_1('#skF_4'(A_4839,B_4840,C_4841),B_4840)
      | ~ r2_hidden(A_4839,k9_relat_1(C_4841,B_4840))
      | ~ v1_relat_1(C_4841) ) ),
    inference(resolution,[status(thm)],[c_8286,c_20])).

tff(c_8877,plain,
    ( m1_subset_1('#skF_4'('#skF_9','#skF_7','#skF_8'),'#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8787,c_8316])).

tff(c_8894,plain,(
    m1_subset_1('#skF_4'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_8877])).

tff(c_218,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(k1_relat_1(B_88),A_89)
      | ~ v4_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_132,plain,(
    ! [B_68,A_69] :
      ( v1_xboole_0(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_143,plain,(
    ! [C_52,A_53] :
      ( v1_xboole_0(C_52)
      | ~ v1_xboole_0(A_53)
      | ~ r1_tarski(C_52,A_53) ) ),
    inference(resolution,[status(thm)],[c_80,c_132])).

tff(c_7293,plain,(
    ! [B_4723,A_4724] :
      ( v1_xboole_0(k1_relat_1(B_4723))
      | ~ v1_xboole_0(A_4724)
      | ~ v4_relat_1(B_4723,A_4724)
      | ~ v1_relat_1(B_4723) ) ),
    inference(resolution,[status(thm)],[c_218,c_143])).

tff(c_7295,plain,
    ( v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_xboole_0('#skF_5')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_198,c_7293])).

tff(c_7298,plain,
    ( v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_7295])).

tff(c_7299,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7298])).

tff(c_146,plain,(
    ! [F_70] :
      ( k1_funct_1('#skF_8',F_70) != '#skF_9'
      | ~ r2_hidden(F_70,'#skF_7')
      | ~ r2_hidden(F_70,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_155,plain,(
    ! [A_15] :
      ( k1_funct_1('#skF_8',A_15) != '#skF_9'
      | ~ r2_hidden(A_15,'#skF_5')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_15,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_22,c_146])).

tff(c_7331,plain,(
    ! [A_4737] :
      ( k1_funct_1('#skF_8',A_4737) != '#skF_9'
      | ~ r2_hidden(A_4737,'#skF_5')
      | ~ m1_subset_1(A_4737,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_7339,plain,(
    ! [A_15] :
      ( k1_funct_1('#skF_8',A_15) != '#skF_9'
      | ~ m1_subset_1(A_15,'#skF_7')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_15,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_7331])).

tff(c_7347,plain,(
    ! [A_15] :
      ( k1_funct_1('#skF_8',A_15) != '#skF_9'
      | ~ m1_subset_1(A_15,'#skF_7')
      | ~ m1_subset_1(A_15,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_7299,c_7339])).

tff(c_8906,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_9','#skF_7','#skF_8')) != '#skF_9'
    | ~ m1_subset_1('#skF_4'('#skF_9','#skF_7','#skF_8'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_8894,c_7347])).

tff(c_9175,plain,(
    ~ m1_subset_1('#skF_4'('#skF_9','#skF_7','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8906])).

tff(c_10232,plain,(
    ~ v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_10222,c_9175])).

tff(c_10268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_10232])).

tff(c_10269,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_9','#skF_7','#skF_8')) != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_8906])).

tff(c_11238,plain,(
    ! [C_5115,A_5116,B_5117] :
      ( k1_funct_1(C_5115,'#skF_4'(A_5116,B_5117,C_5115)) = A_5116
      | ~ v1_funct_1(C_5115)
      | ~ r2_hidden(A_5116,k9_relat_1(C_5115,B_5117))
      | ~ v1_relat_1(C_5115) ) ),
    inference(resolution,[status(thm)],[c_8943,c_40])).

tff(c_11248,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8787,c_11238])).

tff(c_11272,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_9','#skF_7','#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_60,c_11248])).

tff(c_11274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10269,c_11272])).

tff(c_11275,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_11438,plain,(
    ! [A_5145,B_5146,C_5147] :
      ( r2_hidden('#skF_4'(A_5145,B_5146,C_5147),B_5146)
      | ~ r2_hidden(A_5145,k9_relat_1(C_5147,B_5146))
      | ~ v1_relat_1(C_5147) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_11465,plain,(
    ! [B_5148,A_5149,C_5150] :
      ( ~ v1_xboole_0(B_5148)
      | ~ r2_hidden(A_5149,k9_relat_1(C_5150,B_5148))
      | ~ v1_relat_1(C_5150) ) ),
    inference(resolution,[status(thm)],[c_11438,c_2])).

tff(c_11490,plain,(
    ! [B_5148,C_5150] :
      ( ~ v1_xboole_0(B_5148)
      | ~ v1_relat_1(C_5150)
      | v1_xboole_0(k9_relat_1(C_5150,B_5148)) ) ),
    inference(resolution,[status(thm)],[c_4,c_11465])).

tff(c_11681,plain,(
    ! [A_5183,B_5184,C_5185,D_5186] :
      ( k7_relset_1(A_5183,B_5184,C_5185,D_5186) = k9_relat_1(C_5185,D_5186)
      | ~ m1_subset_1(C_5185,k1_zfmisc_1(k2_zfmisc_1(A_5183,B_5184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_11700,plain,(
    ! [D_5186] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_5186) = k9_relat_1('#skF_8',D_5186) ),
    inference(resolution,[status(thm)],[c_56,c_11681])).

tff(c_11703,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11700,c_90])).

tff(c_11719,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_11490,c_11703])).

tff(c_11726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_11275,c_11719])).

tff(c_11727,plain,(
    v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_7298])).

tff(c_12150,plain,(
    ! [A_5255,B_5256,C_5257] :
      ( r2_hidden('#skF_4'(A_5255,B_5256,C_5257),k1_relat_1(C_5257))
      | ~ r2_hidden(A_5255,k9_relat_1(C_5257,B_5256))
      | ~ v1_relat_1(C_5257) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12162,plain,(
    ! [C_5258,A_5259,B_5260] :
      ( ~ v1_xboole_0(k1_relat_1(C_5258))
      | ~ r2_hidden(A_5259,k9_relat_1(C_5258,B_5260))
      | ~ v1_relat_1(C_5258) ) ),
    inference(resolution,[status(thm)],[c_12150,c_2])).

tff(c_12187,plain,(
    ! [C_5258,B_5260] :
      ( ~ v1_xboole_0(k1_relat_1(C_5258))
      | ~ v1_relat_1(C_5258)
      | v1_xboole_0(k9_relat_1(C_5258,B_5260)) ) ),
    inference(resolution,[status(thm)],[c_4,c_12162])).

tff(c_12327,plain,(
    ! [A_5273,B_5274,C_5275,D_5276] :
      ( k7_relset_1(A_5273,B_5274,C_5275,D_5276) = k9_relat_1(C_5275,D_5276)
      | ~ m1_subset_1(C_5275,k1_zfmisc_1(k2_zfmisc_1(A_5273,B_5274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12350,plain,(
    ! [D_5276] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_5276) = k9_relat_1('#skF_8',D_5276) ),
    inference(resolution,[status(thm)],[c_56,c_12327])).

tff(c_12353,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12350,c_90])).

tff(c_12430,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12187,c_12353])).

tff(c_12437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_11727,c_12430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:01:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.22/3.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.22/3.27  
% 10.22/3.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.22/3.27  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2
% 10.22/3.27  
% 10.22/3.27  %Foreground sorts:
% 10.22/3.27  
% 10.22/3.27  
% 10.22/3.27  %Background operators:
% 10.22/3.27  
% 10.22/3.27  
% 10.22/3.27  %Foreground operators:
% 10.22/3.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.22/3.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.22/3.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.22/3.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.22/3.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.22/3.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.22/3.27  tff('#skF_7', type, '#skF_7': $i).
% 10.22/3.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.22/3.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.22/3.27  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 10.22/3.27  tff('#skF_5', type, '#skF_5': $i).
% 10.22/3.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.22/3.27  tff('#skF_6', type, '#skF_6': $i).
% 10.22/3.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.22/3.27  tff('#skF_9', type, '#skF_9': $i).
% 10.22/3.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.22/3.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.22/3.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.22/3.27  tff('#skF_8', type, '#skF_8': $i).
% 10.22/3.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.22/3.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.22/3.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.22/3.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.22/3.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.22/3.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.22/3.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.22/3.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.22/3.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.22/3.27  
% 10.47/3.29  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 10.47/3.29  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.47/3.29  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.47/3.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.47/3.29  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 10.47/3.29  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 10.47/3.29  tff(f_88, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 10.47/3.29  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 10.47/3.29  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 10.47/3.29  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 10.47/3.29  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 10.47/3.29  tff(f_61, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 10.47/3.29  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.47/3.29  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.47/3.29  tff(c_102, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.47/3.29  tff(c_116, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_102])).
% 10.47/3.29  tff(c_184, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.47/3.29  tff(c_198, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_184])).
% 10.47/3.29  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.47/3.29  tff(c_8614, plain, (![A_4881, B_4882, C_4883]: (r2_hidden('#skF_4'(A_4881, B_4882, C_4883), k1_relat_1(C_4883)) | ~r2_hidden(A_4881, k9_relat_1(C_4883, B_4882)) | ~v1_relat_1(C_4883))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.47/3.29  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.47/3.29  tff(c_8626, plain, (![C_4884, A_4885, B_4886]: (~v1_xboole_0(k1_relat_1(C_4884)) | ~r2_hidden(A_4885, k9_relat_1(C_4884, B_4886)) | ~v1_relat_1(C_4884))), inference(resolution, [status(thm)], [c_8614, c_2])).
% 10.47/3.29  tff(c_8651, plain, (![C_4884, B_4886]: (~v1_xboole_0(k1_relat_1(C_4884)) | ~v1_relat_1(C_4884) | v1_xboole_0(k9_relat_1(C_4884, B_4886)))), inference(resolution, [status(thm)], [c_4, c_8626])).
% 10.47/3.29  tff(c_8760, plain, (![A_4895, B_4896, C_4897, D_4898]: (k7_relset_1(A_4895, B_4896, C_4897, D_4898)=k9_relat_1(C_4897, D_4898) | ~m1_subset_1(C_4897, k1_zfmisc_1(k2_zfmisc_1(A_4895, B_4896))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.47/3.29  tff(c_8783, plain, (![D_4898]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_4898)=k9_relat_1('#skF_8', D_4898))), inference(resolution, [status(thm)], [c_56, c_8760])).
% 10.47/3.29  tff(c_54, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.47/3.29  tff(c_90, plain, (~v1_xboole_0(k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_2])).
% 10.47/3.29  tff(c_8786, plain, (~v1_xboole_0(k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_8783, c_90])).
% 10.47/3.29  tff(c_8799, plain, (~v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_8651, c_8786])).
% 10.47/3.29  tff(c_8805, plain, (~v1_xboole_0(k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_8799])).
% 10.47/3.29  tff(c_8787, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_8783, c_54])).
% 10.47/3.29  tff(c_36, plain, (![A_22, B_23, C_24]: (r2_hidden('#skF_4'(A_22, B_23, C_24), k1_relat_1(C_24)) | ~r2_hidden(A_22, k9_relat_1(C_24, B_23)) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.47/3.29  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.47/3.29  tff(c_8943, plain, (![A_4905, B_4906, C_4907]: (r2_hidden(k4_tarski('#skF_4'(A_4905, B_4906, C_4907), A_4905), C_4907) | ~r2_hidden(A_4905, k9_relat_1(C_4907, B_4906)) | ~v1_relat_1(C_4907))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.47/3.29  tff(c_40, plain, (![C_30, A_28, B_29]: (k1_funct_1(C_30, A_28)=B_29 | ~r2_hidden(k4_tarski(A_28, B_29), C_30) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.47/3.29  tff(c_10114, plain, (![C_5015, A_5016, B_5017]: (k1_funct_1(C_5015, '#skF_4'(A_5016, B_5017, C_5015))=A_5016 | ~v1_funct_1(C_5015) | ~r2_hidden(A_5016, k9_relat_1(C_5015, B_5017)) | ~v1_relat_1(C_5015))), inference(resolution, [status(thm)], [c_8943, c_40])).
% 10.47/3.29  tff(c_10124, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_8787, c_10114])).
% 10.47/3.29  tff(c_10148, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_9', '#skF_7', '#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_60, c_10124])).
% 10.47/3.29  tff(c_8809, plain, (![A_4900, C_4901]: (r2_hidden(k4_tarski(A_4900, k1_funct_1(C_4901, A_4900)), C_4901) | ~r2_hidden(A_4900, k1_relat_1(C_4901)) | ~v1_funct_1(C_4901) | ~v1_relat_1(C_4901))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.47/3.29  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.47/3.29  tff(c_8871, plain, (![A_4900, C_4901]: (m1_subset_1(k4_tarski(A_4900, k1_funct_1(C_4901, A_4900)), C_4901) | ~r2_hidden(A_4900, k1_relat_1(C_4901)) | ~v1_funct_1(C_4901) | ~v1_relat_1(C_4901))), inference(resolution, [status(thm)], [c_8809, c_20])).
% 10.47/3.29  tff(c_10158, plain, (m1_subset_1(k4_tarski('#skF_4'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_4'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_10148, c_8871])).
% 10.47/3.29  tff(c_10165, plain, (m1_subset_1(k4_tarski('#skF_4'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), '#skF_8') | ~r2_hidden('#skF_4'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_60, c_10158])).
% 10.47/3.29  tff(c_10169, plain, (~r2_hidden('#skF_4'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_10165])).
% 10.47/3.29  tff(c_10172, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_10169])).
% 10.47/3.29  tff(c_10179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_8787, c_10172])).
% 10.47/3.29  tff(c_10181, plain, (r2_hidden('#skF_4'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_10165])).
% 10.47/3.29  tff(c_10201, plain, (m1_subset_1('#skF_4'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_10181, c_20])).
% 10.47/3.29  tff(c_28, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(B_21), A_20) | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.47/3.29  tff(c_22, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.47/3.29  tff(c_73, plain, (![C_52, A_53]: (r2_hidden(C_52, k1_zfmisc_1(A_53)) | ~r1_tarski(C_52, A_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.47/3.29  tff(c_80, plain, (![C_52, A_53]: (m1_subset_1(C_52, k1_zfmisc_1(A_53)) | ~r1_tarski(C_52, A_53))), inference(resolution, [status(thm)], [c_73, c_20])).
% 10.47/3.29  tff(c_243, plain, (![A_91, C_92, B_93]: (m1_subset_1(A_91, C_92) | ~m1_subset_1(B_93, k1_zfmisc_1(C_92)) | ~r2_hidden(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.47/3.29  tff(c_255, plain, (![A_95, A_96, C_97]: (m1_subset_1(A_95, A_96) | ~r2_hidden(A_95, C_97) | ~r1_tarski(C_97, A_96))), inference(resolution, [status(thm)], [c_80, c_243])).
% 10.47/3.29  tff(c_7370, plain, (![A_4741, A_4742, B_4743]: (m1_subset_1(A_4741, A_4742) | ~r1_tarski(B_4743, A_4742) | v1_xboole_0(B_4743) | ~m1_subset_1(A_4741, B_4743))), inference(resolution, [status(thm)], [c_22, c_255])).
% 10.47/3.29  tff(c_7384, plain, (![A_4741, A_20, B_21]: (m1_subset_1(A_4741, A_20) | v1_xboole_0(k1_relat_1(B_21)) | ~m1_subset_1(A_4741, k1_relat_1(B_21)) | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_28, c_7370])).
% 10.47/3.29  tff(c_10204, plain, (![A_20]: (m1_subset_1('#skF_4'('#skF_9', '#skF_7', '#skF_8'), A_20) | v1_xboole_0(k1_relat_1('#skF_8')) | ~v4_relat_1('#skF_8', A_20) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_10201, c_7384])).
% 10.47/3.29  tff(c_10207, plain, (![A_20]: (m1_subset_1('#skF_4'('#skF_9', '#skF_7', '#skF_8'), A_20) | v1_xboole_0(k1_relat_1('#skF_8')) | ~v4_relat_1('#skF_8', A_20))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_10204])).
% 10.47/3.29  tff(c_10222, plain, (![A_5018]: (m1_subset_1('#skF_4'('#skF_9', '#skF_7', '#skF_8'), A_5018) | ~v4_relat_1('#skF_8', A_5018))), inference(negUnitSimplification, [status(thm)], [c_8805, c_10207])).
% 10.47/3.29  tff(c_8286, plain, (![A_4839, B_4840, C_4841]: (r2_hidden('#skF_4'(A_4839, B_4840, C_4841), B_4840) | ~r2_hidden(A_4839, k9_relat_1(C_4841, B_4840)) | ~v1_relat_1(C_4841))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.47/3.29  tff(c_8316, plain, (![A_4839, B_4840, C_4841]: (m1_subset_1('#skF_4'(A_4839, B_4840, C_4841), B_4840) | ~r2_hidden(A_4839, k9_relat_1(C_4841, B_4840)) | ~v1_relat_1(C_4841))), inference(resolution, [status(thm)], [c_8286, c_20])).
% 10.47/3.29  tff(c_8877, plain, (m1_subset_1('#skF_4'('#skF_9', '#skF_7', '#skF_8'), '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_8787, c_8316])).
% 10.47/3.29  tff(c_8894, plain, (m1_subset_1('#skF_4'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_8877])).
% 10.47/3.29  tff(c_218, plain, (![B_88, A_89]: (r1_tarski(k1_relat_1(B_88), A_89) | ~v4_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.47/3.29  tff(c_132, plain, (![B_68, A_69]: (v1_xboole_0(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.47/3.29  tff(c_143, plain, (![C_52, A_53]: (v1_xboole_0(C_52) | ~v1_xboole_0(A_53) | ~r1_tarski(C_52, A_53))), inference(resolution, [status(thm)], [c_80, c_132])).
% 10.47/3.29  tff(c_7293, plain, (![B_4723, A_4724]: (v1_xboole_0(k1_relat_1(B_4723)) | ~v1_xboole_0(A_4724) | ~v4_relat_1(B_4723, A_4724) | ~v1_relat_1(B_4723))), inference(resolution, [status(thm)], [c_218, c_143])).
% 10.47/3.29  tff(c_7295, plain, (v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_xboole_0('#skF_5') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_198, c_7293])).
% 10.47/3.29  tff(c_7298, plain, (v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_7295])).
% 10.47/3.29  tff(c_7299, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_7298])).
% 10.47/3.29  tff(c_146, plain, (![F_70]: (k1_funct_1('#skF_8', F_70)!='#skF_9' | ~r2_hidden(F_70, '#skF_7') | ~r2_hidden(F_70, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.47/3.29  tff(c_155, plain, (![A_15]: (k1_funct_1('#skF_8', A_15)!='#skF_9' | ~r2_hidden(A_15, '#skF_5') | v1_xboole_0('#skF_7') | ~m1_subset_1(A_15, '#skF_7'))), inference(resolution, [status(thm)], [c_22, c_146])).
% 10.47/3.29  tff(c_7331, plain, (![A_4737]: (k1_funct_1('#skF_8', A_4737)!='#skF_9' | ~r2_hidden(A_4737, '#skF_5') | ~m1_subset_1(A_4737, '#skF_7'))), inference(splitLeft, [status(thm)], [c_155])).
% 10.47/3.29  tff(c_7339, plain, (![A_15]: (k1_funct_1('#skF_8', A_15)!='#skF_9' | ~m1_subset_1(A_15, '#skF_7') | v1_xboole_0('#skF_5') | ~m1_subset_1(A_15, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_7331])).
% 10.47/3.29  tff(c_7347, plain, (![A_15]: (k1_funct_1('#skF_8', A_15)!='#skF_9' | ~m1_subset_1(A_15, '#skF_7') | ~m1_subset_1(A_15, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_7299, c_7339])).
% 10.47/3.29  tff(c_8906, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_9', '#skF_7', '#skF_8'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_9', '#skF_7', '#skF_8'), '#skF_5')), inference(resolution, [status(thm)], [c_8894, c_7347])).
% 10.47/3.29  tff(c_9175, plain, (~m1_subset_1('#skF_4'('#skF_9', '#skF_7', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_8906])).
% 10.47/3.29  tff(c_10232, plain, (~v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_10222, c_9175])).
% 10.47/3.29  tff(c_10268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_198, c_10232])).
% 10.47/3.29  tff(c_10269, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_9', '#skF_7', '#skF_8'))!='#skF_9'), inference(splitRight, [status(thm)], [c_8906])).
% 10.47/3.29  tff(c_11238, plain, (![C_5115, A_5116, B_5117]: (k1_funct_1(C_5115, '#skF_4'(A_5116, B_5117, C_5115))=A_5116 | ~v1_funct_1(C_5115) | ~r2_hidden(A_5116, k9_relat_1(C_5115, B_5117)) | ~v1_relat_1(C_5115))), inference(resolution, [status(thm)], [c_8943, c_40])).
% 10.47/3.29  tff(c_11248, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_8787, c_11238])).
% 10.47/3.29  tff(c_11272, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_9', '#skF_7', '#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_60, c_11248])).
% 10.47/3.29  tff(c_11274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10269, c_11272])).
% 10.47/3.29  tff(c_11275, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_155])).
% 10.47/3.29  tff(c_11438, plain, (![A_5145, B_5146, C_5147]: (r2_hidden('#skF_4'(A_5145, B_5146, C_5147), B_5146) | ~r2_hidden(A_5145, k9_relat_1(C_5147, B_5146)) | ~v1_relat_1(C_5147))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.47/3.29  tff(c_11465, plain, (![B_5148, A_5149, C_5150]: (~v1_xboole_0(B_5148) | ~r2_hidden(A_5149, k9_relat_1(C_5150, B_5148)) | ~v1_relat_1(C_5150))), inference(resolution, [status(thm)], [c_11438, c_2])).
% 10.47/3.29  tff(c_11490, plain, (![B_5148, C_5150]: (~v1_xboole_0(B_5148) | ~v1_relat_1(C_5150) | v1_xboole_0(k9_relat_1(C_5150, B_5148)))), inference(resolution, [status(thm)], [c_4, c_11465])).
% 10.47/3.29  tff(c_11681, plain, (![A_5183, B_5184, C_5185, D_5186]: (k7_relset_1(A_5183, B_5184, C_5185, D_5186)=k9_relat_1(C_5185, D_5186) | ~m1_subset_1(C_5185, k1_zfmisc_1(k2_zfmisc_1(A_5183, B_5184))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.47/3.29  tff(c_11700, plain, (![D_5186]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_5186)=k9_relat_1('#skF_8', D_5186))), inference(resolution, [status(thm)], [c_56, c_11681])).
% 10.47/3.29  tff(c_11703, plain, (~v1_xboole_0(k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_11700, c_90])).
% 10.47/3.29  tff(c_11719, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_11490, c_11703])).
% 10.47/3.29  tff(c_11726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_11275, c_11719])).
% 10.47/3.29  tff(c_11727, plain, (v1_xboole_0(k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_7298])).
% 10.47/3.29  tff(c_12150, plain, (![A_5255, B_5256, C_5257]: (r2_hidden('#skF_4'(A_5255, B_5256, C_5257), k1_relat_1(C_5257)) | ~r2_hidden(A_5255, k9_relat_1(C_5257, B_5256)) | ~v1_relat_1(C_5257))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.47/3.29  tff(c_12162, plain, (![C_5258, A_5259, B_5260]: (~v1_xboole_0(k1_relat_1(C_5258)) | ~r2_hidden(A_5259, k9_relat_1(C_5258, B_5260)) | ~v1_relat_1(C_5258))), inference(resolution, [status(thm)], [c_12150, c_2])).
% 10.47/3.29  tff(c_12187, plain, (![C_5258, B_5260]: (~v1_xboole_0(k1_relat_1(C_5258)) | ~v1_relat_1(C_5258) | v1_xboole_0(k9_relat_1(C_5258, B_5260)))), inference(resolution, [status(thm)], [c_4, c_12162])).
% 10.47/3.29  tff(c_12327, plain, (![A_5273, B_5274, C_5275, D_5276]: (k7_relset_1(A_5273, B_5274, C_5275, D_5276)=k9_relat_1(C_5275, D_5276) | ~m1_subset_1(C_5275, k1_zfmisc_1(k2_zfmisc_1(A_5273, B_5274))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.47/3.29  tff(c_12350, plain, (![D_5276]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_5276)=k9_relat_1('#skF_8', D_5276))), inference(resolution, [status(thm)], [c_56, c_12327])).
% 10.47/3.29  tff(c_12353, plain, (~v1_xboole_0(k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_12350, c_90])).
% 10.47/3.29  tff(c_12430, plain, (~v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12187, c_12353])).
% 10.47/3.29  tff(c_12437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_11727, c_12430])).
% 10.47/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.47/3.29  
% 10.47/3.29  Inference rules
% 10.47/3.29  ----------------------
% 10.47/3.29  #Ref     : 0
% 10.47/3.29  #Sup     : 2236
% 10.47/3.29  #Fact    : 1
% 10.47/3.29  #Define  : 0
% 10.47/3.29  #Split   : 26
% 10.47/3.29  #Chain   : 0
% 10.47/3.29  #Close   : 0
% 10.47/3.29  
% 10.47/3.29  Ordering : KBO
% 10.47/3.29  
% 10.47/3.29  Simplification rules
% 10.47/3.29  ----------------------
% 10.47/3.29  #Subsume      : 419
% 10.47/3.29  #Demod        : 262
% 10.47/3.29  #Tautology    : 150
% 10.47/3.29  #SimpNegUnit  : 75
% 10.47/3.29  #BackRed      : 27
% 10.47/3.29  
% 10.47/3.29  #Partial instantiations: 3104
% 10.47/3.29  #Strategies tried      : 1
% 10.47/3.29  
% 10.47/3.29  Timing (in seconds)
% 10.47/3.29  ----------------------
% 10.47/3.29  Preprocessing        : 0.35
% 10.47/3.29  Parsing              : 0.18
% 10.47/3.29  CNF conversion       : 0.03
% 10.47/3.29  Main loop            : 2.16
% 10.47/3.29  Inferencing          : 0.80
% 10.47/3.29  Reduction            : 0.54
% 10.47/3.29  Demodulation         : 0.35
% 10.47/3.29  BG Simplification    : 0.08
% 10.47/3.29  Subsumption          : 0.55
% 10.47/3.29  Abstraction          : 0.10
% 10.47/3.29  MUC search           : 0.00
% 10.47/3.29  Cooper               : 0.00
% 10.47/3.29  Total                : 2.55
% 10.47/3.29  Index Insertion      : 0.00
% 10.47/3.29  Index Deletion       : 0.00
% 10.47/3.29  Index Matching       : 0.00
% 10.47/3.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
