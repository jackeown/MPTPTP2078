%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:14 EST 2020

% Result     : Theorem 8.59s
% Output     : CNFRefutation 8.81s
% Verified   : 
% Statistics : Number of formulae       :  253 (1368 expanded)
%              Number of leaves         :   44 ( 458 expanded)
%              Depth                    :   19
%              Number of atoms          :  474 (3583 expanded)
%              Number of equality atoms :  162 (1021 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_94,axiom,(
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

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_5645,plain,(
    ! [B_778,A_779] :
      ( v1_relat_1(B_778)
      | ~ m1_subset_1(B_778,k1_zfmisc_1(A_779))
      | ~ v1_relat_1(A_779) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5651,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_5645])).

tff(c_5658,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5651])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_74,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_7814,plain,(
    ! [C_1066,A_1067,B_1068] :
      ( v2_funct_1(C_1066)
      | ~ v3_funct_2(C_1066,A_1067,B_1068)
      | ~ v1_funct_1(C_1066)
      | ~ m1_subset_1(C_1066,k1_zfmisc_1(k2_zfmisc_1(A_1067,B_1068))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_7821,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_7814])).

tff(c_7835,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_7821])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_7771,plain,(
    ! [A_1059,B_1060,C_1061] :
      ( k1_relset_1(A_1059,B_1060,C_1061) = k1_relat_1(C_1061)
      | ~ m1_subset_1(C_1061,k1_zfmisc_1(k2_zfmisc_1(A_1059,B_1060))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_7790,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_7771])).

tff(c_8426,plain,(
    ! [B_1147,A_1148,C_1149] :
      ( k1_xboole_0 = B_1147
      | k1_relset_1(A_1148,B_1147,C_1149) = A_1148
      | ~ v1_funct_2(C_1149,A_1148,B_1147)
      | ~ m1_subset_1(C_1149,k1_zfmisc_1(k2_zfmisc_1(A_1148,B_1147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8433,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_8426])).

tff(c_8447,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7790,c_8433])).

tff(c_8451,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8447])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( k10_relat_1(B_22,k9_relat_1(B_22,A_21)) = A_21
      | ~ v2_funct_1(B_22)
      | ~ r1_tarski(A_21,k1_relat_1(B_22))
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8457,plain,(
    ! [A_21] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_21)) = A_21
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_21,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8451,c_34])).

tff(c_8627,plain,(
    ! [A_1159] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_1159)) = A_1159
      | ~ r1_tarski(A_1159,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5658,c_78,c_7835,c_8457])).

tff(c_8031,plain,(
    ! [A_1098,B_1099,C_1100,D_1101] :
      ( k8_relset_1(A_1098,B_1099,C_1100,D_1101) = k10_relat_1(C_1100,D_1101)
      | ~ m1_subset_1(C_1100,k1_zfmisc_1(k2_zfmisc_1(A_1098,B_1099))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8045,plain,(
    ! [D_1101] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_1101) = k10_relat_1('#skF_3',D_1101) ),
    inference(resolution,[status(thm)],[c_72,c_8031])).

tff(c_7906,plain,(
    ! [A_1080,B_1081,C_1082,D_1083] :
      ( k7_relset_1(A_1080,B_1081,C_1082,D_1083) = k9_relat_1(C_1082,D_1083)
      | ~ m1_subset_1(C_1082,k1_zfmisc_1(k2_zfmisc_1(A_1080,B_1081))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_7920,plain,(
    ! [D_1083] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_1083) = k9_relat_1('#skF_3',D_1083) ),
    inference(resolution,[status(thm)],[c_72,c_7906])).

tff(c_70,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1435,plain,(
    ! [B_247,A_248] :
      ( v1_relat_1(B_247)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(A_248))
      | ~ v1_relat_1(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1441,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_1435])).

tff(c_1448,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1441])).

tff(c_4720,plain,(
    ! [C_684,A_685,B_686] :
      ( v2_funct_1(C_684)
      | ~ v3_funct_2(C_684,A_685,B_686)
      | ~ v1_funct_1(C_684)
      | ~ m1_subset_1(C_684,k1_zfmisc_1(k2_zfmisc_1(A_685,B_686))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4727,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_4720])).

tff(c_4741,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_4727])).

tff(c_4105,plain,(
    ! [A_600,B_601,C_602] :
      ( k1_relset_1(A_600,B_601,C_602) = k1_relat_1(C_602)
      | ~ m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(A_600,B_601))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4124,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_4105])).

tff(c_5340,plain,(
    ! [B_766,A_767,C_768] :
      ( k1_xboole_0 = B_766
      | k1_relset_1(A_767,B_766,C_768) = A_767
      | ~ v1_funct_2(C_768,A_767,B_766)
      | ~ m1_subset_1(C_768,k1_zfmisc_1(k2_zfmisc_1(A_767,B_766))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5347,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_5340])).

tff(c_5361,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4124,c_5347])).

tff(c_5365,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5361])).

tff(c_5374,plain,(
    ! [A_21] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_21)) = A_21
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_21,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5365,c_34])).

tff(c_5523,plain,(
    ! [A_776] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_776)) = A_776
      | ~ r1_tarski(A_776,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_78,c_4741,c_5374])).

tff(c_4960,plain,(
    ! [A_717,B_718,C_719,D_720] :
      ( k8_relset_1(A_717,B_718,C_719,D_720) = k10_relat_1(C_719,D_720)
      | ~ m1_subset_1(C_719,k1_zfmisc_1(k2_zfmisc_1(A_717,B_718))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4974,plain,(
    ! [D_720] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_720) = k10_relat_1('#skF_3',D_720) ),
    inference(resolution,[status(thm)],[c_72,c_4960])).

tff(c_4838,plain,(
    ! [A_700,B_701,C_702,D_703] :
      ( k7_relset_1(A_700,B_701,C_702,D_703) = k9_relat_1(C_702,D_703)
      | ~ m1_subset_1(C_702,k1_zfmisc_1(k2_zfmisc_1(A_700,B_701))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4852,plain,(
    ! [D_703] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_703) = k9_relat_1('#skF_3',D_703) ),
    inference(resolution,[status(thm)],[c_72,c_4838])).

tff(c_174,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_180,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_174])).

tff(c_187,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_180])).

tff(c_257,plain,(
    ! [C_75,B_76,A_77] :
      ( v5_relat_1(C_75,B_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_276,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_257])).

tff(c_470,plain,(
    ! [B_109,A_110] :
      ( k2_relat_1(B_109) = A_110
      | ~ v2_funct_2(B_109,A_110)
      | ~ v5_relat_1(B_109,A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_482,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_276,c_470])).

tff(c_492,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_482])).

tff(c_499,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_492])).

tff(c_954,plain,(
    ! [C_181,B_182,A_183] :
      ( v2_funct_2(C_181,B_182)
      | ~ v3_funct_2(C_181,A_183,B_182)
      | ~ v1_funct_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_961,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_954])).

tff(c_975,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_961])).

tff(c_977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_975])).

tff(c_978,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_492])).

tff(c_1190,plain,(
    ! [B_214,A_215] :
      ( k9_relat_1(B_214,k10_relat_1(B_214,A_215)) = A_215
      | ~ r1_tarski(A_215,k2_relat_1(B_214))
      | ~ v1_funct_1(B_214)
      | ~ v1_relat_1(B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1192,plain,(
    ! [A_215] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_215)) = A_215
      | ~ r1_tarski(A_215,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_978,c_1190])).

tff(c_1203,plain,(
    ! [A_215] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_215)) = A_215
      | ~ r1_tarski(A_215,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_78,c_1192])).

tff(c_1395,plain,(
    ! [A_242,B_243,C_244,D_245] :
      ( k7_relset_1(A_242,B_243,C_244,D_245) = k9_relat_1(C_244,D_245)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1409,plain,(
    ! [D_245] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_245) = k9_relat_1('#skF_3',D_245) ),
    inference(resolution,[status(thm)],[c_72,c_1395])).

tff(c_1322,plain,(
    ! [A_228,B_229,C_230,D_231] :
      ( k8_relset_1(A_228,B_229,C_230,D_231) = k10_relat_1(C_230,D_231)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1336,plain,(
    ! [D_231] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_231) = k10_relat_1('#skF_3',D_231) ),
    inference(resolution,[status(thm)],[c_72,c_1322])).

tff(c_68,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_161,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_1338,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_161])).

tff(c_1411,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_1338])).

tff(c_1423,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_1411])).

tff(c_1427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1423])).

tff(c_1428,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_4854,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4852,c_1428])).

tff(c_4977,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4974,c_4854])).

tff(c_5536,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5523,c_4977])).

tff(c_5562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5536])).

tff(c_5563,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5361])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5612,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5563,c_8])).

tff(c_132,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_132])).

tff(c_1430,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_5634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5612,c_1430])).

tff(c_5635,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_5643,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5635,c_5635,c_1428])).

tff(c_7922,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7920,c_5643])).

tff(c_8048,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8045,c_7922])).

tff(c_8636,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8627,c_8048])).

tff(c_8659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8636])).

tff(c_8660,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8447])).

tff(c_8706,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8660,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8704,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8660,c_8660,c_14])).

tff(c_117,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_124,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_117])).

tff(c_141,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_132])).

tff(c_5801,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_8777,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8704,c_5801])).

tff(c_8782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8706,c_8777])).

tff(c_8783,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_14445,plain,(
    ! [B_1789,C_1790,A_1791] :
      ( k1_xboole_0 = B_1789
      | v1_funct_2(C_1790,A_1791,B_1789)
      | k1_relset_1(A_1791,B_1789,C_1790) != A_1791
      | ~ m1_subset_1(C_1790,k1_zfmisc_1(k2_zfmisc_1(A_1791,B_1789))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14448,plain,(
    ! [C_1790] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_1790,'#skF_1','#skF_1')
      | k1_relset_1('#skF_1','#skF_1',C_1790) != '#skF_1'
      | ~ m1_subset_1(C_1790,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_14445])).

tff(c_14530,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14448])).

tff(c_8786,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8783,c_72])).

tff(c_12301,plain,(
    ! [C_1579,A_1580,B_1581] :
      ( v2_funct_1(C_1579)
      | ~ v3_funct_2(C_1579,A_1580,B_1581)
      | ~ v1_funct_1(C_1579)
      | ~ m1_subset_1(C_1579,k1_zfmisc_1(k2_zfmisc_1(A_1580,B_1581))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12329,plain,(
    ! [C_1583] :
      ( v2_funct_1(C_1583)
      | ~ v3_funct_2(C_1583,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_1583)
      | ~ m1_subset_1(C_1583,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_12301])).

tff(c_12332,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8786,c_12329])).

tff(c_12343,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_12332])).

tff(c_12600,plain,(
    ! [A_1616,B_1617,C_1618,D_1619] :
      ( k8_relset_1(A_1616,B_1617,C_1618,D_1619) = k10_relat_1(C_1618,D_1619)
      | ~ m1_subset_1(C_1618,k1_zfmisc_1(k2_zfmisc_1(A_1616,B_1617))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12649,plain,(
    ! [C_1628,D_1629] :
      ( k8_relset_1('#skF_1','#skF_1',C_1628,D_1629) = k10_relat_1(C_1628,D_1629)
      | ~ m1_subset_1(C_1628,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_12600])).

tff(c_12658,plain,(
    ! [D_1629] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_1629) = k10_relat_1('#skF_3',D_1629) ),
    inference(resolution,[status(thm)],[c_8786,c_12649])).

tff(c_12517,plain,(
    ! [A_1600,B_1601,C_1602,D_1603] :
      ( k7_relset_1(A_1600,B_1601,C_1602,D_1603) = k9_relat_1(C_1602,D_1603)
      | ~ m1_subset_1(C_1602,k1_zfmisc_1(k2_zfmisc_1(A_1600,B_1601))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12551,plain,(
    ! [C_1610,D_1611] :
      ( k7_relset_1('#skF_1','#skF_1',C_1610,D_1611) = k9_relat_1(C_1610,D_1611)
      | ~ m1_subset_1(C_1610,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_12517])).

tff(c_12560,plain,(
    ! [D_1611] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_1611) = k9_relat_1('#skF_3',D_1611) ),
    inference(resolution,[status(thm)],[c_8786,c_12551])).

tff(c_12564,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12560,c_5643])).

tff(c_12663,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12658,c_12564])).

tff(c_10140,plain,(
    ! [A_1342,B_1343,C_1344] :
      ( k1_relset_1(A_1342,B_1343,C_1344) = k1_relat_1(C_1344)
      | ~ m1_subset_1(C_1344,k1_zfmisc_1(k2_zfmisc_1(A_1342,B_1343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10192,plain,(
    ! [C_1350] :
      ( k1_relset_1('#skF_1','#skF_1',C_1350) = k1_relat_1(C_1350)
      | ~ m1_subset_1(C_1350,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_10140])).

tff(c_10204,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8786,c_10192])).

tff(c_8822,plain,(
    ! [C_1166,A_1167,B_1168] :
      ( v4_relat_1(C_1166,A_1167)
      | ~ m1_subset_1(C_1166,k1_zfmisc_1(k2_zfmisc_1(A_1167,B_1168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8919,plain,(
    ! [C_1177] :
      ( v4_relat_1(C_1177,'#skF_1')
      | ~ m1_subset_1(C_1177,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_8822])).

tff(c_8931,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_8786,c_8919])).

tff(c_13118,plain,(
    ! [B_1668,C_1669,A_1670] :
      ( k1_xboole_0 = B_1668
      | v1_funct_2(C_1669,A_1670,B_1668)
      | k1_relset_1(A_1670,B_1668,C_1669) != A_1670
      | ~ m1_subset_1(C_1669,k1_zfmisc_1(k2_zfmisc_1(A_1670,B_1668))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_13121,plain,(
    ! [C_1669] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_1669,'#skF_1','#skF_1')
      | k1_relset_1('#skF_1','#skF_1',C_1669) != '#skF_1'
      | ~ m1_subset_1(C_1669,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_13118])).

tff(c_13157,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_13121])).

tff(c_10845,plain,(
    ! [A_1430,B_1431,C_1432,D_1433] :
      ( k8_relset_1(A_1430,B_1431,C_1432,D_1433) = k10_relat_1(C_1432,D_1433)
      | ~ m1_subset_1(C_1432,k1_zfmisc_1(k2_zfmisc_1(A_1430,B_1431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10894,plain,(
    ! [C_1443,D_1444] :
      ( k8_relset_1('#skF_1','#skF_1',C_1443,D_1444) = k10_relat_1(C_1443,D_1444)
      | ~ m1_subset_1(C_1443,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_10845])).

tff(c_10903,plain,(
    ! [D_1444] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_1444) = k10_relat_1('#skF_3',D_1444) ),
    inference(resolution,[status(thm)],[c_8786,c_10894])).

tff(c_10646,plain,(
    ! [A_1402,B_1403,C_1404,D_1405] :
      ( k7_relset_1(A_1402,B_1403,C_1404,D_1405) = k9_relat_1(C_1404,D_1405)
      | ~ m1_subset_1(C_1404,k1_zfmisc_1(k2_zfmisc_1(A_1402,B_1403))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10701,plain,(
    ! [C_1412,D_1413] :
      ( k7_relset_1('#skF_1','#skF_1',C_1412,D_1413) = k9_relat_1(C_1412,D_1413)
      | ~ m1_subset_1(C_1412,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_10646])).

tff(c_10710,plain,(
    ! [D_1413] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_1413) = k9_relat_1('#skF_3',D_1413) ),
    inference(resolution,[status(thm)],[c_8786,c_10701])).

tff(c_10714,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10710,c_5643])).

tff(c_10908,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10903,c_10714])).

tff(c_10754,plain,(
    ! [C_1417,A_1418,B_1419] :
      ( v2_funct_1(C_1417)
      | ~ v3_funct_2(C_1417,A_1418,B_1419)
      | ~ v1_funct_1(C_1417)
      | ~ m1_subset_1(C_1417,k1_zfmisc_1(k2_zfmisc_1(A_1418,B_1419))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10790,plain,(
    ! [C_1422] :
      ( v2_funct_1(C_1422)
      | ~ v3_funct_2(C_1422,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_1422)
      | ~ m1_subset_1(C_1422,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_10754])).

tff(c_10793,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8786,c_10790])).

tff(c_10804,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_10793])).

tff(c_5688,plain,(
    ! [B_784,A_785] :
      ( r1_tarski(k1_relat_1(B_784),A_785)
      | ~ v4_relat_1(B_784,A_785)
      | ~ v1_relat_1(B_784) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5655,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(A_7)
      | ~ v1_relat_1(B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_20,c_5645])).

tff(c_10277,plain,(
    ! [B_1360,A_1361] :
      ( v1_relat_1(k1_relat_1(B_1360))
      | ~ v1_relat_1(A_1361)
      | ~ v4_relat_1(B_1360,A_1361)
      | ~ v1_relat_1(B_1360) ) ),
    inference(resolution,[status(thm)],[c_5688,c_5655])).

tff(c_10283,plain,
    ( v1_relat_1(k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8931,c_10277])).

tff(c_10296,plain,
    ( v1_relat_1(k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5658,c_10283])).

tff(c_10302,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_10296])).

tff(c_11427,plain,(
    ! [B_1504,A_1505,C_1506] :
      ( k1_xboole_0 = B_1504
      | k1_relset_1(A_1505,B_1504,C_1506) = A_1505
      | ~ v1_funct_2(C_1506,A_1505,B_1504)
      | ~ m1_subset_1(C_1506,k1_zfmisc_1(k2_zfmisc_1(A_1505,B_1504))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_11430,plain,(
    ! [C_1506] :
      ( k1_xboole_0 = '#skF_1'
      | k1_relset_1('#skF_1','#skF_1',C_1506) = '#skF_1'
      | ~ v1_funct_2(C_1506,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_1506,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_11427])).

tff(c_11494,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_11430])).

tff(c_110,plain,(
    ! [A_50,B_51] : v1_relat_1(k2_zfmisc_1(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_112,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_110])).

tff(c_11550,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11494,c_112])).

tff(c_11556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10302,c_11550])).

tff(c_11649,plain,(
    ! [C_1527] :
      ( k1_relset_1('#skF_1','#skF_1',C_1527) = '#skF_1'
      | ~ v1_funct_2(C_1527,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_1527,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_11430])).

tff(c_11652,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_8786,c_11649])).

tff(c_11663,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10204,c_11652])).

tff(c_11284,plain,(
    ! [B_1482,A_1483] :
      ( k10_relat_1(B_1482,k9_relat_1(B_1482,A_1483)) = A_1483
      | ~ v2_funct_1(B_1482)
      | ~ r1_tarski(A_1483,k1_relat_1(B_1482))
      | ~ v1_funct_1(B_1482)
      | ~ v1_relat_1(B_1482) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11887,plain,(
    ! [B_1534] :
      ( k10_relat_1(B_1534,k9_relat_1(B_1534,k1_relat_1(B_1534))) = k1_relat_1(B_1534)
      | ~ v2_funct_1(B_1534)
      | ~ v1_funct_1(B_1534)
      | ~ v1_relat_1(B_1534) ) ),
    inference(resolution,[status(thm)],[c_6,c_11284])).

tff(c_11900,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11663,c_11887])).

tff(c_11912,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5658,c_78,c_10804,c_11663,c_11900])).

tff(c_11914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10908,c_11912])).

tff(c_11915,plain,(
    v1_relat_1(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10296])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8903,plain,(
    ! [C_1173,A_1174] :
      ( v4_relat_1(C_1173,A_1174)
      | ~ m1_subset_1(C_1173,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8822])).

tff(c_8913,plain,(
    ! [A_1175,A_1176] :
      ( v4_relat_1(A_1175,A_1176)
      | ~ r1_tarski(A_1175,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_8903])).

tff(c_146,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_132])).

tff(c_5699,plain,(
    ! [B_784] :
      ( k1_relat_1(B_784) = k1_xboole_0
      | ~ v4_relat_1(B_784,k1_xboole_0)
      | ~ v1_relat_1(B_784) ) ),
    inference(resolution,[status(thm)],[c_5688,c_146])).

tff(c_9007,plain,(
    ! [A_1191] :
      ( k1_relat_1(A_1191) = k1_xboole_0
      | ~ v1_relat_1(A_1191)
      | ~ r1_tarski(A_1191,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8913,c_5699])).

tff(c_12482,plain,(
    ! [B_1599] :
      ( k1_relat_1(k1_relat_1(B_1599)) = k1_xboole_0
      | ~ v1_relat_1(k1_relat_1(B_1599))
      | ~ v4_relat_1(B_1599,k1_xboole_0)
      | ~ v1_relat_1(B_1599) ) ),
    inference(resolution,[status(thm)],[c_28,c_9007])).

tff(c_12497,plain,
    ( k1_relat_1(k1_relat_1('#skF_3')) = k1_xboole_0
    | ~ v4_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11915,c_12482])).

tff(c_12509,plain,
    ( k1_relat_1(k1_relat_1('#skF_3')) = k1_xboole_0
    | ~ v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5658,c_12497])).

tff(c_12512,plain,(
    ~ v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_12509])).

tff(c_13178,plain,(
    ~ v4_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13157,c_12512])).

tff(c_13224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8931,c_13178])).

tff(c_13226,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13121])).

tff(c_13288,plain,(
    ! [B_1688,A_1689,C_1690] :
      ( k1_xboole_0 = B_1688
      | k1_relset_1(A_1689,B_1688,C_1690) = A_1689
      | ~ v1_funct_2(C_1690,A_1689,B_1688)
      | ~ m1_subset_1(C_1690,k1_zfmisc_1(k2_zfmisc_1(A_1689,B_1688))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_13291,plain,(
    ! [C_1690] :
      ( k1_xboole_0 = '#skF_1'
      | k1_relset_1('#skF_1','#skF_1',C_1690) = '#skF_1'
      | ~ v1_funct_2(C_1690,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_1690,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_13288])).

tff(c_13435,plain,(
    ! [C_1702] :
      ( k1_relset_1('#skF_1','#skF_1',C_1702) = '#skF_1'
      | ~ v1_funct_2(C_1702,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_1702,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13226,c_13291])).

tff(c_13438,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_8786,c_13435])).

tff(c_13449,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10204,c_13438])).

tff(c_12923,plain,(
    ! [B_1655,A_1656] :
      ( k10_relat_1(B_1655,k9_relat_1(B_1655,A_1656)) = A_1656
      | ~ v2_funct_1(B_1655)
      | ~ r1_tarski(A_1656,k1_relat_1(B_1655))
      | ~ v1_funct_1(B_1655)
      | ~ v1_relat_1(B_1655) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_13571,plain,(
    ! [B_1703] :
      ( k10_relat_1(B_1703,k9_relat_1(B_1703,k1_relat_1(B_1703))) = k1_relat_1(B_1703)
      | ~ v2_funct_1(B_1703)
      | ~ v1_funct_1(B_1703)
      | ~ v1_relat_1(B_1703) ) ),
    inference(resolution,[status(thm)],[c_6,c_12923])).

tff(c_13584,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13449,c_13571])).

tff(c_13599,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5658,c_78,c_12343,c_13449,c_13584])).

tff(c_13601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12663,c_13599])).

tff(c_13603,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_12509])).

tff(c_13608,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_13603,c_5699])).

tff(c_13614,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5658,c_13608])).

tff(c_14297,plain,(
    ! [B_1771,A_1772] :
      ( k10_relat_1(B_1771,k9_relat_1(B_1771,A_1772)) = A_1772
      | ~ v2_funct_1(B_1771)
      | ~ r1_tarski(A_1772,k1_relat_1(B_1771))
      | ~ v1_funct_1(B_1771)
      | ~ v1_relat_1(B_1771) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14303,plain,(
    ! [A_1772] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_1772)) = A_1772
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_1772,k1_xboole_0)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13614,c_14297])).

tff(c_14322,plain,(
    ! [A_1773] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_1773)) = A_1773
      | ~ r1_tarski(A_1773,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5658,c_78,c_12343,c_14303])).

tff(c_13965,plain,(
    ! [A_1729,B_1730,C_1731,D_1732] :
      ( k7_relset_1(A_1729,B_1730,C_1731,D_1732) = k9_relat_1(C_1731,D_1732)
      | ~ m1_subset_1(C_1731,k1_zfmisc_1(k2_zfmisc_1(A_1729,B_1730))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14014,plain,(
    ! [C_1742,D_1743] :
      ( k7_relset_1('#skF_1','#skF_1',C_1742,D_1743) = k9_relat_1(C_1742,D_1743)
      | ~ m1_subset_1(C_1742,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_13965])).

tff(c_14023,plain,(
    ! [D_1743] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_1743) = k9_relat_1('#skF_3',D_1743) ),
    inference(resolution,[status(thm)],[c_8786,c_14014])).

tff(c_13863,plain,(
    ! [A_1708,B_1709,C_1710,D_1711] :
      ( k8_relset_1(A_1708,B_1709,C_1710,D_1711) = k10_relat_1(C_1710,D_1711)
      | ~ m1_subset_1(C_1710,k1_zfmisc_1(k2_zfmisc_1(A_1708,B_1709))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_13912,plain,(
    ! [C_1721,D_1722] :
      ( k8_relset_1('#skF_1','#skF_1',C_1721,D_1722) = k10_relat_1(C_1721,D_1722)
      | ~ m1_subset_1(C_1721,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_13863])).

tff(c_13921,plain,(
    ! [D_1722] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_1722) = k10_relat_1('#skF_3',D_1722) ),
    inference(resolution,[status(thm)],[c_8786,c_13912])).

tff(c_13926,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13921,c_5643])).

tff(c_14027,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14023,c_13926])).

tff(c_14350,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14322,c_14027])).

tff(c_14538,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14530,c_14350])).

tff(c_14600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14538])).

tff(c_14602,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14448])).

tff(c_13616,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13614,c_10204])).

tff(c_14658,plain,(
    ! [B_1803,A_1804,C_1805] :
      ( k1_xboole_0 = B_1803
      | k1_relset_1(A_1804,B_1803,C_1805) = A_1804
      | ~ v1_funct_2(C_1805,A_1804,B_1803)
      | ~ m1_subset_1(C_1805,k1_zfmisc_1(k2_zfmisc_1(A_1804,B_1803))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14661,plain,(
    ! [C_1805] :
      ( k1_xboole_0 = '#skF_1'
      | k1_relset_1('#skF_1','#skF_1',C_1805) = '#skF_1'
      | ~ v1_funct_2(C_1805,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_1805,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_14658])).

tff(c_14712,plain,(
    ! [C_1808] :
      ( k1_relset_1('#skF_1','#skF_1',C_1808) = '#skF_1'
      | ~ v1_funct_2(C_1808,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_1808,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14602,c_14661])).

tff(c_14715,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_8786,c_14712])).

tff(c_14726,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13616,c_14715])).

tff(c_14728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14602,c_14726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.59/3.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/3.24  
% 8.81/3.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/3.25  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.81/3.25  
% 8.81/3.25  %Foreground sorts:
% 8.81/3.25  
% 8.81/3.25  
% 8.81/3.25  %Background operators:
% 8.81/3.25  
% 8.81/3.25  
% 8.81/3.25  %Foreground operators:
% 8.81/3.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.81/3.25  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.81/3.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.81/3.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.81/3.25  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 8.81/3.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.81/3.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.81/3.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.81/3.25  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.81/3.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.81/3.25  tff('#skF_2', type, '#skF_2': $i).
% 8.81/3.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.81/3.25  tff('#skF_3', type, '#skF_3': $i).
% 8.81/3.25  tff('#skF_1', type, '#skF_1': $i).
% 8.81/3.25  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.81/3.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.81/3.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.81/3.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.81/3.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.81/3.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.81/3.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.81/3.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.81/3.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.81/3.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.81/3.25  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 8.81/3.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.81/3.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.81/3.25  
% 8.81/3.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.81/3.28  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.81/3.28  tff(f_155, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_funct_2)).
% 8.81/3.28  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.81/3.28  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 8.81/3.28  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.81/3.28  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.81/3.28  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 8.81/3.28  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 8.81/3.28  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.81/3.28  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.81/3.28  tff(f_140, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 8.81/3.28  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 8.81/3.28  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.81/3.28  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.81/3.28  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.81/3.28  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.81/3.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.81/3.28  tff(c_30, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.81/3.28  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.81/3.28  tff(c_5645, plain, (![B_778, A_779]: (v1_relat_1(B_778) | ~m1_subset_1(B_778, k1_zfmisc_1(A_779)) | ~v1_relat_1(A_779))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.81/3.28  tff(c_5651, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_5645])).
% 8.81/3.28  tff(c_5658, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_5651])).
% 8.81/3.28  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.81/3.28  tff(c_74, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.81/3.28  tff(c_7814, plain, (![C_1066, A_1067, B_1068]: (v2_funct_1(C_1066) | ~v3_funct_2(C_1066, A_1067, B_1068) | ~v1_funct_1(C_1066) | ~m1_subset_1(C_1066, k1_zfmisc_1(k2_zfmisc_1(A_1067, B_1068))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.81/3.28  tff(c_7821, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_7814])).
% 8.81/3.28  tff(c_7835, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_7821])).
% 8.81/3.28  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.81/3.28  tff(c_7771, plain, (![A_1059, B_1060, C_1061]: (k1_relset_1(A_1059, B_1060, C_1061)=k1_relat_1(C_1061) | ~m1_subset_1(C_1061, k1_zfmisc_1(k2_zfmisc_1(A_1059, B_1060))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.81/3.28  tff(c_7790, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_7771])).
% 8.81/3.28  tff(c_8426, plain, (![B_1147, A_1148, C_1149]: (k1_xboole_0=B_1147 | k1_relset_1(A_1148, B_1147, C_1149)=A_1148 | ~v1_funct_2(C_1149, A_1148, B_1147) | ~m1_subset_1(C_1149, k1_zfmisc_1(k2_zfmisc_1(A_1148, B_1147))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.81/3.28  tff(c_8433, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_8426])).
% 8.81/3.28  tff(c_8447, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7790, c_8433])).
% 8.81/3.28  tff(c_8451, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_8447])).
% 8.81/3.28  tff(c_34, plain, (![B_22, A_21]: (k10_relat_1(B_22, k9_relat_1(B_22, A_21))=A_21 | ~v2_funct_1(B_22) | ~r1_tarski(A_21, k1_relat_1(B_22)) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.81/3.28  tff(c_8457, plain, (![A_21]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_21))=A_21 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_21, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8451, c_34])).
% 8.81/3.28  tff(c_8627, plain, (![A_1159]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_1159))=A_1159 | ~r1_tarski(A_1159, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5658, c_78, c_7835, c_8457])).
% 8.81/3.28  tff(c_8031, plain, (![A_1098, B_1099, C_1100, D_1101]: (k8_relset_1(A_1098, B_1099, C_1100, D_1101)=k10_relat_1(C_1100, D_1101) | ~m1_subset_1(C_1100, k1_zfmisc_1(k2_zfmisc_1(A_1098, B_1099))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.81/3.28  tff(c_8045, plain, (![D_1101]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_1101)=k10_relat_1('#skF_3', D_1101))), inference(resolution, [status(thm)], [c_72, c_8031])).
% 8.81/3.28  tff(c_7906, plain, (![A_1080, B_1081, C_1082, D_1083]: (k7_relset_1(A_1080, B_1081, C_1082, D_1083)=k9_relat_1(C_1082, D_1083) | ~m1_subset_1(C_1082, k1_zfmisc_1(k2_zfmisc_1(A_1080, B_1081))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.81/3.28  tff(c_7920, plain, (![D_1083]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_1083)=k9_relat_1('#skF_3', D_1083))), inference(resolution, [status(thm)], [c_72, c_7906])).
% 8.81/3.28  tff(c_70, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.81/3.28  tff(c_1435, plain, (![B_247, A_248]: (v1_relat_1(B_247) | ~m1_subset_1(B_247, k1_zfmisc_1(A_248)) | ~v1_relat_1(A_248))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.81/3.28  tff(c_1441, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_1435])).
% 8.81/3.28  tff(c_1448, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1441])).
% 8.81/3.28  tff(c_4720, plain, (![C_684, A_685, B_686]: (v2_funct_1(C_684) | ~v3_funct_2(C_684, A_685, B_686) | ~v1_funct_1(C_684) | ~m1_subset_1(C_684, k1_zfmisc_1(k2_zfmisc_1(A_685, B_686))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.81/3.28  tff(c_4727, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_4720])).
% 8.81/3.28  tff(c_4741, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_4727])).
% 8.81/3.28  tff(c_4105, plain, (![A_600, B_601, C_602]: (k1_relset_1(A_600, B_601, C_602)=k1_relat_1(C_602) | ~m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(A_600, B_601))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.81/3.28  tff(c_4124, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_4105])).
% 8.81/3.28  tff(c_5340, plain, (![B_766, A_767, C_768]: (k1_xboole_0=B_766 | k1_relset_1(A_767, B_766, C_768)=A_767 | ~v1_funct_2(C_768, A_767, B_766) | ~m1_subset_1(C_768, k1_zfmisc_1(k2_zfmisc_1(A_767, B_766))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.81/3.28  tff(c_5347, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_5340])).
% 8.81/3.28  tff(c_5361, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4124, c_5347])).
% 8.81/3.28  tff(c_5365, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_5361])).
% 8.81/3.28  tff(c_5374, plain, (![A_21]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_21))=A_21 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_21, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5365, c_34])).
% 8.81/3.28  tff(c_5523, plain, (![A_776]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_776))=A_776 | ~r1_tarski(A_776, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_78, c_4741, c_5374])).
% 8.81/3.28  tff(c_4960, plain, (![A_717, B_718, C_719, D_720]: (k8_relset_1(A_717, B_718, C_719, D_720)=k10_relat_1(C_719, D_720) | ~m1_subset_1(C_719, k1_zfmisc_1(k2_zfmisc_1(A_717, B_718))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.81/3.28  tff(c_4974, plain, (![D_720]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_720)=k10_relat_1('#skF_3', D_720))), inference(resolution, [status(thm)], [c_72, c_4960])).
% 8.81/3.28  tff(c_4838, plain, (![A_700, B_701, C_702, D_703]: (k7_relset_1(A_700, B_701, C_702, D_703)=k9_relat_1(C_702, D_703) | ~m1_subset_1(C_702, k1_zfmisc_1(k2_zfmisc_1(A_700, B_701))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.81/3.28  tff(c_4852, plain, (![D_703]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_703)=k9_relat_1('#skF_3', D_703))), inference(resolution, [status(thm)], [c_72, c_4838])).
% 8.81/3.28  tff(c_174, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.81/3.28  tff(c_180, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_174])).
% 8.81/3.28  tff(c_187, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_180])).
% 8.81/3.28  tff(c_257, plain, (![C_75, B_76, A_77]: (v5_relat_1(C_75, B_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.81/3.28  tff(c_276, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_257])).
% 8.81/3.28  tff(c_470, plain, (![B_109, A_110]: (k2_relat_1(B_109)=A_110 | ~v2_funct_2(B_109, A_110) | ~v5_relat_1(B_109, A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.81/3.28  tff(c_482, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_276, c_470])).
% 8.81/3.28  tff(c_492, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_482])).
% 8.81/3.28  tff(c_499, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_492])).
% 8.81/3.28  tff(c_954, plain, (![C_181, B_182, A_183]: (v2_funct_2(C_181, B_182) | ~v3_funct_2(C_181, A_183, B_182) | ~v1_funct_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.81/3.28  tff(c_961, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_954])).
% 8.81/3.28  tff(c_975, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_961])).
% 8.81/3.28  tff(c_977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_499, c_975])).
% 8.81/3.28  tff(c_978, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_492])).
% 8.81/3.28  tff(c_1190, plain, (![B_214, A_215]: (k9_relat_1(B_214, k10_relat_1(B_214, A_215))=A_215 | ~r1_tarski(A_215, k2_relat_1(B_214)) | ~v1_funct_1(B_214) | ~v1_relat_1(B_214))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.81/3.28  tff(c_1192, plain, (![A_215]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_215))=A_215 | ~r1_tarski(A_215, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_978, c_1190])).
% 8.81/3.28  tff(c_1203, plain, (![A_215]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_215))=A_215 | ~r1_tarski(A_215, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_78, c_1192])).
% 8.81/3.28  tff(c_1395, plain, (![A_242, B_243, C_244, D_245]: (k7_relset_1(A_242, B_243, C_244, D_245)=k9_relat_1(C_244, D_245) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.81/3.28  tff(c_1409, plain, (![D_245]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_245)=k9_relat_1('#skF_3', D_245))), inference(resolution, [status(thm)], [c_72, c_1395])).
% 8.81/3.28  tff(c_1322, plain, (![A_228, B_229, C_230, D_231]: (k8_relset_1(A_228, B_229, C_230, D_231)=k10_relat_1(C_230, D_231) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.81/3.28  tff(c_1336, plain, (![D_231]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_231)=k10_relat_1('#skF_3', D_231))), inference(resolution, [status(thm)], [c_72, c_1322])).
% 8.81/3.28  tff(c_68, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.81/3.28  tff(c_161, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_68])).
% 8.81/3.28  tff(c_1338, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_161])).
% 8.81/3.28  tff(c_1411, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_1338])).
% 8.81/3.28  tff(c_1423, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1203, c_1411])).
% 8.81/3.28  tff(c_1427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1423])).
% 8.81/3.28  tff(c_1428, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_68])).
% 8.81/3.28  tff(c_4854, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4852, c_1428])).
% 8.81/3.28  tff(c_4977, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4974, c_4854])).
% 8.81/3.28  tff(c_5536, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5523, c_4977])).
% 8.81/3.28  tff(c_5562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_5536])).
% 8.81/3.28  tff(c_5563, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5361])).
% 8.81/3.28  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.81/3.28  tff(c_5612, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5563, c_8])).
% 8.81/3.28  tff(c_132, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.81/3.28  tff(c_147, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_132])).
% 8.81/3.28  tff(c_1430, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_147])).
% 8.81/3.28  tff(c_5634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5612, c_1430])).
% 8.81/3.28  tff(c_5635, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_147])).
% 8.81/3.28  tff(c_5643, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5635, c_5635, c_1428])).
% 8.81/3.28  tff(c_7922, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7920, c_5643])).
% 8.81/3.28  tff(c_8048, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8045, c_7922])).
% 8.81/3.28  tff(c_8636, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8627, c_8048])).
% 8.81/3.28  tff(c_8659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8636])).
% 8.81/3.28  tff(c_8660, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_8447])).
% 8.81/3.28  tff(c_8706, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8660, c_8])).
% 8.81/3.28  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.81/3.28  tff(c_8704, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8660, c_8660, c_14])).
% 8.81/3.28  tff(c_117, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.81/3.28  tff(c_124, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_117])).
% 8.81/3.28  tff(c_141, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_124, c_132])).
% 8.81/3.28  tff(c_5801, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_141])).
% 8.81/3.28  tff(c_8777, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8704, c_5801])).
% 8.81/3.28  tff(c_8782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8706, c_8777])).
% 8.81/3.28  tff(c_8783, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_141])).
% 8.81/3.28  tff(c_14445, plain, (![B_1789, C_1790, A_1791]: (k1_xboole_0=B_1789 | v1_funct_2(C_1790, A_1791, B_1789) | k1_relset_1(A_1791, B_1789, C_1790)!=A_1791 | ~m1_subset_1(C_1790, k1_zfmisc_1(k2_zfmisc_1(A_1791, B_1789))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.81/3.28  tff(c_14448, plain, (![C_1790]: (k1_xboole_0='#skF_1' | v1_funct_2(C_1790, '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', C_1790)!='#skF_1' | ~m1_subset_1(C_1790, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_14445])).
% 8.81/3.28  tff(c_14530, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_14448])).
% 8.81/3.28  tff(c_8786, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8783, c_72])).
% 8.81/3.28  tff(c_12301, plain, (![C_1579, A_1580, B_1581]: (v2_funct_1(C_1579) | ~v3_funct_2(C_1579, A_1580, B_1581) | ~v1_funct_1(C_1579) | ~m1_subset_1(C_1579, k1_zfmisc_1(k2_zfmisc_1(A_1580, B_1581))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.81/3.28  tff(c_12329, plain, (![C_1583]: (v2_funct_1(C_1583) | ~v3_funct_2(C_1583, '#skF_1', '#skF_1') | ~v1_funct_1(C_1583) | ~m1_subset_1(C_1583, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_12301])).
% 8.81/3.28  tff(c_12332, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_8786, c_12329])).
% 8.81/3.28  tff(c_12343, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_12332])).
% 8.81/3.28  tff(c_12600, plain, (![A_1616, B_1617, C_1618, D_1619]: (k8_relset_1(A_1616, B_1617, C_1618, D_1619)=k10_relat_1(C_1618, D_1619) | ~m1_subset_1(C_1618, k1_zfmisc_1(k2_zfmisc_1(A_1616, B_1617))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.81/3.28  tff(c_12649, plain, (![C_1628, D_1629]: (k8_relset_1('#skF_1', '#skF_1', C_1628, D_1629)=k10_relat_1(C_1628, D_1629) | ~m1_subset_1(C_1628, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_12600])).
% 8.81/3.28  tff(c_12658, plain, (![D_1629]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_1629)=k10_relat_1('#skF_3', D_1629))), inference(resolution, [status(thm)], [c_8786, c_12649])).
% 8.81/3.28  tff(c_12517, plain, (![A_1600, B_1601, C_1602, D_1603]: (k7_relset_1(A_1600, B_1601, C_1602, D_1603)=k9_relat_1(C_1602, D_1603) | ~m1_subset_1(C_1602, k1_zfmisc_1(k2_zfmisc_1(A_1600, B_1601))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.81/3.28  tff(c_12551, plain, (![C_1610, D_1611]: (k7_relset_1('#skF_1', '#skF_1', C_1610, D_1611)=k9_relat_1(C_1610, D_1611) | ~m1_subset_1(C_1610, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_12517])).
% 8.81/3.28  tff(c_12560, plain, (![D_1611]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_1611)=k9_relat_1('#skF_3', D_1611))), inference(resolution, [status(thm)], [c_8786, c_12551])).
% 8.81/3.28  tff(c_12564, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12560, c_5643])).
% 8.81/3.28  tff(c_12663, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12658, c_12564])).
% 8.81/3.28  tff(c_10140, plain, (![A_1342, B_1343, C_1344]: (k1_relset_1(A_1342, B_1343, C_1344)=k1_relat_1(C_1344) | ~m1_subset_1(C_1344, k1_zfmisc_1(k2_zfmisc_1(A_1342, B_1343))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.81/3.28  tff(c_10192, plain, (![C_1350]: (k1_relset_1('#skF_1', '#skF_1', C_1350)=k1_relat_1(C_1350) | ~m1_subset_1(C_1350, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_10140])).
% 8.81/3.28  tff(c_10204, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8786, c_10192])).
% 8.81/3.28  tff(c_8822, plain, (![C_1166, A_1167, B_1168]: (v4_relat_1(C_1166, A_1167) | ~m1_subset_1(C_1166, k1_zfmisc_1(k2_zfmisc_1(A_1167, B_1168))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.81/3.28  tff(c_8919, plain, (![C_1177]: (v4_relat_1(C_1177, '#skF_1') | ~m1_subset_1(C_1177, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_8822])).
% 8.81/3.28  tff(c_8931, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_8786, c_8919])).
% 8.81/3.28  tff(c_13118, plain, (![B_1668, C_1669, A_1670]: (k1_xboole_0=B_1668 | v1_funct_2(C_1669, A_1670, B_1668) | k1_relset_1(A_1670, B_1668, C_1669)!=A_1670 | ~m1_subset_1(C_1669, k1_zfmisc_1(k2_zfmisc_1(A_1670, B_1668))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.81/3.28  tff(c_13121, plain, (![C_1669]: (k1_xboole_0='#skF_1' | v1_funct_2(C_1669, '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', C_1669)!='#skF_1' | ~m1_subset_1(C_1669, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_13118])).
% 8.81/3.28  tff(c_13157, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_13121])).
% 8.81/3.28  tff(c_10845, plain, (![A_1430, B_1431, C_1432, D_1433]: (k8_relset_1(A_1430, B_1431, C_1432, D_1433)=k10_relat_1(C_1432, D_1433) | ~m1_subset_1(C_1432, k1_zfmisc_1(k2_zfmisc_1(A_1430, B_1431))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.81/3.28  tff(c_10894, plain, (![C_1443, D_1444]: (k8_relset_1('#skF_1', '#skF_1', C_1443, D_1444)=k10_relat_1(C_1443, D_1444) | ~m1_subset_1(C_1443, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_10845])).
% 8.81/3.28  tff(c_10903, plain, (![D_1444]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_1444)=k10_relat_1('#skF_3', D_1444))), inference(resolution, [status(thm)], [c_8786, c_10894])).
% 8.81/3.28  tff(c_10646, plain, (![A_1402, B_1403, C_1404, D_1405]: (k7_relset_1(A_1402, B_1403, C_1404, D_1405)=k9_relat_1(C_1404, D_1405) | ~m1_subset_1(C_1404, k1_zfmisc_1(k2_zfmisc_1(A_1402, B_1403))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.81/3.28  tff(c_10701, plain, (![C_1412, D_1413]: (k7_relset_1('#skF_1', '#skF_1', C_1412, D_1413)=k9_relat_1(C_1412, D_1413) | ~m1_subset_1(C_1412, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_10646])).
% 8.81/3.28  tff(c_10710, plain, (![D_1413]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_1413)=k9_relat_1('#skF_3', D_1413))), inference(resolution, [status(thm)], [c_8786, c_10701])).
% 8.81/3.28  tff(c_10714, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10710, c_5643])).
% 8.81/3.28  tff(c_10908, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10903, c_10714])).
% 8.81/3.28  tff(c_10754, plain, (![C_1417, A_1418, B_1419]: (v2_funct_1(C_1417) | ~v3_funct_2(C_1417, A_1418, B_1419) | ~v1_funct_1(C_1417) | ~m1_subset_1(C_1417, k1_zfmisc_1(k2_zfmisc_1(A_1418, B_1419))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.81/3.28  tff(c_10790, plain, (![C_1422]: (v2_funct_1(C_1422) | ~v3_funct_2(C_1422, '#skF_1', '#skF_1') | ~v1_funct_1(C_1422) | ~m1_subset_1(C_1422, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_10754])).
% 8.81/3.28  tff(c_10793, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_8786, c_10790])).
% 8.81/3.28  tff(c_10804, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_10793])).
% 8.81/3.28  tff(c_5688, plain, (![B_784, A_785]: (r1_tarski(k1_relat_1(B_784), A_785) | ~v4_relat_1(B_784, A_785) | ~v1_relat_1(B_784))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.81/3.28  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.81/3.28  tff(c_5655, plain, (![A_7, B_8]: (v1_relat_1(A_7) | ~v1_relat_1(B_8) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_20, c_5645])).
% 8.81/3.28  tff(c_10277, plain, (![B_1360, A_1361]: (v1_relat_1(k1_relat_1(B_1360)) | ~v1_relat_1(A_1361) | ~v4_relat_1(B_1360, A_1361) | ~v1_relat_1(B_1360))), inference(resolution, [status(thm)], [c_5688, c_5655])).
% 8.81/3.28  tff(c_10283, plain, (v1_relat_1(k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8931, c_10277])).
% 8.81/3.28  tff(c_10296, plain, (v1_relat_1(k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5658, c_10283])).
% 8.81/3.28  tff(c_10302, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_10296])).
% 8.81/3.28  tff(c_11427, plain, (![B_1504, A_1505, C_1506]: (k1_xboole_0=B_1504 | k1_relset_1(A_1505, B_1504, C_1506)=A_1505 | ~v1_funct_2(C_1506, A_1505, B_1504) | ~m1_subset_1(C_1506, k1_zfmisc_1(k2_zfmisc_1(A_1505, B_1504))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.81/3.28  tff(c_11430, plain, (![C_1506]: (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', C_1506)='#skF_1' | ~v1_funct_2(C_1506, '#skF_1', '#skF_1') | ~m1_subset_1(C_1506, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_11427])).
% 8.81/3.28  tff(c_11494, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_11430])).
% 8.81/3.28  tff(c_110, plain, (![A_50, B_51]: (v1_relat_1(k2_zfmisc_1(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.81/3.28  tff(c_112, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_110])).
% 8.81/3.28  tff(c_11550, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11494, c_112])).
% 8.81/3.28  tff(c_11556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10302, c_11550])).
% 8.81/3.28  tff(c_11649, plain, (![C_1527]: (k1_relset_1('#skF_1', '#skF_1', C_1527)='#skF_1' | ~v1_funct_2(C_1527, '#skF_1', '#skF_1') | ~m1_subset_1(C_1527, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_11430])).
% 8.81/3.28  tff(c_11652, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_8786, c_11649])).
% 8.81/3.28  tff(c_11663, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10204, c_11652])).
% 8.81/3.28  tff(c_11284, plain, (![B_1482, A_1483]: (k10_relat_1(B_1482, k9_relat_1(B_1482, A_1483))=A_1483 | ~v2_funct_1(B_1482) | ~r1_tarski(A_1483, k1_relat_1(B_1482)) | ~v1_funct_1(B_1482) | ~v1_relat_1(B_1482))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.81/3.28  tff(c_11887, plain, (![B_1534]: (k10_relat_1(B_1534, k9_relat_1(B_1534, k1_relat_1(B_1534)))=k1_relat_1(B_1534) | ~v2_funct_1(B_1534) | ~v1_funct_1(B_1534) | ~v1_relat_1(B_1534))), inference(resolution, [status(thm)], [c_6, c_11284])).
% 8.81/3.28  tff(c_11900, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11663, c_11887])).
% 8.81/3.28  tff(c_11912, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5658, c_78, c_10804, c_11663, c_11900])).
% 8.81/3.28  tff(c_11914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10908, c_11912])).
% 8.81/3.28  tff(c_11915, plain, (v1_relat_1(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10296])).
% 8.81/3.28  tff(c_28, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.81/3.28  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.81/3.28  tff(c_8903, plain, (![C_1173, A_1174]: (v4_relat_1(C_1173, A_1174) | ~m1_subset_1(C_1173, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8822])).
% 8.81/3.28  tff(c_8913, plain, (![A_1175, A_1176]: (v4_relat_1(A_1175, A_1176) | ~r1_tarski(A_1175, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_8903])).
% 8.81/3.28  tff(c_146, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_132])).
% 8.81/3.28  tff(c_5699, plain, (![B_784]: (k1_relat_1(B_784)=k1_xboole_0 | ~v4_relat_1(B_784, k1_xboole_0) | ~v1_relat_1(B_784))), inference(resolution, [status(thm)], [c_5688, c_146])).
% 8.81/3.28  tff(c_9007, plain, (![A_1191]: (k1_relat_1(A_1191)=k1_xboole_0 | ~v1_relat_1(A_1191) | ~r1_tarski(A_1191, k1_xboole_0))), inference(resolution, [status(thm)], [c_8913, c_5699])).
% 8.81/3.28  tff(c_12482, plain, (![B_1599]: (k1_relat_1(k1_relat_1(B_1599))=k1_xboole_0 | ~v1_relat_1(k1_relat_1(B_1599)) | ~v4_relat_1(B_1599, k1_xboole_0) | ~v1_relat_1(B_1599))), inference(resolution, [status(thm)], [c_28, c_9007])).
% 8.81/3.28  tff(c_12497, plain, (k1_relat_1(k1_relat_1('#skF_3'))=k1_xboole_0 | ~v4_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11915, c_12482])).
% 8.81/3.28  tff(c_12509, plain, (k1_relat_1(k1_relat_1('#skF_3'))=k1_xboole_0 | ~v4_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5658, c_12497])).
% 8.81/3.28  tff(c_12512, plain, (~v4_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_12509])).
% 8.81/3.28  tff(c_13178, plain, (~v4_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13157, c_12512])).
% 8.81/3.28  tff(c_13224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8931, c_13178])).
% 8.81/3.28  tff(c_13226, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_13121])).
% 8.81/3.28  tff(c_13288, plain, (![B_1688, A_1689, C_1690]: (k1_xboole_0=B_1688 | k1_relset_1(A_1689, B_1688, C_1690)=A_1689 | ~v1_funct_2(C_1690, A_1689, B_1688) | ~m1_subset_1(C_1690, k1_zfmisc_1(k2_zfmisc_1(A_1689, B_1688))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.81/3.28  tff(c_13291, plain, (![C_1690]: (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', C_1690)='#skF_1' | ~v1_funct_2(C_1690, '#skF_1', '#skF_1') | ~m1_subset_1(C_1690, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_13288])).
% 8.81/3.28  tff(c_13435, plain, (![C_1702]: (k1_relset_1('#skF_1', '#skF_1', C_1702)='#skF_1' | ~v1_funct_2(C_1702, '#skF_1', '#skF_1') | ~m1_subset_1(C_1702, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_13226, c_13291])).
% 8.81/3.28  tff(c_13438, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_8786, c_13435])).
% 8.81/3.28  tff(c_13449, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10204, c_13438])).
% 8.81/3.28  tff(c_12923, plain, (![B_1655, A_1656]: (k10_relat_1(B_1655, k9_relat_1(B_1655, A_1656))=A_1656 | ~v2_funct_1(B_1655) | ~r1_tarski(A_1656, k1_relat_1(B_1655)) | ~v1_funct_1(B_1655) | ~v1_relat_1(B_1655))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.81/3.28  tff(c_13571, plain, (![B_1703]: (k10_relat_1(B_1703, k9_relat_1(B_1703, k1_relat_1(B_1703)))=k1_relat_1(B_1703) | ~v2_funct_1(B_1703) | ~v1_funct_1(B_1703) | ~v1_relat_1(B_1703))), inference(resolution, [status(thm)], [c_6, c_12923])).
% 8.81/3.28  tff(c_13584, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13449, c_13571])).
% 8.81/3.28  tff(c_13599, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5658, c_78, c_12343, c_13449, c_13584])).
% 8.81/3.28  tff(c_13601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12663, c_13599])).
% 8.81/3.28  tff(c_13603, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_12509])).
% 8.81/3.28  tff(c_13608, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_13603, c_5699])).
% 8.81/3.28  tff(c_13614, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5658, c_13608])).
% 8.81/3.28  tff(c_14297, plain, (![B_1771, A_1772]: (k10_relat_1(B_1771, k9_relat_1(B_1771, A_1772))=A_1772 | ~v2_funct_1(B_1771) | ~r1_tarski(A_1772, k1_relat_1(B_1771)) | ~v1_funct_1(B_1771) | ~v1_relat_1(B_1771))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.81/3.28  tff(c_14303, plain, (![A_1772]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_1772))=A_1772 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_1772, k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13614, c_14297])).
% 8.81/3.28  tff(c_14322, plain, (![A_1773]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_1773))=A_1773 | ~r1_tarski(A_1773, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5658, c_78, c_12343, c_14303])).
% 8.81/3.28  tff(c_13965, plain, (![A_1729, B_1730, C_1731, D_1732]: (k7_relset_1(A_1729, B_1730, C_1731, D_1732)=k9_relat_1(C_1731, D_1732) | ~m1_subset_1(C_1731, k1_zfmisc_1(k2_zfmisc_1(A_1729, B_1730))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.81/3.28  tff(c_14014, plain, (![C_1742, D_1743]: (k7_relset_1('#skF_1', '#skF_1', C_1742, D_1743)=k9_relat_1(C_1742, D_1743) | ~m1_subset_1(C_1742, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_13965])).
% 8.81/3.28  tff(c_14023, plain, (![D_1743]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_1743)=k9_relat_1('#skF_3', D_1743))), inference(resolution, [status(thm)], [c_8786, c_14014])).
% 8.81/3.28  tff(c_13863, plain, (![A_1708, B_1709, C_1710, D_1711]: (k8_relset_1(A_1708, B_1709, C_1710, D_1711)=k10_relat_1(C_1710, D_1711) | ~m1_subset_1(C_1710, k1_zfmisc_1(k2_zfmisc_1(A_1708, B_1709))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.81/3.28  tff(c_13912, plain, (![C_1721, D_1722]: (k8_relset_1('#skF_1', '#skF_1', C_1721, D_1722)=k10_relat_1(C_1721, D_1722) | ~m1_subset_1(C_1721, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_13863])).
% 8.81/3.28  tff(c_13921, plain, (![D_1722]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_1722)=k10_relat_1('#skF_3', D_1722))), inference(resolution, [status(thm)], [c_8786, c_13912])).
% 8.81/3.28  tff(c_13926, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13921, c_5643])).
% 8.81/3.28  tff(c_14027, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14023, c_13926])).
% 8.81/3.28  tff(c_14350, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14322, c_14027])).
% 8.81/3.28  tff(c_14538, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14530, c_14350])).
% 8.81/3.28  tff(c_14600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14538])).
% 8.81/3.28  tff(c_14602, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_14448])).
% 8.81/3.28  tff(c_13616, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_13614, c_10204])).
% 8.81/3.28  tff(c_14658, plain, (![B_1803, A_1804, C_1805]: (k1_xboole_0=B_1803 | k1_relset_1(A_1804, B_1803, C_1805)=A_1804 | ~v1_funct_2(C_1805, A_1804, B_1803) | ~m1_subset_1(C_1805, k1_zfmisc_1(k2_zfmisc_1(A_1804, B_1803))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.81/3.28  tff(c_14661, plain, (![C_1805]: (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', C_1805)='#skF_1' | ~v1_funct_2(C_1805, '#skF_1', '#skF_1') | ~m1_subset_1(C_1805, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8783, c_14658])).
% 8.81/3.28  tff(c_14712, plain, (![C_1808]: (k1_relset_1('#skF_1', '#skF_1', C_1808)='#skF_1' | ~v1_funct_2(C_1808, '#skF_1', '#skF_1') | ~m1_subset_1(C_1808, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_14602, c_14661])).
% 8.81/3.28  tff(c_14715, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_8786, c_14712])).
% 8.81/3.28  tff(c_14726, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_13616, c_14715])).
% 8.81/3.28  tff(c_14728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14602, c_14726])).
% 8.81/3.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/3.28  
% 8.81/3.28  Inference rules
% 8.81/3.28  ----------------------
% 8.81/3.28  #Ref     : 0
% 8.81/3.28  #Sup     : 3031
% 8.81/3.28  #Fact    : 0
% 8.81/3.28  #Define  : 0
% 8.81/3.28  #Split   : 58
% 8.81/3.28  #Chain   : 0
% 8.81/3.28  #Close   : 0
% 8.81/3.28  
% 8.81/3.28  Ordering : KBO
% 8.81/3.28  
% 8.81/3.28  Simplification rules
% 8.81/3.28  ----------------------
% 8.81/3.28  #Subsume      : 463
% 8.81/3.28  #Demod        : 3296
% 8.81/3.28  #Tautology    : 1468
% 8.81/3.28  #SimpNegUnit  : 111
% 8.81/3.28  #BackRed      : 496
% 8.81/3.28  
% 8.81/3.28  #Partial instantiations: 0
% 8.81/3.28  #Strategies tried      : 1
% 8.81/3.28  
% 8.81/3.28  Timing (in seconds)
% 8.81/3.28  ----------------------
% 8.81/3.28  Preprocessing        : 0.35
% 8.81/3.28  Parsing              : 0.18
% 8.81/3.28  CNF conversion       : 0.02
% 8.81/3.28  Main loop            : 2.12
% 8.81/3.28  Inferencing          : 0.73
% 8.81/3.28  Reduction            : 0.73
% 8.81/3.28  Demodulation         : 0.51
% 8.81/3.28  BG Simplification    : 0.07
% 8.81/3.28  Subsumption          : 0.41
% 8.81/3.28  Abstraction          : 0.09
% 8.81/3.28  MUC search           : 0.00
% 8.81/3.28  Cooper               : 0.00
% 8.81/3.28  Total                : 2.55
% 8.81/3.28  Index Insertion      : 0.00
% 8.81/3.28  Index Deletion       : 0.00
% 8.81/3.28  Index Matching       : 0.00
% 8.81/3.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
