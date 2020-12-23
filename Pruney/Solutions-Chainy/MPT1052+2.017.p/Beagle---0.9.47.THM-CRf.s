%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:11 EST 2020

% Result     : Theorem 8.70s
% Output     : CNFRefutation 9.01s
% Verified   : 
% Statistics : Number of formulae       :  185 (2586 expanded)
%              Number of leaves         :   39 ( 837 expanded)
%              Depth                    :   13
%              Number of atoms          :  300 (5736 expanded)
%              Number of equality atoms :  114 (1320 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_80,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_7163,plain,(
    ! [A_1254,B_1255] :
      ( v1_xboole_0(k1_funct_2(A_1254,B_1255))
      | ~ v1_xboole_0(B_1255)
      | v1_xboole_0(A_1254) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_116,plain,(
    ! [B_38,A_39] :
      ( ~ r2_hidden(B_38,A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_116])).

tff(c_7170,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_7163,c_120])).

tff(c_7172,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7170])).

tff(c_62,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_145,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_151,plain,(
    ! [A_49,B_50] :
      ( v1_xboole_0(k1_funct_2(A_49,B_50))
      | ~ v1_xboole_0(B_50)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_158,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_151,c_120])).

tff(c_160,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_833,plain,(
    ! [C_80,A_81,B_82] :
      ( m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ r2_hidden(C_80,k1_funct_2(A_81,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_964,plain,(
    ! [C_93,A_94,B_95] :
      ( r1_tarski(C_93,k2_zfmisc_1(A_94,B_95))
      | ~ r2_hidden(C_93,k1_funct_2(A_94,B_95)) ) ),
    inference(resolution,[status(thm)],[c_833,c_20])).

tff(c_1009,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_964])).

tff(c_24,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k1_relat_1(k2_zfmisc_1(A_14,B_15)) = A_14
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_879,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k1_relat_1(A_86),k1_relat_1(B_87))
      | ~ r1_tarski(A_86,B_87)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_885,plain,(
    ! [A_86,A_14,B_15] :
      ( r1_tarski(k1_relat_1(A_86),A_14)
      | ~ r1_tarski(A_86,k2_zfmisc_1(A_14,B_15))
      | ~ v1_relat_1(k2_zfmisc_1(A_14,B_15))
      | ~ v1_relat_1(A_86)
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_879])).

tff(c_3988,plain,(
    ! [A_1162,A_1163,B_1164] :
      ( r1_tarski(k1_relat_1(A_1162),A_1163)
      | ~ r1_tarski(A_1162,k2_zfmisc_1(A_1163,B_1164))
      | ~ v1_relat_1(A_1162)
      | k1_xboole_0 = B_1164
      | k1_xboole_0 = A_1163 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_885])).

tff(c_3996,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1009,c_3988])).

tff(c_4009,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3996])).

tff(c_4014,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4009])).

tff(c_18,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4105,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_2',B_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_4014,c_18])).

tff(c_4262,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4105,c_1009])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4385,plain,(
    ! [A_1179] :
      ( A_1179 = '#skF_2'
      | ~ r1_tarski(A_1179,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_4014,c_12])).

tff(c_4393,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4262,c_4385])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4109,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_4014,c_36])).

tff(c_4411,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4393,c_4393,c_4109])).

tff(c_4419,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4393,c_145])).

tff(c_4501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4411,c_4419])).

tff(c_4503,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4009])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( k2_relat_1(k2_zfmisc_1(A_14,B_15)) = B_15
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1108,plain,(
    ! [A_115,B_116] :
      ( r1_tarski(k2_relat_1(A_115),k2_relat_1(B_116))
      | ~ r1_tarski(A_115,B_116)
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1114,plain,(
    ! [A_115,B_15,A_14] :
      ( r1_tarski(k2_relat_1(A_115),B_15)
      | ~ r1_tarski(A_115,k2_zfmisc_1(A_14,B_15))
      | ~ v1_relat_1(k2_zfmisc_1(A_14,B_15))
      | ~ v1_relat_1(A_115)
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1108])).

tff(c_4628,plain,(
    ! [A_1188,B_1189,A_1190] :
      ( r1_tarski(k2_relat_1(A_1188),B_1189)
      | ~ r1_tarski(A_1188,k2_zfmisc_1(A_1190,B_1189))
      | ~ v1_relat_1(A_1188)
      | k1_xboole_0 = B_1189
      | k1_xboole_0 = A_1190 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1114])).

tff(c_4638,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1009,c_4628])).

tff(c_4652,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4638])).

tff(c_4653,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4503,c_4652])).

tff(c_4658,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4653])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4758,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4658,c_6])).

tff(c_4760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_4758])).

tff(c_4762,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4653])).

tff(c_303,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_funct_2(C_62,A_63,B_64)
      | ~ r2_hidden(C_62,k1_funct_2(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_321,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_303])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1010,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1170,plain,(
    ! [A_119,B_120,A_121] :
      ( k1_relset_1(A_119,B_120,A_121) = k1_relat_1(A_121)
      | ~ r1_tarski(A_121,k2_zfmisc_1(A_119,B_120)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1010])).

tff(c_1184,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1009,c_1170])).

tff(c_2422,plain,(
    ! [B_1100,A_1101,C_1102] :
      ( k1_xboole_0 = B_1100
      | k1_relset_1(A_1101,B_1100,C_1102) = A_1101
      | ~ v1_funct_2(C_1102,A_1101,B_1100)
      | ~ m1_subset_1(C_1102,k1_zfmisc_1(k2_zfmisc_1(A_1101,B_1100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6702,plain,(
    ! [B_1212,A_1213,A_1214] :
      ( k1_xboole_0 = B_1212
      | k1_relset_1(A_1213,B_1212,A_1214) = A_1213
      | ~ v1_funct_2(A_1214,A_1213,B_1212)
      | ~ r1_tarski(A_1214,k2_zfmisc_1(A_1213,B_1212)) ) ),
    inference(resolution,[status(thm)],[c_22,c_2422])).

tff(c_6723,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1009,c_6702])).

tff(c_6742,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_1184,c_6723])).

tff(c_6744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_4762,c_6742])).

tff(c_6746,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6754,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6746,c_8])).

tff(c_6745,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_6750,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6745,c_8])).

tff(c_6769,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6754,c_6750])).

tff(c_6778,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6769,c_64])).

tff(c_16,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6757,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6750,c_6750,c_16])).

tff(c_6840,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6769,c_6769,c_6757])).

tff(c_7053,plain,(
    ! [C_1242,A_1243,B_1244] :
      ( m1_subset_1(C_1242,k1_zfmisc_1(k2_zfmisc_1(A_1243,B_1244)))
      | ~ r2_hidden(C_1242,k1_funct_2(A_1243,B_1244)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_7064,plain,(
    ! [C_1245,A_1246] :
      ( m1_subset_1(C_1245,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_1245,k1_funct_2(A_1246,'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6840,c_7053])).

tff(c_7076,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6778,c_7064])).

tff(c_7081,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_7076,c_20])).

tff(c_6755,plain,(
    ! [A_7] :
      ( A_7 = '#skF_2'
      | ~ r1_tarski(A_7,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6750,c_6750,c_12])).

tff(c_6864,plain,(
    ! [A_7] :
      ( A_7 = '#skF_3'
      | ~ r1_tarski(A_7,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6769,c_6769,c_6755])).

tff(c_7085,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7081,c_6864])).

tff(c_6762,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6750,c_6750,c_36])).

tff(c_6789,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6769,c_6769,c_6762])).

tff(c_7112,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7085,c_7085,c_6789])).

tff(c_6776,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6769,c_145])).

tff(c_7109,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7085,c_6776])).

tff(c_7140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7112,c_7109])).

tff(c_7141,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_7834,plain,(
    ! [C_1283,A_1284,B_1285] :
      ( m1_subset_1(C_1283,k1_zfmisc_1(k2_zfmisc_1(A_1284,B_1285)))
      | ~ r2_hidden(C_1283,k1_funct_2(A_1284,B_1285)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_7965,plain,(
    ! [C_1296,A_1297,B_1298] :
      ( r1_tarski(C_1296,k2_zfmisc_1(A_1297,B_1298))
      | ~ r2_hidden(C_1296,k1_funct_2(A_1297,B_1298)) ) ),
    inference(resolution,[status(thm)],[c_7834,c_20])).

tff(c_8010,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_7965])).

tff(c_7887,plain,(
    ! [A_1290,B_1291] :
      ( r1_tarski(k2_relat_1(A_1290),k2_relat_1(B_1291))
      | ~ r1_tarski(A_1290,B_1291)
      | ~ v1_relat_1(B_1291)
      | ~ v1_relat_1(A_1290) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7893,plain,(
    ! [A_1290,B_15,A_14] :
      ( r1_tarski(k2_relat_1(A_1290),B_15)
      | ~ r1_tarski(A_1290,k2_zfmisc_1(A_14,B_15))
      | ~ v1_relat_1(k2_zfmisc_1(A_14,B_15))
      | ~ v1_relat_1(A_1290)
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7887])).

tff(c_13334,plain,(
    ! [A_3600,B_3601,A_3602] :
      ( r1_tarski(k2_relat_1(A_3600),B_3601)
      | ~ r1_tarski(A_3600,k2_zfmisc_1(A_3602,B_3601))
      | ~ v1_relat_1(A_3600)
      | k1_xboole_0 = B_3601
      | k1_xboole_0 = A_3602 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_7893])).

tff(c_13342,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8010,c_13334])).

tff(c_13355,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_13342])).

tff(c_13356,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_7141,c_13355])).

tff(c_13361,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_13356])).

tff(c_110,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_112,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_110])).

tff(c_7142,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_8044,plain,(
    ! [A_1301,B_1302] :
      ( r1_tarski(k1_relat_1(A_1301),k1_relat_1(B_1302))
      | ~ r1_tarski(A_1301,B_1302)
      | ~ v1_relat_1(B_1302)
      | ~ v1_relat_1(A_1301) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8053,plain,(
    ! [B_1302] :
      ( r1_tarski('#skF_2',k1_relat_1(B_1302))
      | ~ r1_tarski('#skF_4',B_1302)
      | ~ v1_relat_1(B_1302)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7142,c_8044])).

tff(c_8075,plain,(
    ! [B_1303] :
      ( r1_tarski('#skF_2',k1_relat_1(B_1303))
      | ~ r1_tarski('#skF_4',B_1303)
      | ~ v1_relat_1(B_1303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8053])).

tff(c_8084,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_4',k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_8075])).

tff(c_8090,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_8084])).

tff(c_10383,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8090])).

tff(c_13426,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13361,c_10383])).

tff(c_13455,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_2',B_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13361,c_13361,c_18])).

tff(c_13649,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13455,c_8010])).

tff(c_13651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13426,c_13649])).

tff(c_13652,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13356])).

tff(c_13752,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13652,c_6])).

tff(c_13754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7172,c_13752])).

tff(c_13755,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8090])).

tff(c_13764,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_13755,c_12])).

tff(c_13756,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8090])).

tff(c_13812,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13764,c_13756])).

tff(c_13979,plain,(
    ! [A_3619] :
      ( A_3619 = '#skF_2'
      | ~ r1_tarski(A_3619,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13764,c_13764,c_12])).

tff(c_13992,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13812,c_13979])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13797,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13764,c_10])).

tff(c_14003,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13992,c_13797])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_13798,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13764,c_13764,c_34])).

tff(c_14002,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13992,c_13992,c_13798])).

tff(c_14065,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14002,c_7141])).

tff(c_14068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14003,c_14065])).

tff(c_14070,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7170])).

tff(c_14078,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14070,c_8])).

tff(c_14069,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_7170])).

tff(c_14074,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14069,c_8])).

tff(c_14107,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14078,c_14074])).

tff(c_14117,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14107,c_64])).

tff(c_14083,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_2',B_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14074,c_14074,c_18])).

tff(c_14186,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14107,c_14107,c_14083])).

tff(c_14549,plain,(
    ! [C_3655,A_3656,B_3657] :
      ( m1_subset_1(C_3655,k1_zfmisc_1(k2_zfmisc_1(A_3656,B_3657)))
      | ~ r2_hidden(C_3655,k1_funct_2(A_3656,B_3657)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_14560,plain,(
    ! [C_3658,B_3659] :
      ( m1_subset_1(C_3658,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_3658,k1_funct_2('#skF_3',B_3659)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14186,c_14549])).

tff(c_14580,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14117,c_14560])).

tff(c_14585,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_14580,c_20])).

tff(c_14080,plain,(
    ! [A_7] :
      ( A_7 = '#skF_2'
      | ~ r1_tarski(A_7,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14074,c_14074,c_12])).

tff(c_14205,plain,(
    ! [A_7] :
      ( A_7 = '#skF_3'
      | ~ r1_tarski(A_7,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14107,c_14107,c_14080])).

tff(c_14589,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14585,c_14205])).

tff(c_14085,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14074,c_10])).

tff(c_14141,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14107,c_14085])).

tff(c_14616,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14589,c_14141])).

tff(c_14086,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14074,c_14074,c_34])).

tff(c_14136,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14107,c_14107,c_14086])).

tff(c_14617,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14589,c_14589,c_14136])).

tff(c_14624,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14589,c_7141])).

tff(c_14661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14616,c_14617,c_14624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.70/3.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.70/3.08  
% 8.70/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.70/3.08  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 8.70/3.08  
% 8.70/3.08  %Foreground sorts:
% 8.70/3.08  
% 8.70/3.08  
% 8.70/3.08  %Background operators:
% 8.70/3.08  
% 8.70/3.08  
% 8.70/3.08  %Foreground operators:
% 8.70/3.08  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 8.70/3.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.70/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.70/3.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.70/3.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.70/3.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.70/3.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.70/3.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.70/3.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.70/3.08  tff('#skF_2', type, '#skF_2': $i).
% 8.70/3.08  tff('#skF_3', type, '#skF_3': $i).
% 8.70/3.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.70/3.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.70/3.08  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 8.70/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.70/3.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.70/3.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.70/3.08  tff('#skF_4', type, '#skF_4': $i).
% 8.70/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.70/3.08  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 8.70/3.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.70/3.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.70/3.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.70/3.08  
% 9.01/3.10  tff(f_109, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 9.01/3.10  tff(f_130, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 9.01/3.10  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.01/3.10  tff(f_117, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 9.01/3.10  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.01/3.10  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.01/3.10  tff(f_66, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 9.01/3.10  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 9.01/3.10  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.01/3.10  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.01/3.10  tff(f_80, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 9.01/3.10  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.01/3.10  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.01/3.10  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.01/3.10  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.01/3.10  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.01/3.10  tff(c_7163, plain, (![A_1254, B_1255]: (v1_xboole_0(k1_funct_2(A_1254, B_1255)) | ~v1_xboole_0(B_1255) | v1_xboole_0(A_1254))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.01/3.10  tff(c_64, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.01/3.10  tff(c_116, plain, (![B_38, A_39]: (~r2_hidden(B_38, A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.01/3.10  tff(c_120, plain, (~v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_116])).
% 9.01/3.10  tff(c_7170, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_7163, c_120])).
% 9.01/3.10  tff(c_7172, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_7170])).
% 9.01/3.10  tff(c_62, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.01/3.10  tff(c_145, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_62])).
% 9.01/3.10  tff(c_151, plain, (![A_49, B_50]: (v1_xboole_0(k1_funct_2(A_49, B_50)) | ~v1_xboole_0(B_50) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.01/3.10  tff(c_158, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_151, c_120])).
% 9.01/3.10  tff(c_160, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_158])).
% 9.01/3.10  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.01/3.10  tff(c_833, plain, (![C_80, A_81, B_82]: (m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~r2_hidden(C_80, k1_funct_2(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.01/3.10  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.01/3.10  tff(c_964, plain, (![C_93, A_94, B_95]: (r1_tarski(C_93, k2_zfmisc_1(A_94, B_95)) | ~r2_hidden(C_93, k1_funct_2(A_94, B_95)))), inference(resolution, [status(thm)], [c_833, c_20])).
% 9.01/3.10  tff(c_1009, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_964])).
% 9.01/3.10  tff(c_24, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.01/3.10  tff(c_28, plain, (![A_14, B_15]: (k1_relat_1(k2_zfmisc_1(A_14, B_15))=A_14 | k1_xboole_0=B_15 | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.01/3.10  tff(c_879, plain, (![A_86, B_87]: (r1_tarski(k1_relat_1(A_86), k1_relat_1(B_87)) | ~r1_tarski(A_86, B_87) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.01/3.10  tff(c_885, plain, (![A_86, A_14, B_15]: (r1_tarski(k1_relat_1(A_86), A_14) | ~r1_tarski(A_86, k2_zfmisc_1(A_14, B_15)) | ~v1_relat_1(k2_zfmisc_1(A_14, B_15)) | ~v1_relat_1(A_86) | k1_xboole_0=B_15 | k1_xboole_0=A_14)), inference(superposition, [status(thm), theory('equality')], [c_28, c_879])).
% 9.01/3.10  tff(c_3988, plain, (![A_1162, A_1163, B_1164]: (r1_tarski(k1_relat_1(A_1162), A_1163) | ~r1_tarski(A_1162, k2_zfmisc_1(A_1163, B_1164)) | ~v1_relat_1(A_1162) | k1_xboole_0=B_1164 | k1_xboole_0=A_1163)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_885])).
% 9.01/3.10  tff(c_3996, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1009, c_3988])).
% 9.01/3.10  tff(c_4009, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3996])).
% 9.01/3.10  tff(c_4014, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4009])).
% 9.01/3.10  tff(c_18, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.01/3.10  tff(c_4105, plain, (![B_9]: (k2_zfmisc_1('#skF_2', B_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4014, c_4014, c_18])).
% 9.01/3.10  tff(c_4262, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4105, c_1009])).
% 9.01/3.10  tff(c_12, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.01/3.10  tff(c_4385, plain, (![A_1179]: (A_1179='#skF_2' | ~r1_tarski(A_1179, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4014, c_4014, c_12])).
% 9.01/3.10  tff(c_4393, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_4262, c_4385])).
% 9.01/3.10  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.01/3.10  tff(c_4109, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4014, c_4014, c_36])).
% 9.01/3.10  tff(c_4411, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4393, c_4393, c_4109])).
% 9.01/3.10  tff(c_4419, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4393, c_145])).
% 9.01/3.10  tff(c_4501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4411, c_4419])).
% 9.01/3.10  tff(c_4503, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4009])).
% 9.01/3.10  tff(c_26, plain, (![A_14, B_15]: (k2_relat_1(k2_zfmisc_1(A_14, B_15))=B_15 | k1_xboole_0=B_15 | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.01/3.10  tff(c_1108, plain, (![A_115, B_116]: (r1_tarski(k2_relat_1(A_115), k2_relat_1(B_116)) | ~r1_tarski(A_115, B_116) | ~v1_relat_1(B_116) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.01/3.10  tff(c_1114, plain, (![A_115, B_15, A_14]: (r1_tarski(k2_relat_1(A_115), B_15) | ~r1_tarski(A_115, k2_zfmisc_1(A_14, B_15)) | ~v1_relat_1(k2_zfmisc_1(A_14, B_15)) | ~v1_relat_1(A_115) | k1_xboole_0=B_15 | k1_xboole_0=A_14)), inference(superposition, [status(thm), theory('equality')], [c_26, c_1108])).
% 9.01/3.10  tff(c_4628, plain, (![A_1188, B_1189, A_1190]: (r1_tarski(k2_relat_1(A_1188), B_1189) | ~r1_tarski(A_1188, k2_zfmisc_1(A_1190, B_1189)) | ~v1_relat_1(A_1188) | k1_xboole_0=B_1189 | k1_xboole_0=A_1190)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1114])).
% 9.01/3.10  tff(c_4638, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1009, c_4628])).
% 9.01/3.10  tff(c_4652, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4638])).
% 9.01/3.10  tff(c_4653, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4503, c_4652])).
% 9.01/3.10  tff(c_4658, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4653])).
% 9.01/3.10  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.01/3.10  tff(c_4758, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4658, c_6])).
% 9.01/3.10  tff(c_4760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_4758])).
% 9.01/3.10  tff(c_4762, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4653])).
% 9.01/3.10  tff(c_303, plain, (![C_62, A_63, B_64]: (v1_funct_2(C_62, A_63, B_64) | ~r2_hidden(C_62, k1_funct_2(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.01/3.10  tff(c_321, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_303])).
% 9.01/3.10  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.01/3.10  tff(c_1010, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.01/3.10  tff(c_1170, plain, (![A_119, B_120, A_121]: (k1_relset_1(A_119, B_120, A_121)=k1_relat_1(A_121) | ~r1_tarski(A_121, k2_zfmisc_1(A_119, B_120)))), inference(resolution, [status(thm)], [c_22, c_1010])).
% 9.01/3.10  tff(c_1184, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1009, c_1170])).
% 9.01/3.10  tff(c_2422, plain, (![B_1100, A_1101, C_1102]: (k1_xboole_0=B_1100 | k1_relset_1(A_1101, B_1100, C_1102)=A_1101 | ~v1_funct_2(C_1102, A_1101, B_1100) | ~m1_subset_1(C_1102, k1_zfmisc_1(k2_zfmisc_1(A_1101, B_1100))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.01/3.10  tff(c_6702, plain, (![B_1212, A_1213, A_1214]: (k1_xboole_0=B_1212 | k1_relset_1(A_1213, B_1212, A_1214)=A_1213 | ~v1_funct_2(A_1214, A_1213, B_1212) | ~r1_tarski(A_1214, k2_zfmisc_1(A_1213, B_1212)))), inference(resolution, [status(thm)], [c_22, c_2422])).
% 9.01/3.10  tff(c_6723, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1009, c_6702])).
% 9.01/3.10  tff(c_6742, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_321, c_1184, c_6723])).
% 9.01/3.10  tff(c_6744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_4762, c_6742])).
% 9.01/3.10  tff(c_6746, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_158])).
% 9.01/3.10  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.01/3.10  tff(c_6754, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6746, c_8])).
% 9.01/3.10  tff(c_6745, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_158])).
% 9.01/3.10  tff(c_6750, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_6745, c_8])).
% 9.01/3.10  tff(c_6769, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6754, c_6750])).
% 9.01/3.10  tff(c_6778, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6769, c_64])).
% 9.01/3.10  tff(c_16, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.01/3.10  tff(c_6757, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6750, c_6750, c_16])).
% 9.01/3.10  tff(c_6840, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6769, c_6769, c_6757])).
% 9.01/3.10  tff(c_7053, plain, (![C_1242, A_1243, B_1244]: (m1_subset_1(C_1242, k1_zfmisc_1(k2_zfmisc_1(A_1243, B_1244))) | ~r2_hidden(C_1242, k1_funct_2(A_1243, B_1244)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.01/3.10  tff(c_7064, plain, (![C_1245, A_1246]: (m1_subset_1(C_1245, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_1245, k1_funct_2(A_1246, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6840, c_7053])).
% 9.01/3.10  tff(c_7076, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_6778, c_7064])).
% 9.01/3.10  tff(c_7081, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_7076, c_20])).
% 9.01/3.10  tff(c_6755, plain, (![A_7]: (A_7='#skF_2' | ~r1_tarski(A_7, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6750, c_6750, c_12])).
% 9.01/3.10  tff(c_6864, plain, (![A_7]: (A_7='#skF_3' | ~r1_tarski(A_7, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6769, c_6769, c_6755])).
% 9.01/3.10  tff(c_7085, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_7081, c_6864])).
% 9.01/3.10  tff(c_6762, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6750, c_6750, c_36])).
% 9.01/3.10  tff(c_6789, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6769, c_6769, c_6762])).
% 9.01/3.10  tff(c_7112, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7085, c_7085, c_6789])).
% 9.01/3.10  tff(c_6776, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6769, c_145])).
% 9.01/3.10  tff(c_7109, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7085, c_6776])).
% 9.01/3.10  tff(c_7140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7112, c_7109])).
% 9.01/3.10  tff(c_7141, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 9.01/3.10  tff(c_7834, plain, (![C_1283, A_1284, B_1285]: (m1_subset_1(C_1283, k1_zfmisc_1(k2_zfmisc_1(A_1284, B_1285))) | ~r2_hidden(C_1283, k1_funct_2(A_1284, B_1285)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.01/3.10  tff(c_7965, plain, (![C_1296, A_1297, B_1298]: (r1_tarski(C_1296, k2_zfmisc_1(A_1297, B_1298)) | ~r2_hidden(C_1296, k1_funct_2(A_1297, B_1298)))), inference(resolution, [status(thm)], [c_7834, c_20])).
% 9.01/3.10  tff(c_8010, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_7965])).
% 9.01/3.10  tff(c_7887, plain, (![A_1290, B_1291]: (r1_tarski(k2_relat_1(A_1290), k2_relat_1(B_1291)) | ~r1_tarski(A_1290, B_1291) | ~v1_relat_1(B_1291) | ~v1_relat_1(A_1290))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.01/3.10  tff(c_7893, plain, (![A_1290, B_15, A_14]: (r1_tarski(k2_relat_1(A_1290), B_15) | ~r1_tarski(A_1290, k2_zfmisc_1(A_14, B_15)) | ~v1_relat_1(k2_zfmisc_1(A_14, B_15)) | ~v1_relat_1(A_1290) | k1_xboole_0=B_15 | k1_xboole_0=A_14)), inference(superposition, [status(thm), theory('equality')], [c_26, c_7887])).
% 9.01/3.10  tff(c_13334, plain, (![A_3600, B_3601, A_3602]: (r1_tarski(k2_relat_1(A_3600), B_3601) | ~r1_tarski(A_3600, k2_zfmisc_1(A_3602, B_3601)) | ~v1_relat_1(A_3600) | k1_xboole_0=B_3601 | k1_xboole_0=A_3602)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_7893])).
% 9.01/3.10  tff(c_13342, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8010, c_13334])).
% 9.01/3.10  tff(c_13355, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_13342])).
% 9.01/3.10  tff(c_13356, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_7141, c_13355])).
% 9.01/3.10  tff(c_13361, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_13356])).
% 9.01/3.10  tff(c_110, plain, (![A_36, B_37]: (v1_relat_1(k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.01/3.10  tff(c_112, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_110])).
% 9.01/3.10  tff(c_7142, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 9.01/3.10  tff(c_8044, plain, (![A_1301, B_1302]: (r1_tarski(k1_relat_1(A_1301), k1_relat_1(B_1302)) | ~r1_tarski(A_1301, B_1302) | ~v1_relat_1(B_1302) | ~v1_relat_1(A_1301))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.01/3.10  tff(c_8053, plain, (![B_1302]: (r1_tarski('#skF_2', k1_relat_1(B_1302)) | ~r1_tarski('#skF_4', B_1302) | ~v1_relat_1(B_1302) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7142, c_8044])).
% 9.01/3.10  tff(c_8075, plain, (![B_1303]: (r1_tarski('#skF_2', k1_relat_1(B_1303)) | ~r1_tarski('#skF_4', B_1303) | ~v1_relat_1(B_1303))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8053])).
% 9.01/3.10  tff(c_8084, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_8075])).
% 9.01/3.10  tff(c_8090, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_8084])).
% 9.01/3.10  tff(c_10383, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8090])).
% 9.01/3.10  tff(c_13426, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13361, c_10383])).
% 9.01/3.10  tff(c_13455, plain, (![B_9]: (k2_zfmisc_1('#skF_2', B_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13361, c_13361, c_18])).
% 9.01/3.10  tff(c_13649, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13455, c_8010])).
% 9.01/3.10  tff(c_13651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13426, c_13649])).
% 9.01/3.10  tff(c_13652, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_13356])).
% 9.01/3.10  tff(c_13752, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13652, c_6])).
% 9.01/3.10  tff(c_13754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7172, c_13752])).
% 9.01/3.10  tff(c_13755, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8090])).
% 9.01/3.10  tff(c_13764, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_13755, c_12])).
% 9.01/3.10  tff(c_13756, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8090])).
% 9.01/3.10  tff(c_13812, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13764, c_13756])).
% 9.01/3.10  tff(c_13979, plain, (![A_3619]: (A_3619='#skF_2' | ~r1_tarski(A_3619, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13764, c_13764, c_12])).
% 9.01/3.10  tff(c_13992, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_13812, c_13979])).
% 9.01/3.10  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.01/3.10  tff(c_13797, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_13764, c_10])).
% 9.01/3.10  tff(c_14003, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_13992, c_13797])).
% 9.01/3.10  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.01/3.10  tff(c_13798, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13764, c_13764, c_34])).
% 9.01/3.10  tff(c_14002, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13992, c_13992, c_13798])).
% 9.01/3.10  tff(c_14065, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14002, c_7141])).
% 9.01/3.10  tff(c_14068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14003, c_14065])).
% 9.01/3.10  tff(c_14070, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_7170])).
% 9.01/3.10  tff(c_14078, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14070, c_8])).
% 9.01/3.10  tff(c_14069, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_7170])).
% 9.01/3.10  tff(c_14074, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_14069, c_8])).
% 9.01/3.10  tff(c_14107, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14078, c_14074])).
% 9.01/3.10  tff(c_14117, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14107, c_64])).
% 9.01/3.10  tff(c_14083, plain, (![B_9]: (k2_zfmisc_1('#skF_2', B_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14074, c_14074, c_18])).
% 9.01/3.10  tff(c_14186, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14107, c_14107, c_14083])).
% 9.01/3.10  tff(c_14549, plain, (![C_3655, A_3656, B_3657]: (m1_subset_1(C_3655, k1_zfmisc_1(k2_zfmisc_1(A_3656, B_3657))) | ~r2_hidden(C_3655, k1_funct_2(A_3656, B_3657)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.01/3.10  tff(c_14560, plain, (![C_3658, B_3659]: (m1_subset_1(C_3658, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_3658, k1_funct_2('#skF_3', B_3659)))), inference(superposition, [status(thm), theory('equality')], [c_14186, c_14549])).
% 9.01/3.10  tff(c_14580, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_14117, c_14560])).
% 9.01/3.10  tff(c_14585, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_14580, c_20])).
% 9.01/3.10  tff(c_14080, plain, (![A_7]: (A_7='#skF_2' | ~r1_tarski(A_7, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14074, c_14074, c_12])).
% 9.01/3.10  tff(c_14205, plain, (![A_7]: (A_7='#skF_3' | ~r1_tarski(A_7, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14107, c_14107, c_14080])).
% 9.01/3.10  tff(c_14589, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_14585, c_14205])).
% 9.01/3.10  tff(c_14085, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_14074, c_10])).
% 9.01/3.10  tff(c_14141, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_14107, c_14085])).
% 9.01/3.10  tff(c_14616, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_14589, c_14141])).
% 9.01/3.10  tff(c_14086, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14074, c_14074, c_34])).
% 9.01/3.10  tff(c_14136, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14107, c_14107, c_14086])).
% 9.01/3.10  tff(c_14617, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14589, c_14589, c_14136])).
% 9.01/3.10  tff(c_14624, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14589, c_7141])).
% 9.01/3.10  tff(c_14661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14616, c_14617, c_14624])).
% 9.01/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.01/3.10  
% 9.01/3.10  Inference rules
% 9.01/3.10  ----------------------
% 9.01/3.10  #Ref     : 0
% 9.01/3.10  #Sup     : 3219
% 9.01/3.10  #Fact    : 8
% 9.01/3.10  #Define  : 0
% 9.01/3.10  #Split   : 29
% 9.01/3.10  #Chain   : 0
% 9.01/3.10  #Close   : 0
% 9.01/3.10  
% 9.01/3.10  Ordering : KBO
% 9.01/3.10  
% 9.01/3.10  Simplification rules
% 9.01/3.10  ----------------------
% 9.01/3.10  #Subsume      : 725
% 9.01/3.10  #Demod        : 3506
% 9.01/3.10  #Tautology    : 1588
% 9.01/3.10  #SimpNegUnit  : 152
% 9.01/3.10  #BackRed      : 793
% 9.01/3.10  
% 9.01/3.10  #Partial instantiations: 522
% 9.01/3.10  #Strategies tried      : 1
% 9.01/3.10  
% 9.01/3.10  Timing (in seconds)
% 9.01/3.10  ----------------------
% 9.01/3.11  Preprocessing        : 0.34
% 9.01/3.11  Parsing              : 0.18
% 9.01/3.11  CNF conversion       : 0.02
% 9.01/3.11  Main loop            : 1.97
% 9.01/3.11  Inferencing          : 0.64
% 9.01/3.11  Reduction            : 0.62
% 9.01/3.11  Demodulation         : 0.43
% 9.01/3.11  BG Simplification    : 0.08
% 9.01/3.11  Subsumption          : 0.50
% 9.01/3.11  Abstraction          : 0.08
% 9.01/3.11  MUC search           : 0.00
% 9.01/3.11  Cooper               : 0.00
% 9.01/3.11  Total                : 2.37
% 9.01/3.11  Index Insertion      : 0.00
% 9.01/3.11  Index Deletion       : 0.00
% 9.01/3.11  Index Matching       : 0.00
% 9.01/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
