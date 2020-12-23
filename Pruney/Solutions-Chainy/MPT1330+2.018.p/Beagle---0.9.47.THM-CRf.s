%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:11 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :  151 (1259 expanded)
%              Number of leaves         :   46 ( 435 expanded)
%              Depth                    :   14
%              Number of atoms          :  205 (2909 expanded)
%              Number of equality atoms :   70 (1124 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_struct_0(B) = k1_xboole_0
                   => k2_struct_0(A) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1791,plain,(
    ! [A_198,B_199] :
      ( v1_xboole_0(k2_zfmisc_1(A_198,B_199))
      | ~ v1_xboole_0(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1796,plain,(
    ! [A_200,B_201] :
      ( k2_zfmisc_1(A_200,B_201) = k1_xboole_0
      | ~ v1_xboole_0(B_201) ) ),
    inference(resolution,[status(thm)],[c_1791,c_4])).

tff(c_1802,plain,(
    ! [A_200] : k2_zfmisc_1(A_200,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1796])).

tff(c_22,plain,(
    ! [A_14] : k9_relat_1(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_xboole_0(k2_zfmisc_1(A_3,B_4))
      | ~ v1_xboole_0(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,(
    ! [A_43,B_44] :
      ( v1_xboole_0(k2_zfmisc_1(A_43,B_44))
      | ~ v1_xboole_0(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_101,plain,(
    ! [A_48,B_49] :
      ( k2_zfmisc_1(A_48,B_49) = k1_xboole_0
      | ~ v1_xboole_0(B_49) ) ),
    inference(resolution,[status(thm)],[c_77,c_4])).

tff(c_451,plain,(
    ! [A_90,A_91,B_92] :
      ( k2_zfmisc_1(A_90,k2_zfmisc_1(A_91,B_92)) = k1_xboole_0
      | ~ v1_xboole_0(B_92) ) ),
    inference(resolution,[status(thm)],[c_8,c_101])).

tff(c_133,plain,(
    ! [A_53] : m1_subset_1(k6_relat_1(A_53),k1_zfmisc_1(k2_zfmisc_1(A_53,A_53))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_141,plain,(
    ! [A_53] : r1_tarski(k6_relat_1(A_53),k2_zfmisc_1(A_53,A_53)) ),
    inference(resolution,[status(thm)],[c_133,c_10])).

tff(c_500,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(k6_relat_1(k2_zfmisc_1(A_93,B_94)),k1_xboole_0)
      | ~ v1_xboole_0(B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_141])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_520,plain,(
    ! [A_95,B_96] :
      ( k6_relat_1(k2_zfmisc_1(A_95,B_96)) = k1_xboole_0
      | ~ v1_xboole_0(B_96) ) ),
    inference(resolution,[status(thm)],[c_500,c_6])).

tff(c_60,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_82,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_90,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_82])).

tff(c_58,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_89,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_82])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_122,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_89,c_52])).

tff(c_377,plain,(
    ! [A_84,B_85] :
      ( k9_relat_1(k6_relat_1(A_84),B_85) = B_85
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_394,plain,(
    k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_122,c_377])).

tff(c_532,plain,
    ( k9_relat_1(k1_xboole_0,'#skF_3') = '#skF_3'
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_394])).

tff(c_559,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_532])).

tff(c_568,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_559])).

tff(c_20,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_150,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_162,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_122,c_150])).

tff(c_172,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_162])).

tff(c_216,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_232,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_122,c_216])).

tff(c_735,plain,(
    ! [B_108,A_109] :
      ( k1_relat_1(B_108) = A_109
      | ~ v1_partfun1(B_108,A_109)
      | ~ v4_relat_1(B_108,A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_747,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_232,c_735])).

tff(c_760,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_747])).

tff(c_779,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_760])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_91,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_54])).

tff(c_127,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_91])).

tff(c_1216,plain,(
    ! [C_156,A_157,B_158] :
      ( v1_partfun1(C_156,A_157)
      | ~ v1_funct_2(C_156,A_157,B_158)
      | ~ v1_funct_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | v1_xboole_0(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1229,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_122,c_1216])).

tff(c_1237,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_127,c_1229])).

tff(c_1239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_568,c_779,c_1237])).

tff(c_1240,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_760])).

tff(c_48,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_175,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_89,c_48])).

tff(c_1245,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_1240,c_175])).

tff(c_1247,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_122])).

tff(c_1362,plain,(
    ! [A_163,B_164,C_165] :
      ( k1_relset_1(A_163,B_164,C_165) = k1_relat_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1379,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1247,c_1362])).

tff(c_1596,plain,(
    ! [A_186,B_187,C_188] :
      ( k8_relset_1(A_186,B_187,C_188,B_187) = k1_relset_1(A_186,B_187,C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1598,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1247,c_1596])).

tff(c_1609,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_1598])).

tff(c_1611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1245,c_1609])).

tff(c_1612,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_559])).

tff(c_50,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_76,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_1631,plain,(
    k2_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_76])).

tff(c_1613,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_559])).

tff(c_1744,plain,(
    ! [A_196] :
      ( A_196 = '#skF_3'
      | ~ v1_xboole_0(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_4])).

tff(c_1747,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1613,c_1744])).

tff(c_1757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1631,c_1747])).

tff(c_1758,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1768,plain,(
    ! [A_197] :
      ( u1_struct_0(A_197) = k2_struct_0(A_197)
      | ~ l1_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1774,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1768])).

tff(c_1778,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1758,c_1774])).

tff(c_1759,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1771,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1768])).

tff(c_1776,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_1771])).

tff(c_1784,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1776,c_52])).

tff(c_1785,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1778,c_1784])).

tff(c_1804,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1802,c_1785])).

tff(c_1824,plain,(
    ! [A_204,B_205] :
      ( r1_tarski(A_204,B_205)
      | ~ m1_subset_1(A_204,k1_zfmisc_1(B_205)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1835,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1804,c_1824])).

tff(c_1840,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1835,c_6])).

tff(c_1823,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1778,c_1776,c_1759,c_1758,c_48])).

tff(c_1843,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1840,c_1840,c_1840,c_1840,c_1823])).

tff(c_32,plain,(
    ! [A_23] : m1_subset_1(k6_relat_1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1889,plain,(
    ! [B_209,A_210] :
      ( v1_relat_1(B_209)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(A_210))
      | ~ v1_relat_1(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1895,plain,(
    ! [A_23] :
      ( v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k2_zfmisc_1(A_23,A_23)) ) ),
    inference(resolution,[status(thm)],[c_32,c_1889])).

tff(c_1899,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1895])).

tff(c_1805,plain,(
    ! [A_203] : k2_zfmisc_1(A_203,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1796])).

tff(c_1811,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1805,c_32])).

tff(c_1834,plain,(
    r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1811,c_1824])).

tff(c_1901,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1840,c_1840,c_1834])).

tff(c_1942,plain,(
    ! [A_214] :
      ( A_214 = '#skF_3'
      | ~ r1_tarski(A_214,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1840,c_1840,c_6])).

tff(c_1949,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1901,c_1942])).

tff(c_2150,plain,(
    ! [C_239,A_240,B_241] :
      ( v4_relat_1(C_239,A_240)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2173,plain,(
    ! [A_243] : v4_relat_1(k6_relat_1(A_243),A_243) ),
    inference(resolution,[status(thm)],[c_32,c_2150])).

tff(c_1967,plain,(
    ! [B_215,A_216] :
      ( r1_tarski(k1_relat_1(B_215),A_216)
      | ~ v4_relat_1(B_215,A_216)
      | ~ v1_relat_1(B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1853,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ r1_tarski(A_2,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1840,c_1840,c_6])).

tff(c_1972,plain,(
    ! [B_215] :
      ( k1_relat_1(B_215) = '#skF_3'
      | ~ v4_relat_1(B_215,'#skF_3')
      | ~ v1_relat_1(B_215) ) ),
    inference(resolution,[status(thm)],[c_1967,c_1853])).

tff(c_2177,plain,
    ( k1_relat_1(k6_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2173,c_1972])).

tff(c_2186,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_1949,c_2177])).

tff(c_2324,plain,(
    ! [A_256,B_257,C_258] :
      ( k1_relset_1(A_256,B_257,C_258) = k1_relat_1(C_258)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2339,plain,(
    ! [A_23] : k1_relset_1(A_23,A_23,k6_relat_1(A_23)) = k1_relat_1(k6_relat_1(A_23)) ),
    inference(resolution,[status(thm)],[c_32,c_2324])).

tff(c_2362,plain,(
    ! [A_263,B_264,C_265] :
      ( k8_relset_1(A_263,B_264,C_265,B_264) = k1_relset_1(A_263,B_264,C_265)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2373,plain,(
    ! [A_23] : k8_relset_1(A_23,A_23,k6_relat_1(A_23),A_23) = k1_relset_1(A_23,A_23,k6_relat_1(A_23)) ),
    inference(resolution,[status(thm)],[c_32,c_2362])).

tff(c_2627,plain,(
    ! [A_289] : k8_relset_1(A_289,A_289,k6_relat_1(A_289),A_289) = k1_relat_1(k6_relat_1(A_289)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2339,c_2373])).

tff(c_2639,plain,(
    k1_relat_1(k6_relat_1('#skF_3')) = k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1949,c_2627])).

tff(c_2642,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_1949,c_2639])).

tff(c_2644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1843,c_2642])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:18:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.70  
% 3.95/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.95/1.71  
% 3.95/1.71  %Foreground sorts:
% 3.95/1.71  
% 3.95/1.71  
% 3.95/1.71  %Background operators:
% 3.95/1.71  
% 3.95/1.71  
% 3.95/1.71  %Foreground operators:
% 3.95/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.95/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.71  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.95/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.71  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.95/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.95/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.95/1.71  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.95/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.95/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.95/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.95/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.71  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.95/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.95/1.71  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.95/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.95/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.71  
% 4.27/1.73  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.27/1.73  tff(f_38, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 4.27/1.73  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.27/1.73  tff(f_59, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 4.27/1.73  tff(f_75, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 4.27/1.73  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.27/1.73  tff(f_34, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.27/1.73  tff(f_126, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 4.27/1.73  tff(f_107, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.27/1.73  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 4.27/1.73  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.27/1.73  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.27/1.73  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.27/1.73  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.27/1.73  tff(f_95, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.27/1.73  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.27/1.73  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 4.27/1.73  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.27/1.73  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.27/1.73  tff(c_1791, plain, (![A_198, B_199]: (v1_xboole_0(k2_zfmisc_1(A_198, B_199)) | ~v1_xboole_0(B_199))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.27/1.73  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.27/1.73  tff(c_1796, plain, (![A_200, B_201]: (k2_zfmisc_1(A_200, B_201)=k1_xboole_0 | ~v1_xboole_0(B_201))), inference(resolution, [status(thm)], [c_1791, c_4])).
% 4.27/1.73  tff(c_1802, plain, (![A_200]: (k2_zfmisc_1(A_200, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_1796])).
% 4.27/1.73  tff(c_22, plain, (![A_14]: (k9_relat_1(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.27/1.73  tff(c_8, plain, (![A_3, B_4]: (v1_xboole_0(k2_zfmisc_1(A_3, B_4)) | ~v1_xboole_0(B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.27/1.73  tff(c_77, plain, (![A_43, B_44]: (v1_xboole_0(k2_zfmisc_1(A_43, B_44)) | ~v1_xboole_0(B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.27/1.73  tff(c_101, plain, (![A_48, B_49]: (k2_zfmisc_1(A_48, B_49)=k1_xboole_0 | ~v1_xboole_0(B_49))), inference(resolution, [status(thm)], [c_77, c_4])).
% 4.27/1.73  tff(c_451, plain, (![A_90, A_91, B_92]: (k2_zfmisc_1(A_90, k2_zfmisc_1(A_91, B_92))=k1_xboole_0 | ~v1_xboole_0(B_92))), inference(resolution, [status(thm)], [c_8, c_101])).
% 4.27/1.73  tff(c_133, plain, (![A_53]: (m1_subset_1(k6_relat_1(A_53), k1_zfmisc_1(k2_zfmisc_1(A_53, A_53))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.27/1.73  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.27/1.73  tff(c_141, plain, (![A_53]: (r1_tarski(k6_relat_1(A_53), k2_zfmisc_1(A_53, A_53)))), inference(resolution, [status(thm)], [c_133, c_10])).
% 4.27/1.73  tff(c_500, plain, (![A_93, B_94]: (r1_tarski(k6_relat_1(k2_zfmisc_1(A_93, B_94)), k1_xboole_0) | ~v1_xboole_0(B_94))), inference(superposition, [status(thm), theory('equality')], [c_451, c_141])).
% 4.27/1.73  tff(c_6, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.27/1.73  tff(c_520, plain, (![A_95, B_96]: (k6_relat_1(k2_zfmisc_1(A_95, B_96))=k1_xboole_0 | ~v1_xboole_0(B_96))), inference(resolution, [status(thm)], [c_500, c_6])).
% 4.27/1.73  tff(c_60, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.73  tff(c_82, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.27/1.73  tff(c_90, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_82])).
% 4.27/1.73  tff(c_58, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.73  tff(c_89, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_82])).
% 4.27/1.73  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.73  tff(c_122, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_89, c_52])).
% 4.27/1.73  tff(c_377, plain, (![A_84, B_85]: (k9_relat_1(k6_relat_1(A_84), B_85)=B_85 | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.27/1.73  tff(c_394, plain, (k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_122, c_377])).
% 4.27/1.73  tff(c_532, plain, (k9_relat_1(k1_xboole_0, '#skF_3')='#skF_3' | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_520, c_394])).
% 4.27/1.73  tff(c_559, plain, (k1_xboole_0='#skF_3' | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_532])).
% 4.27/1.73  tff(c_568, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_559])).
% 4.27/1.73  tff(c_20, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.27/1.73  tff(c_150, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.27/1.73  tff(c_162, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_122, c_150])).
% 4.27/1.73  tff(c_172, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_162])).
% 4.27/1.73  tff(c_216, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.27/1.73  tff(c_232, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_122, c_216])).
% 4.27/1.73  tff(c_735, plain, (![B_108, A_109]: (k1_relat_1(B_108)=A_109 | ~v1_partfun1(B_108, A_109) | ~v4_relat_1(B_108, A_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.27/1.73  tff(c_747, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_232, c_735])).
% 4.27/1.73  tff(c_760, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_747])).
% 4.27/1.73  tff(c_779, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_760])).
% 4.27/1.73  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.73  tff(c_54, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.73  tff(c_91, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_54])).
% 4.27/1.73  tff(c_127, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_91])).
% 4.27/1.73  tff(c_1216, plain, (![C_156, A_157, B_158]: (v1_partfun1(C_156, A_157) | ~v1_funct_2(C_156, A_157, B_158) | ~v1_funct_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | v1_xboole_0(B_158))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.27/1.73  tff(c_1229, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_122, c_1216])).
% 4.27/1.73  tff(c_1237, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_127, c_1229])).
% 4.27/1.73  tff(c_1239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_568, c_779, c_1237])).
% 4.27/1.73  tff(c_1240, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_760])).
% 4.27/1.73  tff(c_48, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.73  tff(c_175, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_89, c_48])).
% 4.27/1.73  tff(c_1245, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_1240, c_175])).
% 4.27/1.73  tff(c_1247, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_122])).
% 4.27/1.73  tff(c_1362, plain, (![A_163, B_164, C_165]: (k1_relset_1(A_163, B_164, C_165)=k1_relat_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.27/1.73  tff(c_1379, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1247, c_1362])).
% 4.27/1.73  tff(c_1596, plain, (![A_186, B_187, C_188]: (k8_relset_1(A_186, B_187, C_188, B_187)=k1_relset_1(A_186, B_187, C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.27/1.73  tff(c_1598, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_1247, c_1596])).
% 4.27/1.73  tff(c_1609, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1379, c_1598])).
% 4.27/1.73  tff(c_1611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1245, c_1609])).
% 4.27/1.73  tff(c_1612, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_559])).
% 4.27/1.73  tff(c_50, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.27/1.73  tff(c_76, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 4.27/1.73  tff(c_1631, plain, (k2_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_76])).
% 4.27/1.73  tff(c_1613, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_559])).
% 4.27/1.73  tff(c_1744, plain, (![A_196]: (A_196='#skF_3' | ~v1_xboole_0(A_196))), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_4])).
% 4.27/1.73  tff(c_1747, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_1613, c_1744])).
% 4.27/1.73  tff(c_1757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1631, c_1747])).
% 4.27/1.73  tff(c_1758, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 4.27/1.73  tff(c_1768, plain, (![A_197]: (u1_struct_0(A_197)=k2_struct_0(A_197) | ~l1_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.27/1.73  tff(c_1774, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_1768])).
% 4.27/1.73  tff(c_1778, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1758, c_1774])).
% 4.27/1.73  tff(c_1759, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 4.27/1.73  tff(c_1771, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_1768])).
% 4.27/1.73  tff(c_1776, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_1771])).
% 4.27/1.73  tff(c_1784, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1776, c_52])).
% 4.27/1.73  tff(c_1785, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1778, c_1784])).
% 4.27/1.73  tff(c_1804, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1802, c_1785])).
% 4.27/1.73  tff(c_1824, plain, (![A_204, B_205]: (r1_tarski(A_204, B_205) | ~m1_subset_1(A_204, k1_zfmisc_1(B_205)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.27/1.73  tff(c_1835, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_1804, c_1824])).
% 4.27/1.73  tff(c_1840, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1835, c_6])).
% 4.27/1.73  tff(c_1823, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1778, c_1776, c_1759, c_1758, c_48])).
% 4.27/1.73  tff(c_1843, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1840, c_1840, c_1840, c_1840, c_1823])).
% 4.27/1.73  tff(c_32, plain, (![A_23]: (m1_subset_1(k6_relat_1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.27/1.73  tff(c_1889, plain, (![B_209, A_210]: (v1_relat_1(B_209) | ~m1_subset_1(B_209, k1_zfmisc_1(A_210)) | ~v1_relat_1(A_210))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.27/1.73  tff(c_1895, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(k2_zfmisc_1(A_23, A_23)))), inference(resolution, [status(thm)], [c_32, c_1889])).
% 4.27/1.73  tff(c_1899, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1895])).
% 4.27/1.73  tff(c_1805, plain, (![A_203]: (k2_zfmisc_1(A_203, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_1796])).
% 4.27/1.73  tff(c_1811, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1805, c_32])).
% 4.27/1.73  tff(c_1834, plain, (r1_tarski(k6_relat_1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_1811, c_1824])).
% 4.27/1.73  tff(c_1901, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1840, c_1840, c_1834])).
% 4.27/1.73  tff(c_1942, plain, (![A_214]: (A_214='#skF_3' | ~r1_tarski(A_214, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1840, c_1840, c_6])).
% 4.27/1.73  tff(c_1949, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1901, c_1942])).
% 4.27/1.73  tff(c_2150, plain, (![C_239, A_240, B_241]: (v4_relat_1(C_239, A_240) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.27/1.73  tff(c_2173, plain, (![A_243]: (v4_relat_1(k6_relat_1(A_243), A_243))), inference(resolution, [status(thm)], [c_32, c_2150])).
% 4.27/1.73  tff(c_1967, plain, (![B_215, A_216]: (r1_tarski(k1_relat_1(B_215), A_216) | ~v4_relat_1(B_215, A_216) | ~v1_relat_1(B_215))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.27/1.73  tff(c_1853, plain, (![A_2]: (A_2='#skF_3' | ~r1_tarski(A_2, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1840, c_1840, c_6])).
% 4.27/1.73  tff(c_1972, plain, (![B_215]: (k1_relat_1(B_215)='#skF_3' | ~v4_relat_1(B_215, '#skF_3') | ~v1_relat_1(B_215))), inference(resolution, [status(thm)], [c_1967, c_1853])).
% 4.27/1.73  tff(c_2177, plain, (k1_relat_1(k6_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1(k6_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2173, c_1972])).
% 4.27/1.73  tff(c_2186, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_1949, c_2177])).
% 4.27/1.73  tff(c_2324, plain, (![A_256, B_257, C_258]: (k1_relset_1(A_256, B_257, C_258)=k1_relat_1(C_258) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.27/1.73  tff(c_2339, plain, (![A_23]: (k1_relset_1(A_23, A_23, k6_relat_1(A_23))=k1_relat_1(k6_relat_1(A_23)))), inference(resolution, [status(thm)], [c_32, c_2324])).
% 4.27/1.73  tff(c_2362, plain, (![A_263, B_264, C_265]: (k8_relset_1(A_263, B_264, C_265, B_264)=k1_relset_1(A_263, B_264, C_265) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.27/1.73  tff(c_2373, plain, (![A_23]: (k8_relset_1(A_23, A_23, k6_relat_1(A_23), A_23)=k1_relset_1(A_23, A_23, k6_relat_1(A_23)))), inference(resolution, [status(thm)], [c_32, c_2362])).
% 4.27/1.73  tff(c_2627, plain, (![A_289]: (k8_relset_1(A_289, A_289, k6_relat_1(A_289), A_289)=k1_relat_1(k6_relat_1(A_289)))), inference(demodulation, [status(thm), theory('equality')], [c_2339, c_2373])).
% 4.27/1.73  tff(c_2639, plain, (k1_relat_1(k6_relat_1('#skF_3'))=k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1949, c_2627])).
% 4.27/1.73  tff(c_2642, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_1949, c_2639])).
% 4.27/1.73  tff(c_2644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1843, c_2642])).
% 4.27/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.73  
% 4.27/1.73  Inference rules
% 4.27/1.73  ----------------------
% 4.27/1.73  #Ref     : 0
% 4.27/1.73  #Sup     : 566
% 4.27/1.73  #Fact    : 0
% 4.27/1.73  #Define  : 0
% 4.27/1.73  #Split   : 7
% 4.27/1.73  #Chain   : 0
% 4.27/1.73  #Close   : 0
% 4.27/1.73  
% 4.27/1.73  Ordering : KBO
% 4.27/1.73  
% 4.27/1.73  Simplification rules
% 4.27/1.73  ----------------------
% 4.27/1.73  #Subsume      : 76
% 4.27/1.73  #Demod        : 522
% 4.27/1.73  #Tautology    : 324
% 4.27/1.73  #SimpNegUnit  : 29
% 4.27/1.73  #BackRed      : 66
% 4.27/1.73  
% 4.27/1.73  #Partial instantiations: 0
% 4.27/1.73  #Strategies tried      : 1
% 4.27/1.73  
% 4.27/1.73  Timing (in seconds)
% 4.27/1.73  ----------------------
% 4.27/1.73  Preprocessing        : 0.33
% 4.27/1.73  Parsing              : 0.17
% 4.27/1.73  CNF conversion       : 0.02
% 4.27/1.73  Main loop            : 0.63
% 4.27/1.73  Inferencing          : 0.23
% 4.27/1.73  Reduction            : 0.22
% 4.27/1.73  Demodulation         : 0.16
% 4.27/1.73  BG Simplification    : 0.03
% 4.27/1.73  Subsumption          : 0.09
% 4.27/1.73  Abstraction          : 0.03
% 4.27/1.73  MUC search           : 0.00
% 4.27/1.73  Cooper               : 0.00
% 4.27/1.73  Total                : 1.01
% 4.27/1.73  Index Insertion      : 0.00
% 4.27/1.73  Index Deletion       : 0.00
% 4.27/1.73  Index Matching       : 0.00
% 4.27/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
