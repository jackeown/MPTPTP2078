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
% DateTime   : Thu Dec  3 10:14:28 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 375 expanded)
%              Number of leaves         :   50 ( 143 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 ( 770 expanded)
%              Number of equality atoms :   96 ( 361 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_156,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_126,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).

tff(f_63,axiom,(
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

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_144,axiom,(
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

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_209,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_217,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_209])).

tff(c_88,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_40,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_226,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_217,c_40])).

tff(c_228,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_356,plain,(
    ! [C_90,A_91,B_92] :
      ( v4_relat_1(C_90,A_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_364,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_84,c_356])).

tff(c_327,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(k1_relat_1(B_85),A_86)
      | ~ v4_relat_1(B_85,A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_718,plain,(
    ! [B_145,B_146] :
      ( k1_tarski(B_145) = k1_relat_1(B_146)
      | k1_relat_1(B_146) = k1_xboole_0
      | ~ v4_relat_1(B_146,k1_tarski(B_145))
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_327,c_16])).

tff(c_733,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_364,c_718])).

tff(c_747,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_733])).

tff(c_748,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_747])).

tff(c_915,plain,(
    ! [B_161,A_162] :
      ( k1_tarski(k1_funct_1(B_161,A_162)) = k2_relat_1(B_161)
      | k1_tarski(A_162) != k1_relat_1(B_161)
      | ~ v1_funct_1(B_161)
      | ~ v1_relat_1(B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_563,plain,(
    ! [A_122,B_123,C_124] :
      ( k2_relset_1(A_122,B_123,C_124) = k2_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_571,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_563])).

tff(c_80,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_581,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_80])).

tff(c_924,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_581])).

tff(c_938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_88,c_748,c_924])).

tff(c_939,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_940,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_960,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_940])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_950,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_939,c_34])).

tff(c_1530,plain,(
    ! [B_254,A_255] :
      ( k1_tarski(k1_funct_1(B_254,A_255)) = k2_relat_1(B_254)
      | k1_tarski(A_255) != k1_relat_1(B_254)
      | ~ v1_funct_1(B_254)
      | ~ v1_relat_1(B_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_949,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_22])).

tff(c_1350,plain,(
    ! [A_221,B_222,C_223] :
      ( k2_relset_1(A_221,B_222,C_223) = k2_relat_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1354,plain,(
    ! [A_221,B_222] : k2_relset_1(A_221,B_222,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_949,c_1350])).

tff(c_1356,plain,(
    ! [A_221,B_222] : k2_relset_1(A_221,B_222,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_1354])).

tff(c_1357,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1356,c_80])).

tff(c_1539,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1530,c_1357])).

tff(c_1551,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_88,c_960,c_950,c_1539])).

tff(c_1039,plain,(
    ! [A_170] :
      ( k10_relat_1(A_170,k2_relat_1(A_170)) = k1_relat_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1048,plain,
    ( k10_relat_1('#skF_4','#skF_4') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_1039])).

tff(c_1052,plain,(
    k10_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_960,c_1048])).

tff(c_1481,plain,(
    ! [A_243,B_244,C_245,D_246] :
      ( k8_relset_1(A_243,B_244,C_245,D_246) = k10_relat_1(C_245,D_246)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1485,plain,(
    ! [A_243,B_244,D_246] : k8_relset_1(A_243,B_244,'#skF_4',D_246) = k10_relat_1('#skF_4',D_246) ),
    inference(resolution,[status(thm)],[c_949,c_1481])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_952,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_8])).

tff(c_62,plain,(
    ! [A_44] : k1_relat_1('#skF_1'(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_66,plain,(
    ! [A_44] : v1_relat_1('#skF_1'(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_140,plain,(
    ! [A_64] :
      ( k1_relat_1(A_64) != k1_xboole_0
      | k1_xboole_0 = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_143,plain,(
    ! [A_44] :
      ( k1_relat_1('#skF_1'(A_44)) != k1_xboole_0
      | '#skF_1'(A_44) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_140])).

tff(c_147,plain,(
    ! [A_65] :
      ( k1_xboole_0 != A_65
      | '#skF_1'(A_65) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_143])).

tff(c_157,plain,(
    ! [A_65] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_66])).

tff(c_173,plain,(
    ! [A_65] : k1_xboole_0 != A_65 ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_34])).

tff(c_181,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_202,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k9_relat_1(B_67,A_68),k2_relat_1(B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_205,plain,(
    ! [A_68] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_68),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_202])).

tff(c_207,plain,(
    ! [A_68] : r1_tarski(k9_relat_1(k1_xboole_0,A_68),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_205])).

tff(c_1018,plain,(
    ! [A_168] : r1_tarski(k9_relat_1('#skF_4',A_168),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_939,c_207])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1020,plain,(
    ! [A_168] :
      ( k9_relat_1('#skF_4',A_168) = '#skF_4'
      | ~ r1_tarski('#skF_4',k9_relat_1('#skF_4',A_168)) ) ),
    inference(resolution,[status(thm)],[c_1018,c_2])).

tff(c_1023,plain,(
    ! [A_168] : k9_relat_1('#skF_4',A_168) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_1020])).

tff(c_1417,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( k7_relset_1(A_232,B_233,C_234,D_235) = k9_relat_1(C_234,D_235)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1420,plain,(
    ! [A_232,B_233,D_235] : k7_relset_1(A_232,B_233,'#skF_4',D_235) = k9_relat_1('#skF_4',D_235) ),
    inference(resolution,[status(thm)],[c_949,c_1417])).

tff(c_1422,plain,(
    ! [A_232,B_233,D_235] : k7_relset_1(A_232,B_233,'#skF_4',D_235) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_1420])).

tff(c_1771,plain,(
    ! [B_281,A_282,C_283] :
      ( k8_relset_1(B_281,A_282,C_283,k7_relset_1(B_281,A_282,C_283,B_281)) = k1_relset_1(B_281,A_282,C_283)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(B_281,A_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1774,plain,(
    ! [B_281,A_282] : k8_relset_1(B_281,A_282,'#skF_4',k7_relset_1(B_281,A_282,'#skF_4',B_281)) = k1_relset_1(B_281,A_282,'#skF_4') ),
    inference(resolution,[status(thm)],[c_949,c_1771])).

tff(c_1776,plain,(
    ! [B_281,A_282] : k1_relset_1(B_281,A_282,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_1485,c_1422,c_1774])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_953,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_82])).

tff(c_86,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_78,plain,(
    ! [B_51,A_50,C_52] :
      ( k1_xboole_0 = B_51
      | k1_relset_1(A_50,B_51,C_52) = A_50
      | ~ v1_funct_2(C_52,A_50,B_51)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1579,plain,(
    ! [B_263,A_264,C_265] :
      ( B_263 = '#skF_4'
      | k1_relset_1(A_264,B_263,C_265) = A_264
      | ~ v1_funct_2(C_265,A_264,B_263)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_264,B_263))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_78])).

tff(c_1590,plain,(
    ! [B_267,A_268] :
      ( B_267 = '#skF_4'
      | k1_relset_1(A_268,B_267,'#skF_4') = A_268
      | ~ v1_funct_2('#skF_4',A_268,B_267) ) ),
    inference(resolution,[status(thm)],[c_949,c_1579])).

tff(c_1599,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k1_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_1590])).

tff(c_1605,plain,(
    k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_953,c_1599])).

tff(c_1777,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1776,c_1605])).

tff(c_1783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1551,c_1777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.62  
% 3.67/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.67/1.63  
% 3.67/1.63  %Foreground sorts:
% 3.67/1.63  
% 3.67/1.63  
% 3.67/1.63  %Background operators:
% 3.67/1.63  
% 3.67/1.63  
% 3.67/1.63  %Foreground operators:
% 3.67/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.67/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.67/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.67/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.67/1.63  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.67/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.67/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.67/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.67/1.63  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.67/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.67/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.67/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.67/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.67/1.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.67/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.67/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.67/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.67/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.67/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.67/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.67/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.67/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.67/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.67/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.67/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.67/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.67/1.63  
% 4.00/1.65  tff(f_156, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 4.00/1.65  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.00/1.65  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.00/1.65  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.00/1.65  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.00/1.65  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.00/1.65  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.00/1.65  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.00/1.65  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.00/1.65  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.00/1.65  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.00/1.65  tff(f_108, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.00/1.65  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.00/1.65  tff(f_126, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_tarski(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e15_31__wellord2)).
% 4.00/1.65  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 4.00/1.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.00/1.65  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.00/1.65  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 4.00/1.65  tff(f_144, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.00/1.65  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.00/1.65  tff(c_209, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.00/1.65  tff(c_217, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_209])).
% 4.00/1.65  tff(c_88, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.00/1.65  tff(c_40, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.00/1.65  tff(c_226, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_217, c_40])).
% 4.00/1.65  tff(c_228, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_226])).
% 4.00/1.65  tff(c_356, plain, (![C_90, A_91, B_92]: (v4_relat_1(C_90, A_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.00/1.65  tff(c_364, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_84, c_356])).
% 4.00/1.65  tff(c_327, plain, (![B_85, A_86]: (r1_tarski(k1_relat_1(B_85), A_86) | ~v4_relat_1(B_85, A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.00/1.65  tff(c_16, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.00/1.65  tff(c_718, plain, (![B_145, B_146]: (k1_tarski(B_145)=k1_relat_1(B_146) | k1_relat_1(B_146)=k1_xboole_0 | ~v4_relat_1(B_146, k1_tarski(B_145)) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_327, c_16])).
% 4.00/1.65  tff(c_733, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_364, c_718])).
% 4.00/1.65  tff(c_747, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_217, c_733])).
% 4.00/1.65  tff(c_748, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_228, c_747])).
% 4.00/1.65  tff(c_915, plain, (![B_161, A_162]: (k1_tarski(k1_funct_1(B_161, A_162))=k2_relat_1(B_161) | k1_tarski(A_162)!=k1_relat_1(B_161) | ~v1_funct_1(B_161) | ~v1_relat_1(B_161))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.00/1.65  tff(c_563, plain, (![A_122, B_123, C_124]: (k2_relset_1(A_122, B_123, C_124)=k2_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.00/1.65  tff(c_571, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_563])).
% 4.00/1.65  tff(c_80, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.00/1.65  tff(c_581, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_571, c_80])).
% 4.00/1.65  tff(c_924, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_915, c_581])).
% 4.00/1.65  tff(c_938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_88, c_748, c_924])).
% 4.00/1.65  tff(c_939, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_226])).
% 4.00/1.65  tff(c_940, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_226])).
% 4.00/1.65  tff(c_960, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_939, c_940])).
% 4.00/1.65  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.00/1.65  tff(c_950, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_939, c_939, c_34])).
% 4.00/1.65  tff(c_1530, plain, (![B_254, A_255]: (k1_tarski(k1_funct_1(B_254, A_255))=k2_relat_1(B_254) | k1_tarski(A_255)!=k1_relat_1(B_254) | ~v1_funct_1(B_254) | ~v1_relat_1(B_254))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.00/1.65  tff(c_22, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.00/1.65  tff(c_949, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_939, c_22])).
% 4.00/1.65  tff(c_1350, plain, (![A_221, B_222, C_223]: (k2_relset_1(A_221, B_222, C_223)=k2_relat_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.00/1.65  tff(c_1354, plain, (![A_221, B_222]: (k2_relset_1(A_221, B_222, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_949, c_1350])).
% 4.00/1.65  tff(c_1356, plain, (![A_221, B_222]: (k2_relset_1(A_221, B_222, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_950, c_1354])).
% 4.00/1.65  tff(c_1357, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1356, c_80])).
% 4.00/1.65  tff(c_1539, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1530, c_1357])).
% 4.00/1.65  tff(c_1551, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_217, c_88, c_960, c_950, c_1539])).
% 4.00/1.65  tff(c_1039, plain, (![A_170]: (k10_relat_1(A_170, k2_relat_1(A_170))=k1_relat_1(A_170) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.00/1.65  tff(c_1048, plain, (k10_relat_1('#skF_4', '#skF_4')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_950, c_1039])).
% 4.00/1.65  tff(c_1052, plain, (k10_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_217, c_960, c_1048])).
% 4.00/1.65  tff(c_1481, plain, (![A_243, B_244, C_245, D_246]: (k8_relset_1(A_243, B_244, C_245, D_246)=k10_relat_1(C_245, D_246) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.00/1.65  tff(c_1485, plain, (![A_243, B_244, D_246]: (k8_relset_1(A_243, B_244, '#skF_4', D_246)=k10_relat_1('#skF_4', D_246))), inference(resolution, [status(thm)], [c_949, c_1481])).
% 4.00/1.65  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.00/1.65  tff(c_952, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_939, c_8])).
% 4.00/1.65  tff(c_62, plain, (![A_44]: (k1_relat_1('#skF_1'(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.00/1.65  tff(c_66, plain, (![A_44]: (v1_relat_1('#skF_1'(A_44)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.00/1.65  tff(c_140, plain, (![A_64]: (k1_relat_1(A_64)!=k1_xboole_0 | k1_xboole_0=A_64 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.00/1.65  tff(c_143, plain, (![A_44]: (k1_relat_1('#skF_1'(A_44))!=k1_xboole_0 | '#skF_1'(A_44)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_140])).
% 4.00/1.65  tff(c_147, plain, (![A_65]: (k1_xboole_0!=A_65 | '#skF_1'(A_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_143])).
% 4.00/1.65  tff(c_157, plain, (![A_65]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_65)), inference(superposition, [status(thm), theory('equality')], [c_147, c_66])).
% 4.00/1.65  tff(c_173, plain, (![A_65]: (k1_xboole_0!=A_65)), inference(splitLeft, [status(thm)], [c_157])).
% 4.00/1.65  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_34])).
% 4.00/1.65  tff(c_181, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_157])).
% 4.00/1.65  tff(c_202, plain, (![B_67, A_68]: (r1_tarski(k9_relat_1(B_67, A_68), k2_relat_1(B_67)) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.00/1.65  tff(c_205, plain, (![A_68]: (r1_tarski(k9_relat_1(k1_xboole_0, A_68), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_202])).
% 4.00/1.65  tff(c_207, plain, (![A_68]: (r1_tarski(k9_relat_1(k1_xboole_0, A_68), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_205])).
% 4.00/1.65  tff(c_1018, plain, (![A_168]: (r1_tarski(k9_relat_1('#skF_4', A_168), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_939, c_939, c_207])).
% 4.00/1.65  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.00/1.65  tff(c_1020, plain, (![A_168]: (k9_relat_1('#skF_4', A_168)='#skF_4' | ~r1_tarski('#skF_4', k9_relat_1('#skF_4', A_168)))), inference(resolution, [status(thm)], [c_1018, c_2])).
% 4.00/1.65  tff(c_1023, plain, (![A_168]: (k9_relat_1('#skF_4', A_168)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_952, c_1020])).
% 4.00/1.65  tff(c_1417, plain, (![A_232, B_233, C_234, D_235]: (k7_relset_1(A_232, B_233, C_234, D_235)=k9_relat_1(C_234, D_235) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.00/1.65  tff(c_1420, plain, (![A_232, B_233, D_235]: (k7_relset_1(A_232, B_233, '#skF_4', D_235)=k9_relat_1('#skF_4', D_235))), inference(resolution, [status(thm)], [c_949, c_1417])).
% 4.00/1.65  tff(c_1422, plain, (![A_232, B_233, D_235]: (k7_relset_1(A_232, B_233, '#skF_4', D_235)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_1420])).
% 4.00/1.65  tff(c_1771, plain, (![B_281, A_282, C_283]: (k8_relset_1(B_281, A_282, C_283, k7_relset_1(B_281, A_282, C_283, B_281))=k1_relset_1(B_281, A_282, C_283) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(B_281, A_282))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.00/1.65  tff(c_1774, plain, (![B_281, A_282]: (k8_relset_1(B_281, A_282, '#skF_4', k7_relset_1(B_281, A_282, '#skF_4', B_281))=k1_relset_1(B_281, A_282, '#skF_4'))), inference(resolution, [status(thm)], [c_949, c_1771])).
% 4.00/1.65  tff(c_1776, plain, (![B_281, A_282]: (k1_relset_1(B_281, A_282, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_1485, c_1422, c_1774])).
% 4.00/1.65  tff(c_82, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.00/1.65  tff(c_953, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_939, c_82])).
% 4.00/1.65  tff(c_86, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.00/1.65  tff(c_78, plain, (![B_51, A_50, C_52]: (k1_xboole_0=B_51 | k1_relset_1(A_50, B_51, C_52)=A_50 | ~v1_funct_2(C_52, A_50, B_51) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.00/1.65  tff(c_1579, plain, (![B_263, A_264, C_265]: (B_263='#skF_4' | k1_relset_1(A_264, B_263, C_265)=A_264 | ~v1_funct_2(C_265, A_264, B_263) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_264, B_263))))), inference(demodulation, [status(thm), theory('equality')], [c_939, c_78])).
% 4.00/1.65  tff(c_1590, plain, (![B_267, A_268]: (B_267='#skF_4' | k1_relset_1(A_268, B_267, '#skF_4')=A_268 | ~v1_funct_2('#skF_4', A_268, B_267))), inference(resolution, [status(thm)], [c_949, c_1579])).
% 4.00/1.65  tff(c_1599, plain, ('#skF_3'='#skF_4' | k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k1_tarski('#skF_2')), inference(resolution, [status(thm)], [c_86, c_1590])).
% 4.00/1.65  tff(c_1605, plain, (k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_953, c_1599])).
% 4.00/1.65  tff(c_1777, plain, (k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1776, c_1605])).
% 4.00/1.65  tff(c_1783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1551, c_1777])).
% 4.00/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.65  
% 4.00/1.65  Inference rules
% 4.00/1.65  ----------------------
% 4.00/1.65  #Ref     : 2
% 4.00/1.65  #Sup     : 319
% 4.00/1.65  #Fact    : 0
% 4.00/1.65  #Define  : 0
% 4.00/1.65  #Split   : 5
% 4.00/1.65  #Chain   : 0
% 4.00/1.65  #Close   : 0
% 4.00/1.65  
% 4.00/1.65  Ordering : KBO
% 4.00/1.65  
% 4.00/1.65  Simplification rules
% 4.00/1.65  ----------------------
% 4.00/1.65  #Subsume      : 58
% 4.00/1.65  #Demod        : 321
% 4.00/1.65  #Tautology    : 193
% 4.00/1.65  #SimpNegUnit  : 20
% 4.00/1.65  #BackRed      : 34
% 4.00/1.65  
% 4.00/1.65  #Partial instantiations: 0
% 4.00/1.65  #Strategies tried      : 1
% 4.00/1.65  
% 4.00/1.65  Timing (in seconds)
% 4.00/1.65  ----------------------
% 4.00/1.65  Preprocessing        : 0.37
% 4.00/1.65  Parsing              : 0.20
% 4.00/1.65  CNF conversion       : 0.03
% 4.00/1.65  Main loop            : 0.50
% 4.00/1.65  Inferencing          : 0.17
% 4.00/1.65  Reduction            : 0.17
% 4.00/1.65  Demodulation         : 0.12
% 4.00/1.65  BG Simplification    : 0.03
% 4.00/1.65  Subsumption          : 0.09
% 4.00/1.65  Abstraction          : 0.02
% 4.00/1.65  MUC search           : 0.00
% 4.00/1.65  Cooper               : 0.00
% 4.00/1.65  Total                : 0.91
% 4.00/1.65  Index Insertion      : 0.00
% 4.00/1.65  Index Deletion       : 0.00
% 4.00/1.65  Index Matching       : 0.00
% 4.00/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
