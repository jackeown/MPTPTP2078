%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:44 EST 2020

% Result     : Theorem 7.98s
% Output     : CNFRefutation 8.34s
% Verified   : 
% Statistics : Number of formulae       :  370 (4323 expanded)
%              Number of leaves         :   44 (1412 expanded)
%              Depth                    :   17
%              Number of atoms          :  626 (10287 expanded)
%              Number of equality atoms :  230 (2413 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6014,plain,(
    ! [C_599,A_600,B_601] :
      ( v1_relat_1(C_599)
      | ~ m1_subset_1(C_599,k1_zfmisc_1(k2_zfmisc_1(A_600,B_601))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6035,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_6014])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_74,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6468,plain,(
    ! [A_666,B_667,C_668] :
      ( k2_relset_1(A_666,B_667,C_668) = k2_relat_1(C_668)
      | ~ m1_subset_1(C_668,k1_zfmisc_1(k2_zfmisc_1(A_666,B_667))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6478,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_6468])).

tff(c_6492,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6478])).

tff(c_46,plain,(
    ! [A_22] :
      ( k1_relat_1(k2_funct_1(A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_342,plain,(
    ! [C_78,B_79,A_80] :
      ( ~ v1_xboole_0(C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_352,plain,(
    ! [A_81,A_82] :
      ( ~ v1_xboole_0(A_81)
      | ~ r2_hidden(A_82,A_81) ) ),
    inference(resolution,[status(thm)],[c_83,c_342])).

tff(c_356,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_352])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [A_21] :
      ( v1_funct_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_72,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_158,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_161,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_158])).

tff(c_164,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_161])).

tff(c_202,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_209,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_202])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_209])).

tff(c_223,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_225,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_229,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_225])).

tff(c_274,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_291,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_274])).

tff(c_653,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_relset_1(A_134,B_135,C_136) = k2_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_660,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_653])).

tff(c_673,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_660])).

tff(c_38,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) = k1_xboole_0
      | k1_relat_1(A_20) != k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_299,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_291,c_38])).

tff(c_377,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_36,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) = k1_xboole_0
      | k2_relat_1(A_20) != k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_300,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_291,c_36])).

tff(c_382,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_377,c_300])).

tff(c_675,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_382])).

tff(c_80,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_593,plain,(
    ! [A_124,B_125,C_126] :
      ( k1_relset_1(A_124,B_125,C_126) = k1_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_612,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_593])).

tff(c_1147,plain,(
    ! [B_192,A_193,C_194] :
      ( k1_xboole_0 = B_192
      | k1_relset_1(A_193,B_192,C_194) = A_193
      | ~ v1_funct_2(C_194,A_193,B_192)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_193,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1160,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1147])).

tff(c_1179,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_612,c_1160])).

tff(c_1180,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_675,c_1179])).

tff(c_44,plain,(
    ! [A_22] :
      ( k2_relat_1(k2_funct_1(A_22)) = k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_541,plain,(
    ! [A_114] :
      ( k1_relat_1(k2_funct_1(A_114)) = k2_relat_1(A_114)
      | ~ v2_funct_1(A_114)
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k10_relat_1(B_18,A_17),k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1884,plain,(
    ! [A_245,A_246] :
      ( r1_tarski(k10_relat_1(k2_funct_1(A_245),A_246),k2_relat_1(A_245))
      | ~ v1_relat_1(k2_funct_1(A_245))
      | ~ v2_funct_1(A_245)
      | ~ v1_funct_1(A_245)
      | ~ v1_relat_1(A_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_32])).

tff(c_1901,plain,(
    ! [A_246] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_4'),A_246),'#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_1884])).

tff(c_1918,plain,(
    ! [A_246] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_4'),A_246),'#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_76,c_1901])).

tff(c_1921,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1918])).

tff(c_1924,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1921])).

tff(c_1928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_1924])).

tff(c_1930,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1918])).

tff(c_224,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_19] :
      ( k10_relat_1(A_19,k2_relat_1(A_19)) = k1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1955,plain,(
    ! [A_250] : r1_tarski(k10_relat_1(k2_funct_1('#skF_4'),A_250),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1918])).

tff(c_1970,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1('#skF_4')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1955])).

tff(c_1977,plain,(
    r1_tarski(k1_relat_1(k2_funct_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1930,c_1970])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1996,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_1977,c_10])).

tff(c_2078,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1996])).

tff(c_2081,plain,
    ( ~ r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2078])).

tff(c_2087,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_76,c_14,c_673,c_2081])).

tff(c_2088,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1996])).

tff(c_775,plain,(
    ! [A_144] :
      ( m1_subset_1(A_144,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_144),k2_relat_1(A_144))))
      | ~ v1_funct_1(A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_806,plain,(
    ! [A_144] :
      ( r1_tarski(A_144,k2_zfmisc_1(k1_relat_1(A_144),k2_relat_1(A_144)))
      | ~ v1_funct_1(A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_775,c_26])).

tff(c_2154,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2088,c_806])).

tff(c_2191,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1930,c_224,c_2154])).

tff(c_2282,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2191])).

tff(c_2303,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_76,c_1180,c_2282])).

tff(c_2305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_2303])).

tff(c_2306,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_2768,plain,(
    ! [A_298,B_299,C_300] :
      ( k2_relset_1(A_298,B_299,C_300) = k2_relat_1(C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2775,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_2768])).

tff(c_2788,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2306,c_2775])).

tff(c_2307,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_2320,plain,(
    ! [A_17] :
      ( r1_tarski(k10_relat_1('#skF_4',A_17),k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2307,c_32])).

tff(c_2324,plain,(
    ! [A_17] : r1_tarski(k10_relat_1('#skF_4',A_17),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_2320])).

tff(c_357,plain,(
    ! [A_83,B_84] :
      ( ~ v1_xboole_0(A_83)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_352])).

tff(c_2400,plain,(
    ! [B_265,A_266] :
      ( B_265 = A_266
      | ~ r1_tarski(B_265,A_266)
      | ~ v1_xboole_0(A_266) ) ),
    inference(resolution,[status(thm)],[c_357,c_10])).

tff(c_2403,plain,(
    ! [A_17] :
      ( k10_relat_1('#skF_4',A_17) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2324,c_2400])).

tff(c_2418,plain,(
    ! [A_17] : k10_relat_1('#skF_4',A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2403])).

tff(c_2480,plain,(
    ! [B_272,A_273,A_274] :
      ( ~ v1_xboole_0(B_272)
      | ~ r2_hidden(A_273,A_274)
      | ~ r1_tarski(A_274,B_272) ) ),
    inference(resolution,[status(thm)],[c_28,c_342])).

tff(c_2484,plain,(
    ! [B_275,A_276,B_277] :
      ( ~ v1_xboole_0(B_275)
      | ~ r1_tarski(A_276,B_275)
      | r1_tarski(A_276,B_277) ) ),
    inference(resolution,[status(thm)],[c_6,c_2480])).

tff(c_2560,plain,(
    ! [B_283,A_284,B_285] :
      ( ~ v1_xboole_0(k1_relat_1(B_283))
      | r1_tarski(k10_relat_1(B_283,A_284),B_285)
      | ~ v1_relat_1(B_283) ) ),
    inference(resolution,[status(thm)],[c_32,c_2484])).

tff(c_2578,plain,(
    ! [B_285] :
      ( ~ v1_xboole_0(k1_relat_1('#skF_4'))
      | r1_tarski(k1_xboole_0,B_285)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2418,c_2560])).

tff(c_2588,plain,(
    ! [B_285] : r1_tarski(k1_xboole_0,B_285) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_8,c_2307,c_2578])).

tff(c_2795,plain,(
    ! [B_285] : r1_tarski('#skF_3',B_285) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2788,c_2588])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2813,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2788,c_2788,c_18])).

tff(c_131,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_142,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_131])).

tff(c_256,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_261,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_256])).

tff(c_2465,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_2919,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2813,c_2465])).

tff(c_2925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2795,c_2919])).

tff(c_2926,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_350,plain,(
    ! [A_80] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_80,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_342])).

tff(c_370,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_2928,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2926,c_370])).

tff(c_3357,plain,(
    ! [A_348,B_349,C_350] :
      ( k2_relset_1(A_348,B_349,C_350) = k2_relat_1(C_350)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_348,B_349))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3387,plain,(
    ! [C_351] :
      ( k2_relset_1('#skF_2','#skF_3',C_351) = k2_relat_1(C_351)
      | ~ m1_subset_1(C_351,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2926,c_3357])).

tff(c_3395,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_83,c_3387])).

tff(c_3398,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2306,c_3395])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2942,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2926,c_16])).

tff(c_2972,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2942])).

tff(c_3412,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3398,c_2972])).

tff(c_3606,plain,(
    ! [A_357] : k2_zfmisc_1(A_357,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3398,c_3398,c_18])).

tff(c_3616,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3606,c_2926])).

tff(c_3633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3412,c_3616])).

tff(c_3635,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2942])).

tff(c_3666,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_8])).

tff(c_3669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2928,c_3666])).

tff(c_3672,plain,(
    ! [A_359] : ~ r2_hidden(A_359,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_3679,plain,(
    ! [B_360] : r1_tarski('#skF_4',B_360) ),
    inference(resolution,[status(thm)],[c_6,c_3672])).

tff(c_3700,plain,(
    ! [B_362] :
      ( B_362 = '#skF_4'
      | ~ r1_tarski(B_362,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3679,c_10])).

tff(c_3718,plain,(
    ! [A_363] :
      ( A_363 = '#skF_4'
      | ~ v1_xboole_0(A_363) ) ),
    inference(resolution,[status(thm)],[c_356,c_3700])).

tff(c_3726,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_3718])).

tff(c_3734,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_3726,c_20])).

tff(c_3735,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_3726,c_18])).

tff(c_3671,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_3725,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3671,c_3718])).

tff(c_5162,plain,(
    ! [B_524,A_525] :
      ( B_524 = '#skF_4'
      | A_525 = '#skF_4'
      | k2_zfmisc_1(A_525,B_524) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_3726,c_3726,c_16])).

tff(c_5176,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3725,c_5162])).

tff(c_5177,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5176])).

tff(c_5180,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5177,c_225])).

tff(c_5185,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3735,c_5180])).

tff(c_3736,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_8])).

tff(c_3801,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_3726,c_299])).

tff(c_3802,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3801])).

tff(c_3834,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_3726,c_300])).

tff(c_3835,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3802,c_3834])).

tff(c_4782,plain,(
    ! [A_488,B_489,C_490] :
      ( k2_relset_1(A_488,B_489,C_490) = k2_relat_1(C_490)
      | ~ m1_subset_1(C_490,k1_zfmisc_1(k2_zfmisc_1(A_488,B_489))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4827,plain,(
    ! [A_495,B_496] : k2_relset_1(A_495,B_496,k2_zfmisc_1(A_495,B_496)) = k2_relat_1(k2_zfmisc_1(A_495,B_496)) ),
    inference(resolution,[status(thm)],[c_83,c_4782])).

tff(c_4839,plain,(
    ! [A_8] : k2_relat_1(k2_zfmisc_1(A_8,'#skF_4')) = k2_relset_1(A_8,'#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3735,c_4827])).

tff(c_4876,plain,(
    ! [A_500] : k2_relset_1(A_500,'#skF_4','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3735,c_4839])).

tff(c_4093,plain,(
    ! [A_401,B_402,C_403] :
      ( k1_relset_1(A_401,B_402,C_403) = k1_relat_1(C_403)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4126,plain,(
    ! [A_405,B_406] : k1_relset_1(A_405,B_406,k2_zfmisc_1(A_405,B_406)) = k1_relat_1(k2_zfmisc_1(A_405,B_406)) ),
    inference(resolution,[status(thm)],[c_83,c_4093])).

tff(c_4135,plain,(
    ! [B_9] : k1_relat_1(k2_zfmisc_1('#skF_4',B_9)) = k1_relset_1('#skF_4',B_9,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3734,c_4126])).

tff(c_4141,plain,(
    ! [B_9] : k1_relset_1('#skF_4',B_9,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3734,c_4135])).

tff(c_3966,plain,(
    ! [B_390,A_391] :
      ( B_390 = '#skF_4'
      | A_391 = '#skF_4'
      | k2_zfmisc_1(A_391,B_390) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_3726,c_3726,c_16])).

tff(c_3980,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3725,c_3966])).

tff(c_3981,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3980])).

tff(c_3986,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3981,c_80])).

tff(c_62,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1(k1_xboole_0,B_33,C_34) = k1_xboole_0
      | ~ v1_funct_2(C_34,k1_xboole_0,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_84,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1(k1_xboole_0,B_33,C_34) = k1_xboole_0
      | ~ v1_funct_2(C_34,k1_xboole_0,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_4452,plain,(
    ! [B_444,C_445] :
      ( k1_relset_1('#skF_4',B_444,C_445) = '#skF_4'
      | ~ v1_funct_2(C_445,'#skF_4',B_444)
      | ~ m1_subset_1(C_445,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_3726,c_3726,c_3726,c_84])).

tff(c_4454,plain,
    ( k1_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3986,c_4452])).

tff(c_4460,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_4141,c_4454])).

tff(c_4462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3802,c_4460])).

tff(c_4463,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3980])).

tff(c_4468,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4463,c_4463,c_74])).

tff(c_4883,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4876,c_4468])).

tff(c_4894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3835,c_4883])).

tff(c_4895,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3801])).

tff(c_5116,plain,(
    ! [B_517,A_518,A_519] :
      ( ~ v1_xboole_0(B_517)
      | ~ r2_hidden(A_518,A_519)
      | ~ r1_tarski(A_519,B_517) ) ),
    inference(resolution,[status(thm)],[c_28,c_342])).

tff(c_5148,plain,(
    ! [B_521,A_522,B_523] :
      ( ~ v1_xboole_0(B_521)
      | ~ r1_tarski(A_522,B_521)
      | r1_tarski(A_522,B_523) ) ),
    inference(resolution,[status(thm)],[c_6,c_5116])).

tff(c_5448,plain,(
    ! [B_551,A_552,B_553] :
      ( ~ v1_xboole_0(k1_relat_1(B_551))
      | r1_tarski(k10_relat_1(B_551,A_552),B_553)
      | ~ v1_relat_1(B_551) ) ),
    inference(resolution,[status(thm)],[c_32,c_5148])).

tff(c_3688,plain,(
    ! [B_360] :
      ( B_360 = '#skF_4'
      | ~ r1_tarski(B_360,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3679,c_10])).

tff(c_5503,plain,(
    ! [B_558,A_559] :
      ( k10_relat_1(B_558,A_559) = '#skF_4'
      | ~ v1_xboole_0(k1_relat_1(B_558))
      | ~ v1_relat_1(B_558) ) ),
    inference(resolution,[status(thm)],[c_5448,c_3688])).

tff(c_5517,plain,(
    ! [A_562,A_563] :
      ( k10_relat_1(k2_funct_1(A_562),A_563) = '#skF_4'
      | ~ v1_xboole_0(k2_relat_1(A_562))
      | ~ v1_relat_1(k2_funct_1(A_562))
      | ~ v2_funct_1(A_562)
      | ~ v1_funct_1(A_562)
      | ~ v1_relat_1(A_562) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_5503])).

tff(c_5523,plain,(
    ! [A_563] :
      ( k10_relat_1(k2_funct_1('#skF_4'),A_563) = '#skF_4'
      | ~ v1_xboole_0('#skF_4')
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4895,c_5517])).

tff(c_5527,plain,(
    ! [A_563] :
      ( k10_relat_1(k2_funct_1('#skF_4'),A_563) = '#skF_4'
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_76,c_3736,c_5523])).

tff(c_5528,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5527])).

tff(c_5531,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_5528])).

tff(c_5535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_5531])).

tff(c_5537,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5527])).

tff(c_5546,plain,(
    ! [A_564] : k10_relat_1(k2_funct_1('#skF_4'),A_564) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5527])).

tff(c_5558,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5546,c_34])).

tff(c_5571,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5537,c_5558])).

tff(c_66,plain,(
    ! [A_35] :
      ( m1_subset_1(A_35,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_35),k2_relat_1(A_35))))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5584,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5571,c_66])).

tff(c_5606,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5537,c_224,c_3734,c_5584])).

tff(c_5608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5185,c_5606])).

tff(c_5609,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5176])).

tff(c_5627,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5609,c_225])).

tff(c_5632,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3734,c_5627])).

tff(c_5858,plain,(
    ! [B_587,A_588,B_589] :
      ( ~ v1_xboole_0(k1_relat_1(B_587))
      | r1_tarski(k10_relat_1(B_587,A_588),B_589)
      | ~ v1_relat_1(B_587) ) ),
    inference(resolution,[status(thm)],[c_32,c_5148])).

tff(c_5913,plain,(
    ! [B_594,A_595] :
      ( k10_relat_1(B_594,A_595) = '#skF_4'
      | ~ v1_xboole_0(k1_relat_1(B_594))
      | ~ v1_relat_1(B_594) ) ),
    inference(resolution,[status(thm)],[c_5858,c_3688])).

tff(c_5920,plain,(
    ! [A_596,A_597] :
      ( k10_relat_1(k2_funct_1(A_596),A_597) = '#skF_4'
      | ~ v1_xboole_0(k2_relat_1(A_596))
      | ~ v1_relat_1(k2_funct_1(A_596))
      | ~ v2_funct_1(A_596)
      | ~ v1_funct_1(A_596)
      | ~ v1_relat_1(A_596) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_5913])).

tff(c_5926,plain,(
    ! [A_597] :
      ( k10_relat_1(k2_funct_1('#skF_4'),A_597) = '#skF_4'
      | ~ v1_xboole_0('#skF_4')
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4895,c_5920])).

tff(c_5930,plain,(
    ! [A_597] :
      ( k10_relat_1(k2_funct_1('#skF_4'),A_597) = '#skF_4'
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_76,c_3736,c_5926])).

tff(c_5931,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5930])).

tff(c_5934,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_5931])).

tff(c_5938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_82,c_5934])).

tff(c_5940,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5930])).

tff(c_5949,plain,(
    ! [A_598] : k10_relat_1(k2_funct_1('#skF_4'),A_598) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5930])).

tff(c_5961,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5949,c_34])).

tff(c_5974,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5940,c_5961])).

tff(c_5985,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5974,c_66])).

tff(c_6005,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5940,c_224,c_3734,c_5985])).

tff(c_6007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5632,c_6005])).

tff(c_6008,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_6009,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_6426,plain,(
    ! [A_661,B_662,C_663] :
      ( k1_relset_1(A_661,B_662,C_663) = k1_relat_1(C_663)
      | ~ m1_subset_1(C_663,k1_zfmisc_1(k2_zfmisc_1(A_661,B_662))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6447,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6009,c_6426])).

tff(c_6972,plain,(
    ! [B_726,C_727,A_728] :
      ( k1_xboole_0 = B_726
      | v1_funct_2(C_727,A_728,B_726)
      | k1_relset_1(A_728,B_726,C_727) != A_728
      | ~ m1_subset_1(C_727,k1_zfmisc_1(k2_zfmisc_1(A_728,B_726))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6981,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_6009,c_6972])).

tff(c_7005,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6447,c_6981])).

tff(c_7006,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6008,c_7005])).

tff(c_7014,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7006])).

tff(c_7017,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_7014])).

tff(c_7020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6035,c_82,c_76,c_6492,c_7017])).

tff(c_7021,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7006])).

tff(c_6055,plain,(
    ! [A_605] :
      ( k2_relat_1(A_605) = k1_xboole_0
      | k1_relat_1(A_605) != k1_xboole_0
      | ~ v1_relat_1(A_605) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6074,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6035,c_6055])).

tff(c_6083,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6074])).

tff(c_7046,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7021,c_6083])).

tff(c_6119,plain,(
    ! [A_612] :
      ( k1_relat_1(A_612) = k1_xboole_0
      | k2_relat_1(A_612) != k1_xboole_0
      | ~ v1_relat_1(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6131,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6035,c_6119])).

tff(c_6142,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_6083,c_6131])).

tff(c_6494,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6492,c_6142])).

tff(c_7036,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7021,c_6494])).

tff(c_6449,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_6426])).

tff(c_64,plain,(
    ! [B_33,A_32,C_34] :
      ( k1_xboole_0 = B_33
      | k1_relset_1(A_32,B_33,C_34) = A_32
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_7078,plain,(
    ! [B_729,A_730,C_731] :
      ( B_729 = '#skF_2'
      | k1_relset_1(A_730,B_729,C_731) = A_730
      | ~ v1_funct_2(C_731,A_730,B_729)
      | ~ m1_subset_1(C_731,k1_zfmisc_1(k2_zfmisc_1(A_730,B_729))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7021,c_64])).

tff(c_7094,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_7078])).

tff(c_7109,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6449,c_7094])).

tff(c_7111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7046,c_7036,c_7109])).

tff(c_7112,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6074])).

tff(c_7113,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6074])).

tff(c_10077,plain,(
    ! [A_965] :
      ( m1_subset_1(A_965,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_965),k2_relat_1(A_965))))
      | ~ v1_funct_1(A_965)
      | ~ v1_relat_1(A_965) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_10109,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4'))))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7113,c_10077])).

tff(c_10127,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6035,c_82,c_20,c_7112,c_10109])).

tff(c_10170,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10127,c_26])).

tff(c_9252,plain,(
    ! [C_907,B_908,A_909] :
      ( ~ v1_xboole_0(C_907)
      | ~ m1_subset_1(B_908,k1_zfmisc_1(C_907))
      | ~ r2_hidden(A_909,B_908) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_9265,plain,(
    ! [A_910,A_911] :
      ( ~ v1_xboole_0(A_910)
      | ~ r2_hidden(A_911,A_910) ) ),
    inference(resolution,[status(thm)],[c_83,c_9252])).

tff(c_9270,plain,(
    ! [A_912,B_913] :
      ( ~ v1_xboole_0(A_912)
      | r1_tarski(A_912,B_913) ) ),
    inference(resolution,[status(thm)],[c_6,c_9265])).

tff(c_9285,plain,(
    ! [B_913,A_912] :
      ( B_913 = A_912
      | ~ r1_tarski(B_913,A_912)
      | ~ v1_xboole_0(A_912) ) ),
    inference(resolution,[status(thm)],[c_9270,c_10])).

tff(c_10181,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10170,c_9285])).

tff(c_10192,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10181])).

tff(c_10226,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10192,c_8])).

tff(c_10225,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10192,c_10192,c_18])).

tff(c_10217,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10192,c_7112])).

tff(c_10236,plain,(
    ! [A_968,B_969,C_970] :
      ( k2_relset_1(A_968,B_969,C_970) = k2_relat_1(C_970)
      | ~ m1_subset_1(C_970,k1_zfmisc_1(k2_zfmisc_1(A_968,B_969))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_10249,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_10236])).

tff(c_10258,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10249])).

tff(c_10310,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10217,c_10258])).

tff(c_9263,plain,(
    ! [A_909] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_909,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_9252])).

tff(c_9326,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9263])).

tff(c_10332,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10310,c_9326])).

tff(c_10545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10226,c_10225,c_10332])).

tff(c_10547,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9263])).

tff(c_9222,plain,(
    ! [B_902,A_903] :
      ( B_902 = A_903
      | ~ r1_tarski(B_902,A_903)
      | ~ r1_tarski(A_903,B_902) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_9242,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_9222])).

tff(c_9251,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_9242])).

tff(c_9284,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_9270,c_9251])).

tff(c_10602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10547,c_9284])).

tff(c_10603,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9242])).

tff(c_10618,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_10603,c_16])).

tff(c_10643,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10618])).

tff(c_11077,plain,(
    ! [A_1028] :
      ( m1_subset_1(A_1028,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1028),k2_relat_1(A_1028))))
      | ~ v1_funct_1(A_1028)
      | ~ v1_relat_1(A_1028) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_11112,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4'))))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7113,c_11077])).

tff(c_11131,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6035,c_82,c_20,c_7112,c_11112])).

tff(c_11151,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11131,c_26])).

tff(c_10644,plain,(
    ! [C_986,B_987,A_988] :
      ( ~ v1_xboole_0(C_986)
      | ~ m1_subset_1(B_987,k1_zfmisc_1(C_986))
      | ~ r2_hidden(A_988,B_987) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10654,plain,(
    ! [A_989,A_990] :
      ( ~ v1_xboole_0(A_989)
      | ~ r2_hidden(A_990,A_989) ) ),
    inference(resolution,[status(thm)],[c_83,c_10644])).

tff(c_10691,plain,(
    ! [A_992,B_993] :
      ( ~ v1_xboole_0(A_992)
      | r1_tarski(A_992,B_993) ) ),
    inference(resolution,[status(thm)],[c_6,c_10654])).

tff(c_10707,plain,(
    ! [B_993,A_992] :
      ( B_993 = A_992
      | ~ r1_tarski(B_993,A_992)
      | ~ v1_xboole_0(A_992) ) ),
    inference(resolution,[status(thm)],[c_10691,c_10])).

tff(c_11164,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11151,c_10707])).

tff(c_11177,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11164])).

tff(c_11179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10643,c_11177])).

tff(c_11181,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10618])).

tff(c_11720,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11181,c_7113])).

tff(c_11728,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11181,c_11181,c_20])).

tff(c_12425,plain,(
    ! [A_1109,B_1110,C_1111] :
      ( k1_relset_1(A_1109,B_1110,C_1111) = k1_relat_1(C_1111)
      | ~ m1_subset_1(C_1111,k1_zfmisc_1(k2_zfmisc_1(A_1109,B_1110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12453,plain,(
    ! [A_1114,B_1115] : k1_relset_1(A_1114,B_1115,k2_zfmisc_1(A_1114,B_1115)) = k1_relat_1(k2_zfmisc_1(A_1114,B_1115)) ),
    inference(resolution,[status(thm)],[c_83,c_12425])).

tff(c_12462,plain,(
    ! [B_9] : k1_relat_1(k2_zfmisc_1('#skF_4',B_9)) = k1_relset_1('#skF_4',B_9,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11728,c_12453])).

tff(c_12468,plain,(
    ! [B_9] : k1_relset_1('#skF_4',B_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11720,c_11728,c_12462])).

tff(c_58,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_85,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_58])).

tff(c_12540,plain,(
    ! [C_1124,B_1125] :
      ( v1_funct_2(C_1124,'#skF_4',B_1125)
      | k1_relset_1('#skF_4',B_1125,C_1124) != '#skF_4'
      | ~ m1_subset_1(C_1124,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11181,c_11181,c_11181,c_11181,c_85])).

tff(c_12546,plain,(
    ! [B_1125] :
      ( v1_funct_2('#skF_4','#skF_4',B_1125)
      | k1_relset_1('#skF_4',B_1125,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_83,c_12540])).

tff(c_12550,plain,(
    ! [B_1125] : v1_funct_2('#skF_4','#skF_4',B_1125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12468,c_12546])).

tff(c_11180,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10618])).

tff(c_11878,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11181,c_11181,c_11180])).

tff(c_11879,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11878])).

tff(c_11205,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11181,c_8])).

tff(c_11231,plain,(
    ! [C_1030,B_1031,A_1032] :
      ( ~ v1_xboole_0(C_1030)
      | ~ m1_subset_1(B_1031,k1_zfmisc_1(C_1030))
      | ~ r2_hidden(A_1032,B_1031) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_11603,plain,(
    ! [A_1047,A_1048] :
      ( ~ v1_xboole_0(A_1047)
      | ~ r2_hidden(A_1048,A_1047) ) ),
    inference(resolution,[status(thm)],[c_83,c_11231])).

tff(c_11607,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_11603])).

tff(c_11204,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11181,c_11181,c_18])).

tff(c_11421,plain,(
    ! [A_1039,A_1040] :
      ( ~ v1_xboole_0(A_1039)
      | ~ r2_hidden(A_1040,A_1039) ) ),
    inference(resolution,[status(thm)],[c_83,c_11231])).

tff(c_11425,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_11421])).

tff(c_11203,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11181,c_11181,c_20])).

tff(c_11351,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11181,c_11181,c_11180])).

tff(c_11352,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11351])).

tff(c_6013,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6009,c_26])).

tff(c_9241,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4')
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6013,c_9222])).

tff(c_11182,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_9241])).

tff(c_11521,plain,(
    ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11203,c_11352,c_11182])).

tff(c_11524,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_11425,c_11521])).

tff(c_11528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11205,c_11524])).

tff(c_11529,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11351])).

tff(c_11698,plain,(
    ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11204,c_11529,c_11182])).

tff(c_11701,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_11607,c_11698])).

tff(c_11705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11205,c_11701])).

tff(c_11706,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_9241])).

tff(c_11955,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11728,c_11879,c_11706])).

tff(c_11883,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11879,c_6008])).

tff(c_12071,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11955,c_11883])).

tff(c_12554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12550,c_12071])).

tff(c_12556,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11878])).

tff(c_54,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_87,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_54])).

tff(c_89,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_87])).

tff(c_12818,plain,(
    ! [A_1141] :
      ( v1_funct_2('#skF_4',A_1141,'#skF_4')
      | A_1141 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11181,c_11181,c_11181,c_89])).

tff(c_11729,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11181,c_11181,c_18])).

tff(c_12555,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11878])).

tff(c_12628,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11729,c_12555,c_11706])).

tff(c_12560,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12555,c_6008])).

tff(c_12776,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12628,c_12560])).

tff(c_12823,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12818,c_12776])).

tff(c_12831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12556,c_12823])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.98/2.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.31/2.94  
% 8.31/2.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.31/2.94  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.31/2.94  
% 8.31/2.94  %Foreground sorts:
% 8.31/2.94  
% 8.31/2.94  
% 8.31/2.94  %Background operators:
% 8.31/2.94  
% 8.31/2.94  
% 8.31/2.94  %Foreground operators:
% 8.31/2.94  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.31/2.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.31/2.94  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.31/2.94  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.31/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.31/2.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.31/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.31/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.31/2.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.31/2.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.31/2.94  tff('#skF_2', type, '#skF_2': $i).
% 8.31/2.94  tff('#skF_3', type, '#skF_3': $i).
% 8.31/2.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.31/2.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.31/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.31/2.95  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.31/2.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.31/2.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.31/2.95  tff('#skF_4', type, '#skF_4': $i).
% 8.31/2.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.31/2.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.31/2.95  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.31/2.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.31/2.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.31/2.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.31/2.95  
% 8.34/2.98  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.34/2.98  tff(f_149, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.34/2.98  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.34/2.98  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.34/2.98  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.34/2.98  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 8.34/2.98  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.34/2.98  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 8.34/2.98  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.34/2.98  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 8.34/2.98  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.34/2.98  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.34/2.98  tff(f_74, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 8.34/2.98  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.34/2.98  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.34/2.98  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 8.34/2.98  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.34/2.98  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 8.34/2.98  tff(f_132, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 8.34/2.98  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.34/2.98  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.34/2.98  tff(c_6014, plain, (![C_599, A_600, B_601]: (v1_relat_1(C_599) | ~m1_subset_1(C_599, k1_zfmisc_1(k2_zfmisc_1(A_600, B_601))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.34/2.98  tff(c_6035, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_6014])).
% 8.34/2.98  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.34/2.98  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.34/2.98  tff(c_76, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.34/2.98  tff(c_74, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.34/2.98  tff(c_6468, plain, (![A_666, B_667, C_668]: (k2_relset_1(A_666, B_667, C_668)=k2_relat_1(C_668) | ~m1_subset_1(C_668, k1_zfmisc_1(k2_zfmisc_1(A_666, B_667))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.34/2.98  tff(c_6478, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_6468])).
% 8.34/2.98  tff(c_6492, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6478])).
% 8.34/2.99  tff(c_46, plain, (![A_22]: (k1_relat_1(k2_funct_1(A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.34/2.99  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.34/2.99  tff(c_22, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.34/2.99  tff(c_24, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.34/2.99  tff(c_83, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 8.34/2.99  tff(c_342, plain, (![C_78, B_79, A_80]: (~v1_xboole_0(C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.34/2.99  tff(c_352, plain, (![A_81, A_82]: (~v1_xboole_0(A_81) | ~r2_hidden(A_82, A_81))), inference(resolution, [status(thm)], [c_83, c_342])).
% 8.34/2.99  tff(c_356, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_352])).
% 8.34/2.99  tff(c_28, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.34/2.99  tff(c_40, plain, (![A_21]: (v1_funct_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.34/2.99  tff(c_72, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.34/2.99  tff(c_158, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_72])).
% 8.34/2.99  tff(c_161, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_158])).
% 8.34/2.99  tff(c_164, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_161])).
% 8.34/2.99  tff(c_202, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.34/2.99  tff(c_209, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_202])).
% 8.34/2.99  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_209])).
% 8.34/2.99  tff(c_223, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_72])).
% 8.34/2.99  tff(c_225, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_223])).
% 8.34/2.99  tff(c_229, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_225])).
% 8.34/2.99  tff(c_274, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.34/2.99  tff(c_291, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_274])).
% 8.34/2.99  tff(c_653, plain, (![A_134, B_135, C_136]: (k2_relset_1(A_134, B_135, C_136)=k2_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.34/2.99  tff(c_660, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_653])).
% 8.34/2.99  tff(c_673, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_660])).
% 8.34/2.99  tff(c_38, plain, (![A_20]: (k2_relat_1(A_20)=k1_xboole_0 | k1_relat_1(A_20)!=k1_xboole_0 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.34/2.99  tff(c_299, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_291, c_38])).
% 8.34/2.99  tff(c_377, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_299])).
% 8.34/2.99  tff(c_36, plain, (![A_20]: (k1_relat_1(A_20)=k1_xboole_0 | k2_relat_1(A_20)!=k1_xboole_0 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.34/2.99  tff(c_300, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_291, c_36])).
% 8.34/2.99  tff(c_382, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_377, c_300])).
% 8.34/2.99  tff(c_675, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_673, c_382])).
% 8.34/2.99  tff(c_80, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.34/2.99  tff(c_593, plain, (![A_124, B_125, C_126]: (k1_relset_1(A_124, B_125, C_126)=k1_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.34/2.99  tff(c_612, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_593])).
% 8.34/2.99  tff(c_1147, plain, (![B_192, A_193, C_194]: (k1_xboole_0=B_192 | k1_relset_1(A_193, B_192, C_194)=A_193 | ~v1_funct_2(C_194, A_193, B_192) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_193, B_192))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.34/2.99  tff(c_1160, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_1147])).
% 8.34/2.99  tff(c_1179, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_612, c_1160])).
% 8.34/2.99  tff(c_1180, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_675, c_1179])).
% 8.34/2.99  tff(c_44, plain, (![A_22]: (k2_relat_1(k2_funct_1(A_22))=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.34/2.99  tff(c_42, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.34/2.99  tff(c_541, plain, (![A_114]: (k1_relat_1(k2_funct_1(A_114))=k2_relat_1(A_114) | ~v2_funct_1(A_114) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.34/2.99  tff(c_32, plain, (![B_18, A_17]: (r1_tarski(k10_relat_1(B_18, A_17), k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.34/2.99  tff(c_1884, plain, (![A_245, A_246]: (r1_tarski(k10_relat_1(k2_funct_1(A_245), A_246), k2_relat_1(A_245)) | ~v1_relat_1(k2_funct_1(A_245)) | ~v2_funct_1(A_245) | ~v1_funct_1(A_245) | ~v1_relat_1(A_245))), inference(superposition, [status(thm), theory('equality')], [c_541, c_32])).
% 8.34/2.99  tff(c_1901, plain, (![A_246]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_4'), A_246), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_673, c_1884])).
% 8.34/2.99  tff(c_1918, plain, (![A_246]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_4'), A_246), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_76, c_1901])).
% 8.34/2.99  tff(c_1921, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1918])).
% 8.34/2.99  tff(c_1924, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_1921])).
% 8.34/2.99  tff(c_1928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_1924])).
% 8.34/2.99  tff(c_1930, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1918])).
% 8.34/2.99  tff(c_224, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_72])).
% 8.34/2.99  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.34/2.99  tff(c_34, plain, (![A_19]: (k10_relat_1(A_19, k2_relat_1(A_19))=k1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.34/2.99  tff(c_1955, plain, (![A_250]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_4'), A_250), '#skF_3'))), inference(splitRight, [status(thm)], [c_1918])).
% 8.34/2.99  tff(c_1970, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_4')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1955])).
% 8.34/2.99  tff(c_1977, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1930, c_1970])).
% 8.34/2.99  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.34/2.99  tff(c_1996, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4')))), inference(resolution, [status(thm)], [c_1977, c_10])).
% 8.34/2.99  tff(c_2078, plain, (~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_1996])).
% 8.34/2.99  tff(c_2081, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46, c_2078])).
% 8.34/2.99  tff(c_2087, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_76, c_14, c_673, c_2081])).
% 8.34/2.99  tff(c_2088, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_1996])).
% 8.34/2.99  tff(c_775, plain, (![A_144]: (m1_subset_1(A_144, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_144), k2_relat_1(A_144)))) | ~v1_funct_1(A_144) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.34/2.99  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.34/2.99  tff(c_806, plain, (![A_144]: (r1_tarski(A_144, k2_zfmisc_1(k1_relat_1(A_144), k2_relat_1(A_144))) | ~v1_funct_1(A_144) | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_775, c_26])).
% 8.34/2.99  tff(c_2154, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2088, c_806])).
% 8.34/2.99  tff(c_2191, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1930, c_224, c_2154])).
% 8.34/2.99  tff(c_2282, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44, c_2191])).
% 8.34/2.99  tff(c_2303, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_76, c_1180, c_2282])).
% 8.34/2.99  tff(c_2305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_2303])).
% 8.34/2.99  tff(c_2306, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_299])).
% 8.34/2.99  tff(c_2768, plain, (![A_298, B_299, C_300]: (k2_relset_1(A_298, B_299, C_300)=k2_relat_1(C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.34/2.99  tff(c_2775, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_2768])).
% 8.34/2.99  tff(c_2788, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2306, c_2775])).
% 8.34/2.99  tff(c_2307, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_299])).
% 8.34/2.99  tff(c_2320, plain, (![A_17]: (r1_tarski(k10_relat_1('#skF_4', A_17), k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2307, c_32])).
% 8.34/2.99  tff(c_2324, plain, (![A_17]: (r1_tarski(k10_relat_1('#skF_4', A_17), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_2320])).
% 8.34/2.99  tff(c_357, plain, (![A_83, B_84]: (~v1_xboole_0(A_83) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_6, c_352])).
% 8.34/2.99  tff(c_2400, plain, (![B_265, A_266]: (B_265=A_266 | ~r1_tarski(B_265, A_266) | ~v1_xboole_0(A_266))), inference(resolution, [status(thm)], [c_357, c_10])).
% 8.34/2.99  tff(c_2403, plain, (![A_17]: (k10_relat_1('#skF_4', A_17)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_2324, c_2400])).
% 8.34/2.99  tff(c_2418, plain, (![A_17]: (k10_relat_1('#skF_4', A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2403])).
% 8.34/2.99  tff(c_2480, plain, (![B_272, A_273, A_274]: (~v1_xboole_0(B_272) | ~r2_hidden(A_273, A_274) | ~r1_tarski(A_274, B_272))), inference(resolution, [status(thm)], [c_28, c_342])).
% 8.34/2.99  tff(c_2484, plain, (![B_275, A_276, B_277]: (~v1_xboole_0(B_275) | ~r1_tarski(A_276, B_275) | r1_tarski(A_276, B_277))), inference(resolution, [status(thm)], [c_6, c_2480])).
% 8.34/2.99  tff(c_2560, plain, (![B_283, A_284, B_285]: (~v1_xboole_0(k1_relat_1(B_283)) | r1_tarski(k10_relat_1(B_283, A_284), B_285) | ~v1_relat_1(B_283))), inference(resolution, [status(thm)], [c_32, c_2484])).
% 8.34/2.99  tff(c_2578, plain, (![B_285]: (~v1_xboole_0(k1_relat_1('#skF_4')) | r1_tarski(k1_xboole_0, B_285) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2418, c_2560])).
% 8.34/2.99  tff(c_2588, plain, (![B_285]: (r1_tarski(k1_xboole_0, B_285))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_8, c_2307, c_2578])).
% 8.34/2.99  tff(c_2795, plain, (![B_285]: (r1_tarski('#skF_3', B_285))), inference(demodulation, [status(thm), theory('equality')], [c_2788, c_2588])).
% 8.34/2.99  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.34/2.99  tff(c_2813, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2788, c_2788, c_18])).
% 8.34/2.99  tff(c_131, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.34/2.99  tff(c_142, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_78, c_131])).
% 8.34/2.99  tff(c_256, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.34/2.99  tff(c_261, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_142, c_256])).
% 8.34/2.99  tff(c_2465, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_261])).
% 8.34/2.99  tff(c_2919, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2813, c_2465])).
% 8.34/2.99  tff(c_2925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2795, c_2919])).
% 8.34/2.99  tff(c_2926, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_261])).
% 8.34/2.99  tff(c_350, plain, (![A_80]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_80, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_342])).
% 8.34/2.99  tff(c_370, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_350])).
% 8.34/2.99  tff(c_2928, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2926, c_370])).
% 8.34/2.99  tff(c_3357, plain, (![A_348, B_349, C_350]: (k2_relset_1(A_348, B_349, C_350)=k2_relat_1(C_350) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_348, B_349))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.34/2.99  tff(c_3387, plain, (![C_351]: (k2_relset_1('#skF_2', '#skF_3', C_351)=k2_relat_1(C_351) | ~m1_subset_1(C_351, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2926, c_3357])).
% 8.34/2.99  tff(c_3395, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_83, c_3387])).
% 8.34/2.99  tff(c_3398, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2306, c_3395])).
% 8.34/2.99  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.34/2.99  tff(c_2942, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2926, c_16])).
% 8.34/2.99  tff(c_2972, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_2942])).
% 8.34/2.99  tff(c_3412, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3398, c_2972])).
% 8.34/2.99  tff(c_3606, plain, (![A_357]: (k2_zfmisc_1(A_357, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3398, c_3398, c_18])).
% 8.34/2.99  tff(c_3616, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3606, c_2926])).
% 8.34/2.99  tff(c_3633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3412, c_3616])).
% 8.34/2.99  tff(c_3635, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2942])).
% 8.34/2.99  tff(c_3666, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_8])).
% 8.34/2.99  tff(c_3669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2928, c_3666])).
% 8.34/2.99  tff(c_3672, plain, (![A_359]: (~r2_hidden(A_359, '#skF_4'))), inference(splitRight, [status(thm)], [c_350])).
% 8.34/2.99  tff(c_3679, plain, (![B_360]: (r1_tarski('#skF_4', B_360))), inference(resolution, [status(thm)], [c_6, c_3672])).
% 8.34/2.99  tff(c_3700, plain, (![B_362]: (B_362='#skF_4' | ~r1_tarski(B_362, '#skF_4'))), inference(resolution, [status(thm)], [c_3679, c_10])).
% 8.34/2.99  tff(c_3718, plain, (![A_363]: (A_363='#skF_4' | ~v1_xboole_0(A_363))), inference(resolution, [status(thm)], [c_356, c_3700])).
% 8.34/2.99  tff(c_3726, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_3718])).
% 8.34/2.99  tff(c_3734, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_3726, c_20])).
% 8.34/2.99  tff(c_3735, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_3726, c_18])).
% 8.34/2.99  tff(c_3671, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_350])).
% 8.34/2.99  tff(c_3725, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_3671, c_3718])).
% 8.34/2.99  tff(c_5162, plain, (![B_524, A_525]: (B_524='#skF_4' | A_525='#skF_4' | k2_zfmisc_1(A_525, B_524)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_3726, c_3726, c_16])).
% 8.34/2.99  tff(c_5176, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3725, c_5162])).
% 8.34/2.99  tff(c_5177, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_5176])).
% 8.34/2.99  tff(c_5180, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5177, c_225])).
% 8.34/2.99  tff(c_5185, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3735, c_5180])).
% 8.34/2.99  tff(c_3736, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_8])).
% 8.34/2.99  tff(c_3801, plain, (k2_relat_1('#skF_4')='#skF_4' | k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_3726, c_299])).
% 8.34/2.99  tff(c_3802, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_3801])).
% 8.34/2.99  tff(c_3834, plain, (k1_relat_1('#skF_4')='#skF_4' | k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_3726, c_300])).
% 8.34/2.99  tff(c_3835, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3802, c_3834])).
% 8.34/2.99  tff(c_4782, plain, (![A_488, B_489, C_490]: (k2_relset_1(A_488, B_489, C_490)=k2_relat_1(C_490) | ~m1_subset_1(C_490, k1_zfmisc_1(k2_zfmisc_1(A_488, B_489))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.34/2.99  tff(c_4827, plain, (![A_495, B_496]: (k2_relset_1(A_495, B_496, k2_zfmisc_1(A_495, B_496))=k2_relat_1(k2_zfmisc_1(A_495, B_496)))), inference(resolution, [status(thm)], [c_83, c_4782])).
% 8.34/2.99  tff(c_4839, plain, (![A_8]: (k2_relat_1(k2_zfmisc_1(A_8, '#skF_4'))=k2_relset_1(A_8, '#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3735, c_4827])).
% 8.34/2.99  tff(c_4876, plain, (![A_500]: (k2_relset_1(A_500, '#skF_4', '#skF_4')=k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3735, c_4839])).
% 8.34/2.99  tff(c_4093, plain, (![A_401, B_402, C_403]: (k1_relset_1(A_401, B_402, C_403)=k1_relat_1(C_403) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.34/2.99  tff(c_4126, plain, (![A_405, B_406]: (k1_relset_1(A_405, B_406, k2_zfmisc_1(A_405, B_406))=k1_relat_1(k2_zfmisc_1(A_405, B_406)))), inference(resolution, [status(thm)], [c_83, c_4093])).
% 8.34/2.99  tff(c_4135, plain, (![B_9]: (k1_relat_1(k2_zfmisc_1('#skF_4', B_9))=k1_relset_1('#skF_4', B_9, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3734, c_4126])).
% 8.34/2.99  tff(c_4141, plain, (![B_9]: (k1_relset_1('#skF_4', B_9, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3734, c_4135])).
% 8.34/2.99  tff(c_3966, plain, (![B_390, A_391]: (B_390='#skF_4' | A_391='#skF_4' | k2_zfmisc_1(A_391, B_390)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_3726, c_3726, c_16])).
% 8.34/2.99  tff(c_3980, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3725, c_3966])).
% 8.34/2.99  tff(c_3981, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_3980])).
% 8.34/2.99  tff(c_3986, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3981, c_80])).
% 8.34/2.99  tff(c_62, plain, (![B_33, C_34]: (k1_relset_1(k1_xboole_0, B_33, C_34)=k1_xboole_0 | ~v1_funct_2(C_34, k1_xboole_0, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.34/2.99  tff(c_84, plain, (![B_33, C_34]: (k1_relset_1(k1_xboole_0, B_33, C_34)=k1_xboole_0 | ~v1_funct_2(C_34, k1_xboole_0, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_62])).
% 8.34/2.99  tff(c_4452, plain, (![B_444, C_445]: (k1_relset_1('#skF_4', B_444, C_445)='#skF_4' | ~v1_funct_2(C_445, '#skF_4', B_444) | ~m1_subset_1(C_445, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_3726, c_3726, c_3726, c_84])).
% 8.34/2.99  tff(c_4454, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_3986, c_4452])).
% 8.34/2.99  tff(c_4460, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_4141, c_4454])).
% 8.34/2.99  tff(c_4462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3802, c_4460])).
% 8.34/2.99  tff(c_4463, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_3980])).
% 8.34/2.99  tff(c_4468, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4463, c_4463, c_74])).
% 8.34/2.99  tff(c_4883, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4876, c_4468])).
% 8.34/2.99  tff(c_4894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3835, c_4883])).
% 8.34/2.99  tff(c_4895, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_3801])).
% 8.34/2.99  tff(c_5116, plain, (![B_517, A_518, A_519]: (~v1_xboole_0(B_517) | ~r2_hidden(A_518, A_519) | ~r1_tarski(A_519, B_517))), inference(resolution, [status(thm)], [c_28, c_342])).
% 8.34/2.99  tff(c_5148, plain, (![B_521, A_522, B_523]: (~v1_xboole_0(B_521) | ~r1_tarski(A_522, B_521) | r1_tarski(A_522, B_523))), inference(resolution, [status(thm)], [c_6, c_5116])).
% 8.34/2.99  tff(c_5448, plain, (![B_551, A_552, B_553]: (~v1_xboole_0(k1_relat_1(B_551)) | r1_tarski(k10_relat_1(B_551, A_552), B_553) | ~v1_relat_1(B_551))), inference(resolution, [status(thm)], [c_32, c_5148])).
% 8.34/2.99  tff(c_3688, plain, (![B_360]: (B_360='#skF_4' | ~r1_tarski(B_360, '#skF_4'))), inference(resolution, [status(thm)], [c_3679, c_10])).
% 8.34/2.99  tff(c_5503, plain, (![B_558, A_559]: (k10_relat_1(B_558, A_559)='#skF_4' | ~v1_xboole_0(k1_relat_1(B_558)) | ~v1_relat_1(B_558))), inference(resolution, [status(thm)], [c_5448, c_3688])).
% 8.34/2.99  tff(c_5517, plain, (![A_562, A_563]: (k10_relat_1(k2_funct_1(A_562), A_563)='#skF_4' | ~v1_xboole_0(k2_relat_1(A_562)) | ~v1_relat_1(k2_funct_1(A_562)) | ~v2_funct_1(A_562) | ~v1_funct_1(A_562) | ~v1_relat_1(A_562))), inference(superposition, [status(thm), theory('equality')], [c_46, c_5503])).
% 8.34/2.99  tff(c_5523, plain, (![A_563]: (k10_relat_1(k2_funct_1('#skF_4'), A_563)='#skF_4' | ~v1_xboole_0('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4895, c_5517])).
% 8.34/2.99  tff(c_5527, plain, (![A_563]: (k10_relat_1(k2_funct_1('#skF_4'), A_563)='#skF_4' | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_76, c_3736, c_5523])).
% 8.34/2.99  tff(c_5528, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5527])).
% 8.34/2.99  tff(c_5531, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_5528])).
% 8.34/2.99  tff(c_5535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_5531])).
% 8.34/2.99  tff(c_5537, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5527])).
% 8.34/2.99  tff(c_5546, plain, (![A_564]: (k10_relat_1(k2_funct_1('#skF_4'), A_564)='#skF_4')), inference(splitRight, [status(thm)], [c_5527])).
% 8.34/2.99  tff(c_5558, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5546, c_34])).
% 8.34/2.99  tff(c_5571, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5537, c_5558])).
% 8.34/2.99  tff(c_66, plain, (![A_35]: (m1_subset_1(A_35, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_35), k2_relat_1(A_35)))) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.34/2.99  tff(c_5584, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5571, c_66])).
% 8.34/2.99  tff(c_5606, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5537, c_224, c_3734, c_5584])).
% 8.34/2.99  tff(c_5608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5185, c_5606])).
% 8.34/2.99  tff(c_5609, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_5176])).
% 8.34/2.99  tff(c_5627, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5609, c_225])).
% 8.34/2.99  tff(c_5632, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3734, c_5627])).
% 8.34/2.99  tff(c_5858, plain, (![B_587, A_588, B_589]: (~v1_xboole_0(k1_relat_1(B_587)) | r1_tarski(k10_relat_1(B_587, A_588), B_589) | ~v1_relat_1(B_587))), inference(resolution, [status(thm)], [c_32, c_5148])).
% 8.34/2.99  tff(c_5913, plain, (![B_594, A_595]: (k10_relat_1(B_594, A_595)='#skF_4' | ~v1_xboole_0(k1_relat_1(B_594)) | ~v1_relat_1(B_594))), inference(resolution, [status(thm)], [c_5858, c_3688])).
% 8.34/2.99  tff(c_5920, plain, (![A_596, A_597]: (k10_relat_1(k2_funct_1(A_596), A_597)='#skF_4' | ~v1_xboole_0(k2_relat_1(A_596)) | ~v1_relat_1(k2_funct_1(A_596)) | ~v2_funct_1(A_596) | ~v1_funct_1(A_596) | ~v1_relat_1(A_596))), inference(superposition, [status(thm), theory('equality')], [c_46, c_5913])).
% 8.34/2.99  tff(c_5926, plain, (![A_597]: (k10_relat_1(k2_funct_1('#skF_4'), A_597)='#skF_4' | ~v1_xboole_0('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4895, c_5920])).
% 8.34/2.99  tff(c_5930, plain, (![A_597]: (k10_relat_1(k2_funct_1('#skF_4'), A_597)='#skF_4' | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_76, c_3736, c_5926])).
% 8.34/2.99  tff(c_5931, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5930])).
% 8.34/2.99  tff(c_5934, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_5931])).
% 8.34/2.99  tff(c_5938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_291, c_82, c_5934])).
% 8.34/2.99  tff(c_5940, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5930])).
% 8.34/2.99  tff(c_5949, plain, (![A_598]: (k10_relat_1(k2_funct_1('#skF_4'), A_598)='#skF_4')), inference(splitRight, [status(thm)], [c_5930])).
% 8.34/2.99  tff(c_5961, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5949, c_34])).
% 8.34/2.99  tff(c_5974, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5940, c_5961])).
% 8.34/2.99  tff(c_5985, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5974, c_66])).
% 8.34/2.99  tff(c_6005, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5940, c_224, c_3734, c_5985])).
% 8.34/2.99  tff(c_6007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5632, c_6005])).
% 8.34/2.99  tff(c_6008, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_223])).
% 8.34/2.99  tff(c_6009, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_223])).
% 8.34/2.99  tff(c_6426, plain, (![A_661, B_662, C_663]: (k1_relset_1(A_661, B_662, C_663)=k1_relat_1(C_663) | ~m1_subset_1(C_663, k1_zfmisc_1(k2_zfmisc_1(A_661, B_662))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.34/2.99  tff(c_6447, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6009, c_6426])).
% 8.34/2.99  tff(c_6972, plain, (![B_726, C_727, A_728]: (k1_xboole_0=B_726 | v1_funct_2(C_727, A_728, B_726) | k1_relset_1(A_728, B_726, C_727)!=A_728 | ~m1_subset_1(C_727, k1_zfmisc_1(k2_zfmisc_1(A_728, B_726))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.34/2.99  tff(c_6981, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_6009, c_6972])).
% 8.34/2.99  tff(c_7005, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6447, c_6981])).
% 8.34/2.99  tff(c_7006, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6008, c_7005])).
% 8.34/2.99  tff(c_7014, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_7006])).
% 8.34/2.99  tff(c_7017, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46, c_7014])).
% 8.34/2.99  tff(c_7020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6035, c_82, c_76, c_6492, c_7017])).
% 8.34/2.99  tff(c_7021, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7006])).
% 8.34/2.99  tff(c_6055, plain, (![A_605]: (k2_relat_1(A_605)=k1_xboole_0 | k1_relat_1(A_605)!=k1_xboole_0 | ~v1_relat_1(A_605))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.34/2.99  tff(c_6074, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6035, c_6055])).
% 8.34/2.99  tff(c_6083, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6074])).
% 8.34/2.99  tff(c_7046, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7021, c_6083])).
% 8.34/2.99  tff(c_6119, plain, (![A_612]: (k1_relat_1(A_612)=k1_xboole_0 | k2_relat_1(A_612)!=k1_xboole_0 | ~v1_relat_1(A_612))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.34/2.99  tff(c_6131, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6035, c_6119])).
% 8.34/2.99  tff(c_6142, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_6083, c_6131])).
% 8.34/2.99  tff(c_6494, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6492, c_6142])).
% 8.34/2.99  tff(c_7036, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7021, c_6494])).
% 8.34/2.99  tff(c_6449, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_6426])).
% 8.34/2.99  tff(c_64, plain, (![B_33, A_32, C_34]: (k1_xboole_0=B_33 | k1_relset_1(A_32, B_33, C_34)=A_32 | ~v1_funct_2(C_34, A_32, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.34/2.99  tff(c_7078, plain, (![B_729, A_730, C_731]: (B_729='#skF_2' | k1_relset_1(A_730, B_729, C_731)=A_730 | ~v1_funct_2(C_731, A_730, B_729) | ~m1_subset_1(C_731, k1_zfmisc_1(k2_zfmisc_1(A_730, B_729))))), inference(demodulation, [status(thm), theory('equality')], [c_7021, c_64])).
% 8.34/2.99  tff(c_7094, plain, ('#skF_2'='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_7078])).
% 8.34/2.99  tff(c_7109, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6449, c_7094])).
% 8.34/2.99  tff(c_7111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7046, c_7036, c_7109])).
% 8.34/2.99  tff(c_7112, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6074])).
% 8.34/2.99  tff(c_7113, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6074])).
% 8.34/2.99  tff(c_10077, plain, (![A_965]: (m1_subset_1(A_965, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_965), k2_relat_1(A_965)))) | ~v1_funct_1(A_965) | ~v1_relat_1(A_965))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.34/2.99  tff(c_10109, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7113, c_10077])).
% 8.34/2.99  tff(c_10127, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6035, c_82, c_20, c_7112, c_10109])).
% 8.34/2.99  tff(c_10170, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_10127, c_26])).
% 8.34/2.99  tff(c_9252, plain, (![C_907, B_908, A_909]: (~v1_xboole_0(C_907) | ~m1_subset_1(B_908, k1_zfmisc_1(C_907)) | ~r2_hidden(A_909, B_908))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.34/2.99  tff(c_9265, plain, (![A_910, A_911]: (~v1_xboole_0(A_910) | ~r2_hidden(A_911, A_910))), inference(resolution, [status(thm)], [c_83, c_9252])).
% 8.34/2.99  tff(c_9270, plain, (![A_912, B_913]: (~v1_xboole_0(A_912) | r1_tarski(A_912, B_913))), inference(resolution, [status(thm)], [c_6, c_9265])).
% 8.34/2.99  tff(c_9285, plain, (![B_913, A_912]: (B_913=A_912 | ~r1_tarski(B_913, A_912) | ~v1_xboole_0(A_912))), inference(resolution, [status(thm)], [c_9270, c_10])).
% 8.34/2.99  tff(c_10181, plain, (k1_xboole_0='#skF_4' | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_10170, c_9285])).
% 8.34/2.99  tff(c_10192, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10181])).
% 8.34/2.99  tff(c_10226, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10192, c_8])).
% 8.34/2.99  tff(c_10225, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10192, c_10192, c_18])).
% 8.34/2.99  tff(c_10217, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10192, c_7112])).
% 8.34/2.99  tff(c_10236, plain, (![A_968, B_969, C_970]: (k2_relset_1(A_968, B_969, C_970)=k2_relat_1(C_970) | ~m1_subset_1(C_970, k1_zfmisc_1(k2_zfmisc_1(A_968, B_969))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.34/2.99  tff(c_10249, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_10236])).
% 8.34/2.99  tff(c_10258, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10249])).
% 8.34/2.99  tff(c_10310, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10217, c_10258])).
% 8.34/2.99  tff(c_9263, plain, (![A_909]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_909, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_9252])).
% 8.34/2.99  tff(c_9326, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_9263])).
% 8.34/2.99  tff(c_10332, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10310, c_9326])).
% 8.34/2.99  tff(c_10545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10226, c_10225, c_10332])).
% 8.34/2.99  tff(c_10547, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_9263])).
% 8.34/2.99  tff(c_9222, plain, (![B_902, A_903]: (B_902=A_903 | ~r1_tarski(B_902, A_903) | ~r1_tarski(A_903, B_902))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.34/2.99  tff(c_9242, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_142, c_9222])).
% 8.34/2.99  tff(c_9251, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_9242])).
% 8.34/2.99  tff(c_9284, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_9270, c_9251])).
% 8.34/2.99  tff(c_10602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10547, c_9284])).
% 8.34/2.99  tff(c_10603, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_9242])).
% 8.34/2.99  tff(c_10618, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_10603, c_16])).
% 8.34/2.99  tff(c_10643, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_10618])).
% 8.34/2.99  tff(c_11077, plain, (![A_1028]: (m1_subset_1(A_1028, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1028), k2_relat_1(A_1028)))) | ~v1_funct_1(A_1028) | ~v1_relat_1(A_1028))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.34/2.99  tff(c_11112, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7113, c_11077])).
% 8.34/2.99  tff(c_11131, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6035, c_82, c_20, c_7112, c_11112])).
% 8.34/2.99  tff(c_11151, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_11131, c_26])).
% 8.34/2.99  tff(c_10644, plain, (![C_986, B_987, A_988]: (~v1_xboole_0(C_986) | ~m1_subset_1(B_987, k1_zfmisc_1(C_986)) | ~r2_hidden(A_988, B_987))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.34/2.99  tff(c_10654, plain, (![A_989, A_990]: (~v1_xboole_0(A_989) | ~r2_hidden(A_990, A_989))), inference(resolution, [status(thm)], [c_83, c_10644])).
% 8.34/2.99  tff(c_10691, plain, (![A_992, B_993]: (~v1_xboole_0(A_992) | r1_tarski(A_992, B_993))), inference(resolution, [status(thm)], [c_6, c_10654])).
% 8.34/2.99  tff(c_10707, plain, (![B_993, A_992]: (B_993=A_992 | ~r1_tarski(B_993, A_992) | ~v1_xboole_0(A_992))), inference(resolution, [status(thm)], [c_10691, c_10])).
% 8.34/2.99  tff(c_11164, plain, (k1_xboole_0='#skF_4' | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_11151, c_10707])).
% 8.34/2.99  tff(c_11177, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_11164])).
% 8.34/2.99  tff(c_11179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10643, c_11177])).
% 8.34/2.99  tff(c_11181, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_10618])).
% 8.34/2.99  tff(c_11720, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11181, c_7113])).
% 8.34/2.99  tff(c_11728, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11181, c_11181, c_20])).
% 8.34/2.99  tff(c_12425, plain, (![A_1109, B_1110, C_1111]: (k1_relset_1(A_1109, B_1110, C_1111)=k1_relat_1(C_1111) | ~m1_subset_1(C_1111, k1_zfmisc_1(k2_zfmisc_1(A_1109, B_1110))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.34/2.99  tff(c_12453, plain, (![A_1114, B_1115]: (k1_relset_1(A_1114, B_1115, k2_zfmisc_1(A_1114, B_1115))=k1_relat_1(k2_zfmisc_1(A_1114, B_1115)))), inference(resolution, [status(thm)], [c_83, c_12425])).
% 8.34/2.99  tff(c_12462, plain, (![B_9]: (k1_relat_1(k2_zfmisc_1('#skF_4', B_9))=k1_relset_1('#skF_4', B_9, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11728, c_12453])).
% 8.34/2.99  tff(c_12468, plain, (![B_9]: (k1_relset_1('#skF_4', B_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11720, c_11728, c_12462])).
% 8.34/2.99  tff(c_58, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.34/2.99  tff(c_85, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_58])).
% 8.34/2.99  tff(c_12540, plain, (![C_1124, B_1125]: (v1_funct_2(C_1124, '#skF_4', B_1125) | k1_relset_1('#skF_4', B_1125, C_1124)!='#skF_4' | ~m1_subset_1(C_1124, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11181, c_11181, c_11181, c_11181, c_85])).
% 8.34/2.99  tff(c_12546, plain, (![B_1125]: (v1_funct_2('#skF_4', '#skF_4', B_1125) | k1_relset_1('#skF_4', B_1125, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_83, c_12540])).
% 8.34/2.99  tff(c_12550, plain, (![B_1125]: (v1_funct_2('#skF_4', '#skF_4', B_1125))), inference(demodulation, [status(thm), theory('equality')], [c_12468, c_12546])).
% 8.34/2.99  tff(c_11180, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_10618])).
% 8.34/2.99  tff(c_11878, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11181, c_11181, c_11180])).
% 8.34/2.99  tff(c_11879, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_11878])).
% 8.34/2.99  tff(c_11205, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11181, c_8])).
% 8.34/2.99  tff(c_11231, plain, (![C_1030, B_1031, A_1032]: (~v1_xboole_0(C_1030) | ~m1_subset_1(B_1031, k1_zfmisc_1(C_1030)) | ~r2_hidden(A_1032, B_1031))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.34/2.99  tff(c_11603, plain, (![A_1047, A_1048]: (~v1_xboole_0(A_1047) | ~r2_hidden(A_1048, A_1047))), inference(resolution, [status(thm)], [c_83, c_11231])).
% 8.34/2.99  tff(c_11607, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_11603])).
% 8.34/2.99  tff(c_11204, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11181, c_11181, c_18])).
% 8.34/2.99  tff(c_11421, plain, (![A_1039, A_1040]: (~v1_xboole_0(A_1039) | ~r2_hidden(A_1040, A_1039))), inference(resolution, [status(thm)], [c_83, c_11231])).
% 8.34/2.99  tff(c_11425, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_11421])).
% 8.34/2.99  tff(c_11203, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11181, c_11181, c_20])).
% 8.34/2.99  tff(c_11351, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11181, c_11181, c_11180])).
% 8.34/2.99  tff(c_11352, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_11351])).
% 8.34/2.99  tff(c_6013, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_6009, c_26])).
% 8.34/2.99  tff(c_9241, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4') | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6013, c_9222])).
% 8.34/2.99  tff(c_11182, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_9241])).
% 8.34/2.99  tff(c_11521, plain, (~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11203, c_11352, c_11182])).
% 8.34/2.99  tff(c_11524, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_11425, c_11521])).
% 8.34/2.99  tff(c_11528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11205, c_11524])).
% 8.34/2.99  tff(c_11529, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_11351])).
% 8.34/2.99  tff(c_11698, plain, (~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11204, c_11529, c_11182])).
% 8.34/2.99  tff(c_11701, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_11607, c_11698])).
% 8.34/2.99  tff(c_11705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11205, c_11701])).
% 8.34/2.99  tff(c_11706, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_9241])).
% 8.34/2.99  tff(c_11955, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11728, c_11879, c_11706])).
% 8.34/2.99  tff(c_11883, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11879, c_6008])).
% 8.34/2.99  tff(c_12071, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11955, c_11883])).
% 8.34/2.99  tff(c_12554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12550, c_12071])).
% 8.34/2.99  tff(c_12556, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_11878])).
% 8.34/2.99  tff(c_54, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.34/2.99  tff(c_87, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_54])).
% 8.34/2.99  tff(c_89, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_87])).
% 8.34/2.99  tff(c_12818, plain, (![A_1141]: (v1_funct_2('#skF_4', A_1141, '#skF_4') | A_1141='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11181, c_11181, c_11181, c_89])).
% 8.34/2.99  tff(c_11729, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11181, c_11181, c_18])).
% 8.34/2.99  tff(c_12555, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_11878])).
% 8.34/2.99  tff(c_12628, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11729, c_12555, c_11706])).
% 8.34/2.99  tff(c_12560, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12555, c_6008])).
% 8.34/2.99  tff(c_12776, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12628, c_12560])).
% 8.34/2.99  tff(c_12823, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_12818, c_12776])).
% 8.34/2.99  tff(c_12831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12556, c_12823])).
% 8.34/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.34/2.99  
% 8.34/2.99  Inference rules
% 8.34/2.99  ----------------------
% 8.34/2.99  #Ref     : 0
% 8.34/2.99  #Sup     : 2793
% 8.34/2.99  #Fact    : 0
% 8.34/2.99  #Define  : 0
% 8.34/2.99  #Split   : 70
% 8.34/2.99  #Chain   : 0
% 8.34/2.99  #Close   : 0
% 8.34/2.99  
% 8.34/2.99  Ordering : KBO
% 8.34/2.99  
% 8.34/2.99  Simplification rules
% 8.34/2.99  ----------------------
% 8.34/2.99  #Subsume      : 404
% 8.34/2.99  #Demod        : 3071
% 8.34/2.99  #Tautology    : 1431
% 8.34/2.99  #SimpNegUnit  : 89
% 8.34/2.99  #BackRed      : 449
% 8.34/2.99  
% 8.34/2.99  #Partial instantiations: 0
% 8.34/2.99  #Strategies tried      : 1
% 8.34/2.99  
% 8.34/2.99  Timing (in seconds)
% 8.34/2.99  ----------------------
% 8.34/2.99  Preprocessing        : 0.35
% 8.34/2.99  Parsing              : 0.18
% 8.34/2.99  CNF conversion       : 0.02
% 8.34/2.99  Main loop            : 1.81
% 8.34/2.99  Inferencing          : 0.60
% 8.34/2.99  Reduction            : 0.64
% 8.34/2.99  Demodulation         : 0.44
% 8.34/2.99  BG Simplification    : 0.07
% 8.34/2.99  Subsumption          : 0.34
% 8.34/2.99  Abstraction          : 0.07
% 8.34/2.99  MUC search           : 0.00
% 8.34/2.99  Cooper               : 0.00
% 8.34/2.99  Total                : 2.26
% 8.34/2.99  Index Insertion      : 0.00
% 8.34/2.99  Index Deletion       : 0.00
% 8.34/2.99  Index Matching       : 0.00
% 8.34/2.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
