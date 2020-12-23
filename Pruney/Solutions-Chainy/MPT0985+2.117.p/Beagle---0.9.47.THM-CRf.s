%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:45 EST 2020

% Result     : Theorem 9.26s
% Output     : CNFRefutation 9.83s
% Verified   : 
% Statistics : Number of formulae       :  440 (7532 expanded)
%              Number of leaves         :   33 (2272 expanded)
%              Depth                    :   23
%              Number of atoms          :  780 (19544 expanded)
%              Number of equality atoms :  255 (7538 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_17150,plain,(
    ! [C_1164,A_1165,B_1166] :
      ( v1_relat_1(C_1164)
      | ~ m1_subset_1(C_1164,k1_zfmisc_1(k2_zfmisc_1(A_1165,B_1166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_17167,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_17150])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_18249,plain,(
    ! [A_1249,B_1250,C_1251] :
      ( k1_relset_1(A_1249,B_1250,C_1251) = k1_relat_1(C_1251)
      | ~ m1_subset_1(C_1251,k1_zfmisc_1(k2_zfmisc_1(A_1249,B_1250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18267,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_18249])).

tff(c_19914,plain,(
    ! [B_1349,A_1350,C_1351] :
      ( k1_xboole_0 = B_1349
      | k1_relset_1(A_1350,B_1349,C_1351) = A_1350
      | ~ v1_funct_2(C_1351,A_1350,B_1349)
      | ~ m1_subset_1(C_1351,k1_zfmisc_1(k2_zfmisc_1(A_1350,B_1349))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_19938,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_19914])).

tff(c_19952,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_18267,c_19938])).

tff(c_19954,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_19952])).

tff(c_19614,plain,(
    ! [A_1337,B_1338,C_1339] :
      ( m1_subset_1(k1_relset_1(A_1337,B_1338,C_1339),k1_zfmisc_1(A_1337))
      | ~ m1_subset_1(C_1339,k1_zfmisc_1(k2_zfmisc_1(A_1337,B_1338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_19676,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18267,c_19614])).

tff(c_19704,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_19676])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_19809,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_19704,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_19812,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_19809,c_2])).

tff(c_19896,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_19812])).

tff(c_19955,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19954,c_19896])).

tff(c_19966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_19955])).

tff(c_19967,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_19952])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19998,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19967,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_19996,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19967,c_19967,c_12])).

tff(c_176,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_184,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_176])).

tff(c_17174,plain,(
    ! [B_1168,A_1169] :
      ( B_1168 = A_1169
      | ~ r1_tarski(B_1168,A_1169)
      | ~ r1_tarski(A_1169,B_1168) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17184,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_184,c_17174])).

tff(c_17214,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_17184])).

tff(c_20059,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19996,c_17214])).

tff(c_20064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19998,c_20059])).

tff(c_20065,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19812])).

tff(c_101,plain,(
    ! [A_33] :
      ( v1_funct_1(k2_funct_1(A_33))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_98,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_104,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_101,c_98])).

tff(c_107,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_104])).

tff(c_155,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_162,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_155])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_162])).

tff(c_172,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_186,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_191,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_204,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_191])).

tff(c_335,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_350,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_335])).

tff(c_1648,plain,(
    ! [B_171,A_172,C_173] :
      ( k1_xboole_0 = B_171
      | k1_relset_1(A_172,B_171,C_173) = A_172
      | ~ v1_funct_2(C_173,A_172,B_171)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1665,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1648])).

tff(c_1677,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_350,c_1665])).

tff(c_1679,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1677])).

tff(c_578,plain,(
    ! [A_96,B_97,C_98] :
      ( m1_subset_1(k1_relset_1(A_96,B_97,C_98),k1_zfmisc_1(A_96))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_615,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_578])).

tff(c_631,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_615])).

tff(c_635,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_631,c_16])).

tff(c_638,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_635,c_2])).

tff(c_646,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_638])).

tff(c_1683,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1679,c_646])).

tff(c_1692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1683])).

tff(c_1693,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1677])).

tff(c_1725,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_8])).

tff(c_1723,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1693,c_12])).

tff(c_211,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_218,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_184,c_211])).

tff(c_248,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_1804,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_248])).

tff(c_1809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1725,c_1804])).

tff(c_1810,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_638])).

tff(c_24,plain,(
    ! [A_9] :
      ( k2_relat_1(k2_funct_1(A_9)) = k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_173,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_481,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_491,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_481])).

tff(c_501,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_491])).

tff(c_311,plain,(
    ! [A_67] :
      ( k1_relat_1(k2_funct_1(A_67)) = k2_relat_1(A_67)
      | ~ v2_funct_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ! [A_25] :
      ( v1_funct_2(A_25,k1_relat_1(A_25),k2_relat_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4188,plain,(
    ! [A_338] :
      ( v1_funct_2(k2_funct_1(A_338),k2_relat_1(A_338),k2_relat_1(k2_funct_1(A_338)))
      | ~ v1_funct_1(k2_funct_1(A_338))
      | ~ v1_relat_1(k2_funct_1(A_338))
      | ~ v2_funct_1(A_338)
      | ~ v1_funct_1(A_338)
      | ~ v1_relat_1(A_338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_50])).

tff(c_4191,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_4188])).

tff(c_4199,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_58,c_173,c_4191])).

tff(c_4200,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4199])).

tff(c_4203,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_4200])).

tff(c_4207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_4203])).

tff(c_4209,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4199])).

tff(c_26,plain,(
    ! [A_9] :
      ( k1_relat_1(k2_funct_1(A_9)) = k2_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_388,plain,(
    ! [A_79] :
      ( m1_subset_1(A_79,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_79),k2_relat_1(A_79))))
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4889,plain,(
    ! [A_368] :
      ( m1_subset_1(k2_funct_1(A_368),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_368),k2_relat_1(k2_funct_1(A_368)))))
      | ~ v1_funct_1(k2_funct_1(A_368))
      | ~ v1_relat_1(k2_funct_1(A_368))
      | ~ v2_funct_1(A_368)
      | ~ v1_funct_1(A_368)
      | ~ v1_relat_1(A_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_388])).

tff(c_4912,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_4889])).

tff(c_4927,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_58,c_4209,c_173,c_4912])).

tff(c_4950,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4927])).

tff(c_4963,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_58,c_1810,c_4950])).

tff(c_4965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_4963])).

tff(c_4966,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_4970,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4966,c_60])).

tff(c_5174,plain,(
    ! [A_392,B_393,C_394] :
      ( k1_relset_1(A_392,B_393,C_394) = k1_relat_1(C_394)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5223,plain,(
    ! [C_400] :
      ( k1_relset_1('#skF_1','#skF_2',C_400) = k1_relat_1(C_400)
      | ~ m1_subset_1(C_400,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4966,c_5174])).

tff(c_5231,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4970,c_5223])).

tff(c_8495,plain,(
    ! [B_601,C_602,A_603] :
      ( k1_xboole_0 = B_601
      | v1_funct_2(C_602,A_603,B_601)
      | k1_relset_1(A_603,B_601,C_602) != A_603
      | ~ m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(A_603,B_601))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8512,plain,(
    ! [C_602] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_602,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_602) != '#skF_1'
      | ~ m1_subset_1(C_602,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4966,c_8495])).

tff(c_8574,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8512])).

tff(c_5026,plain,(
    ! [B_374,A_375] :
      ( k1_xboole_0 = B_374
      | k1_xboole_0 = A_375
      | k2_zfmisc_1(A_375,B_374) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5029,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4966,c_5026])).

tff(c_5050,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5029])).

tff(c_8598,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8574,c_5050])).

tff(c_8735,plain,(
    ! [A_615] : k2_zfmisc_1(A_615,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8574,c_8574,c_12])).

tff(c_6284,plain,(
    ! [B_473,C_474,A_475] :
      ( k1_xboole_0 = B_473
      | v1_funct_2(C_474,A_475,B_473)
      | k1_relset_1(A_475,B_473,C_474) != A_475
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(A_475,B_473))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6301,plain,(
    ! [C_474] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_474,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_474) != '#skF_1'
      | ~ m1_subset_1(C_474,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4966,c_6284])).

tff(c_6739,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6301])).

tff(c_6777,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6739,c_8])).

tff(c_6775,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6739,c_6739,c_12])).

tff(c_5097,plain,(
    ! [A_382,B_383,C_384] :
      ( k2_relset_1(A_382,B_383,C_384) = k2_relat_1(C_384)
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(A_382,B_383))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5127,plain,(
    ! [C_388] :
      ( k2_relset_1('#skF_1','#skF_2',C_388) = k2_relat_1(C_388)
      | ~ m1_subset_1(C_388,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4966,c_5097])).

tff(c_5130,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4970,c_5127])).

tff(c_5136,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_5130])).

tff(c_5268,plain,(
    ! [A_405] :
      ( m1_subset_1(A_405,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_405),k2_relat_1(A_405))))
      | ~ v1_funct_1(A_405)
      | ~ v1_relat_1(A_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5283,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5136,c_5268])).

tff(c_5295,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_5283])).

tff(c_5313,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_5295,c_16])).

tff(c_5325,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5313,c_2])).

tff(c_5461,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5325])).

tff(c_6912,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6775,c_5461])).

tff(c_6917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6777,c_6912])).

tff(c_6919,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6301])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6572,plain,(
    ! [B_492,A_493,C_494] :
      ( k1_xboole_0 = B_492
      | k1_relset_1(A_493,B_492,C_494) = A_493
      | ~ v1_funct_2(C_494,A_493,B_492)
      | ~ m1_subset_1(C_494,k1_zfmisc_1(k2_zfmisc_1(A_493,B_492))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7292,plain,(
    ! [B_539,A_540,A_541] :
      ( k1_xboole_0 = B_539
      | k1_relset_1(A_540,B_539,A_541) = A_540
      | ~ v1_funct_2(A_541,A_540,B_539)
      | ~ r1_tarski(A_541,k2_zfmisc_1(A_540,B_539)) ) ),
    inference(resolution,[status(thm)],[c_18,c_6572])).

tff(c_7313,plain,(
    ! [A_541] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',A_541) = '#skF_1'
      | ~ v1_funct_2(A_541,'#skF_1','#skF_2')
      | ~ r1_tarski(A_541,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4966,c_7292])).

tff(c_7342,plain,(
    ! [A_542] :
      ( k1_relset_1('#skF_1','#skF_2',A_542) = '#skF_1'
      | ~ v1_funct_2(A_542,'#skF_1','#skF_2')
      | ~ r1_tarski(A_542,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_6919,c_7313])).

tff(c_7352,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_7342])).

tff(c_7360,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5231,c_7352])).

tff(c_5556,plain,(
    ! [A_431,B_432,C_433] :
      ( m1_subset_1(k1_relset_1(A_431,B_432,C_433),k1_zfmisc_1(A_431))
      | ~ m1_subset_1(C_433,k1_zfmisc_1(k2_zfmisc_1(A_431,B_432))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5614,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5231,c_5556])).

tff(c_5635,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4970,c_4966,c_5614])).

tff(c_5639,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5635,c_16])).

tff(c_5642,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5639,c_2])).

tff(c_5663,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5642])).

tff(c_7361,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7360,c_5663])).

tff(c_7374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7361])).

tff(c_7375,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5642])).

tff(c_7380,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7375,c_5461])).

tff(c_7390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4966,c_7380])).

tff(c_7391,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5325])).

tff(c_8759,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8735,c_7391])).

tff(c_8794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8598,c_8759])).

tff(c_8796,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8512])).

tff(c_8893,plain,(
    ! [B_622,A_623,C_624] :
      ( k1_xboole_0 = B_622
      | k1_relset_1(A_623,B_622,C_624) = A_623
      | ~ v1_funct_2(C_624,A_623,B_622)
      | ~ m1_subset_1(C_624,k1_zfmisc_1(k2_zfmisc_1(A_623,B_622))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8910,plain,(
    ! [C_624] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_624) = '#skF_1'
      | ~ v1_funct_2(C_624,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_624,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4966,c_8893])).

tff(c_9374,plain,(
    ! [C_649] :
      ( k1_relset_1('#skF_1','#skF_2',C_649) = '#skF_1'
      | ~ v1_funct_2(C_649,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_649,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8796,c_8910])).

tff(c_9385,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4970,c_9374])).

tff(c_9395,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5231,c_9385])).

tff(c_8127,plain,(
    ! [A_582,B_583,C_584] :
      ( m1_subset_1(k1_relset_1(A_582,B_583,C_584),k1_zfmisc_1(A_582))
      | ~ m1_subset_1(C_584,k1_zfmisc_1(k2_zfmisc_1(A_582,B_583))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8185,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5231,c_8127])).

tff(c_8209,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4970,c_4966,c_8185])).

tff(c_8243,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8209,c_16])).

tff(c_8246,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8243,c_2])).

tff(c_8253,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8246])).

tff(c_9400,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9395,c_8253])).

tff(c_9412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9400])).

tff(c_9413,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8246])).

tff(c_5073,plain,(
    ! [A_380] :
      ( k2_relat_1(k2_funct_1(A_380)) = k1_relat_1(A_380)
      | ~ v2_funct_1(A_380)
      | ~ v1_funct_1(A_380)
      | ~ v1_relat_1(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_11806,plain,(
    ! [A_788] :
      ( v1_funct_2(k2_funct_1(A_788),k1_relat_1(k2_funct_1(A_788)),k1_relat_1(A_788))
      | ~ v1_funct_1(k2_funct_1(A_788))
      | ~ v1_relat_1(k2_funct_1(A_788))
      | ~ v2_funct_1(A_788)
      | ~ v1_funct_1(A_788)
      | ~ v1_relat_1(A_788) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5073,c_50])).

tff(c_11812,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9413,c_11806])).

tff(c_11823,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_58,c_173,c_11812])).

tff(c_11826,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_11823])).

tff(c_11829,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_11826])).

tff(c_11833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_11829])).

tff(c_11835,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11823])).

tff(c_12493,plain,(
    ! [A_827] :
      ( m1_subset_1(k2_funct_1(A_827),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_827),k2_relat_1(k2_funct_1(A_827)))))
      | ~ v1_funct_1(k2_funct_1(A_827))
      | ~ v1_relat_1(k2_funct_1(A_827))
      | ~ v2_funct_1(A_827)
      | ~ v1_funct_1(A_827)
      | ~ v1_relat_1(A_827) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_5268])).

tff(c_12516,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5136,c_12493])).

tff(c_12531,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_58,c_11835,c_173,c_12516])).

tff(c_12554,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_12531])).

tff(c_12567,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_58,c_9413,c_12554])).

tff(c_12569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_12567])).

tff(c_12571,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5029])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12578,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12571,c_12571,c_14])).

tff(c_12570,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5029])).

tff(c_12601,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12571,c_12571,c_12570])).

tff(c_12602,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12601])).

tff(c_12605,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12602,c_186])).

tff(c_12667,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12578,c_12605])).

tff(c_12577,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12571,c_12571,c_12])).

tff(c_12740,plain,(
    ! [A_840,B_841,C_842] :
      ( k2_relset_1(A_840,B_841,C_842) = k2_relat_1(C_842)
      | ~ m1_subset_1(C_842,k1_zfmisc_1(k2_zfmisc_1(A_840,B_841))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12772,plain,(
    ! [A_846,C_847] :
      ( k2_relset_1(A_846,'#skF_3',C_847) = k2_relat_1(C_847)
      | ~ m1_subset_1(C_847,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12577,c_12740])).

tff(c_12780,plain,(
    ! [A_848] : k2_relset_1(A_848,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4970,c_12772])).

tff(c_12606,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12602,c_12602,c_56])).

tff(c_12784,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_12780,c_12606])).

tff(c_12687,plain,(
    ! [A_836] :
      ( k1_relat_1(k2_funct_1(A_836)) = k2_relat_1(A_836)
      | ~ v2_funct_1(A_836)
      | ~ v1_funct_1(A_836)
      | ~ v1_relat_1(A_836) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14133,plain,(
    ! [A_959] :
      ( v1_funct_2(k2_funct_1(A_959),k2_relat_1(A_959),k2_relat_1(k2_funct_1(A_959)))
      | ~ v1_funct_1(k2_funct_1(A_959))
      | ~ v1_relat_1(k2_funct_1(A_959))
      | ~ v2_funct_1(A_959)
      | ~ v1_funct_1(A_959)
      | ~ v1_relat_1(A_959) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12687,c_50])).

tff(c_14136,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12784,c_14133])).

tff(c_14144,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_58,c_173,c_14136])).

tff(c_14162,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14144])).

tff(c_14165,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_14162])).

tff(c_14169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_14165])).

tff(c_14171,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_14144])).

tff(c_12756,plain,(
    ! [A_843,B_844,C_845] :
      ( k1_relset_1(A_843,B_844,C_845) = k1_relat_1(C_845)
      | ~ m1_subset_1(C_845,k1_zfmisc_1(k2_zfmisc_1(A_843,B_844))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12877,plain,(
    ! [B_859,C_860] :
      ( k1_relset_1('#skF_3',B_859,C_860) = k1_relat_1(C_860)
      | ~ m1_subset_1(C_860,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12578,c_12756])).

tff(c_12883,plain,(
    ! [B_859] : k1_relset_1('#skF_3',B_859,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4970,c_12877])).

tff(c_40,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_12921,plain,(
    ! [C_866,B_867] :
      ( v1_funct_2(C_866,'#skF_3',B_867)
      | k1_relset_1('#skF_3',B_867,C_866) != '#skF_3'
      | ~ m1_subset_1(C_866,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12571,c_12571,c_12571,c_12571,c_66])).

tff(c_12923,plain,(
    ! [B_867] :
      ( v1_funct_2('#skF_3','#skF_3',B_867)
      | k1_relset_1('#skF_3',B_867,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_4970,c_12921])).

tff(c_12928,plain,(
    ! [B_867] :
      ( v1_funct_2('#skF_3','#skF_3',B_867)
      | k1_relat_1('#skF_3') != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12883,c_12923])).

tff(c_12945,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12928])).

tff(c_12946,plain,(
    ! [A_869,B_870,C_871] :
      ( m1_subset_1(k1_relset_1(A_869,B_870,C_871),k1_zfmisc_1(A_869))
      | ~ m1_subset_1(C_871,k1_zfmisc_1(k2_zfmisc_1(A_869,B_870))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12983,plain,(
    ! [B_859] :
      ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_859))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12883,c_12946])).

tff(c_13004,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4970,c_12578,c_12983])).

tff(c_13029,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_13004,c_16])).

tff(c_223,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_211])).

tff(c_12575,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12571,c_12571,c_223])).

tff(c_13038,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13029,c_12575])).

tff(c_13050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12945,c_13038])).

tff(c_13052,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12928])).

tff(c_12711,plain,(
    ! [A_838] :
      ( m1_subset_1(A_838,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_838),k2_relat_1(A_838))))
      | ~ v1_funct_1(A_838)
      | ~ v1_relat_1(A_838) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14621,plain,(
    ! [A_987] :
      ( m1_subset_1(k2_funct_1(A_987),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_987)),k1_relat_1(A_987))))
      | ~ v1_funct_1(k2_funct_1(A_987))
      | ~ v1_relat_1(k2_funct_1(A_987))
      | ~ v2_funct_1(A_987)
      | ~ v1_funct_1(A_987)
      | ~ v1_relat_1(A_987) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_12711])).

tff(c_14647,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13052,c_14621])).

tff(c_14663,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_64,c_58,c_14171,c_173,c_12577,c_14647])).

tff(c_14665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12667,c_14663])).

tff(c_14666,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12601])).

tff(c_14771,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14666,c_14666,c_12577])).

tff(c_14676,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14666,c_186])).

tff(c_14816,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14771,c_14676])).

tff(c_14674,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14666,c_204])).

tff(c_14681,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14666,c_64])).

tff(c_14680,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14666,c_58])).

tff(c_14672,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14666,c_14666,c_4970])).

tff(c_14906,plain,(
    ! [A_1004,B_1005,C_1006] :
      ( k1_relset_1(A_1004,B_1005,C_1006) = k1_relat_1(C_1006)
      | ~ m1_subset_1(C_1006,k1_zfmisc_1(k2_zfmisc_1(A_1004,B_1005))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14963,plain,(
    ! [A_1013,C_1014] :
      ( k1_relset_1(A_1013,'#skF_1',C_1014) = k1_relat_1(C_1014)
      | ~ m1_subset_1(C_1014,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14771,c_14906])).

tff(c_14969,plain,(
    ! [A_1013] : k1_relset_1(A_1013,'#skF_1','#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14672,c_14963])).

tff(c_15028,plain,(
    ! [A_1024,B_1025,C_1026] :
      ( m1_subset_1(k1_relset_1(A_1024,B_1025,C_1026),k1_zfmisc_1(A_1024))
      | ~ m1_subset_1(C_1026,k1_zfmisc_1(k2_zfmisc_1(A_1024,B_1025))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_15059,plain,(
    ! [A_1013] :
      ( m1_subset_1(k1_relat_1('#skF_1'),k1_zfmisc_1(A_1013))
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_1013,'#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14969,c_15028])).

tff(c_15079,plain,(
    ! [A_1027] : m1_subset_1(k1_relat_1('#skF_1'),k1_zfmisc_1(A_1027)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14672,c_14771,c_15059])).

tff(c_15117,plain,(
    ! [A_1028] : r1_tarski(k1_relat_1('#skF_1'),A_1028) ),
    inference(resolution,[status(thm)],[c_15079,c_16])).

tff(c_14821,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14666,c_14666,c_12575])).

tff(c_15142,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_15117,c_14821])).

tff(c_14677,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14666,c_173])).

tff(c_14874,plain,(
    ! [A_999] :
      ( k2_relat_1(k2_funct_1(A_999)) = k1_relat_1(A_999)
      | ~ v2_funct_1(A_999)
      | ~ v1_funct_1(A_999)
      | ~ v1_relat_1(A_999) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16473,plain,(
    ! [A_1135] :
      ( v1_funct_2(k2_funct_1(A_1135),k1_relat_1(k2_funct_1(A_1135)),k1_relat_1(A_1135))
      | ~ v1_funct_1(k2_funct_1(A_1135))
      | ~ v1_relat_1(k2_funct_1(A_1135))
      | ~ v2_funct_1(A_1135)
      | ~ v1_funct_1(A_1135)
      | ~ v1_relat_1(A_1135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14874,c_50])).

tff(c_16476,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15142,c_16473])).

tff(c_16484,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14674,c_14681,c_14680,c_14677,c_16476])).

tff(c_16485,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_16484])).

tff(c_16488,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_16485])).

tff(c_16492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14674,c_14681,c_16488])).

tff(c_16494,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_16484])).

tff(c_15076,plain,(
    ! [A_1013] : m1_subset_1(k1_relat_1('#skF_1'),k1_zfmisc_1(A_1013)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14672,c_14771,c_15059])).

tff(c_15182,plain,(
    ! [A_1031] : m1_subset_1('#skF_1',k1_zfmisc_1(A_1031)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15142,c_15076])).

tff(c_34,plain,(
    ! [A_19,B_20,C_21] :
      ( k2_relset_1(A_19,B_20,C_21) = k2_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_15306,plain,(
    ! [A_1039,B_1040] : k2_relset_1(A_1039,B_1040,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_15182,c_34])).

tff(c_14678,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14666,c_56])).

tff(c_15310,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_15306,c_14678])).

tff(c_14918,plain,(
    ! [A_1007] :
      ( m1_subset_1(A_1007,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1007),k2_relat_1(A_1007))))
      | ~ v1_funct_1(A_1007)
      | ~ v1_relat_1(A_1007) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_17056,plain,(
    ! [A_1161] :
      ( m1_subset_1(k2_funct_1(A_1161),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1161),k2_relat_1(k2_funct_1(A_1161)))))
      | ~ v1_funct_1(k2_funct_1(A_1161))
      | ~ v1_relat_1(k2_funct_1(A_1161))
      | ~ v2_funct_1(A_1161)
      | ~ v1_funct_1(A_1161)
      | ~ v1_relat_1(A_1161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_14918])).

tff(c_17079,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_1')))))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15310,c_17056])).

tff(c_17094,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14674,c_14681,c_14680,c_16494,c_14677,c_17079])).

tff(c_17117,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_1'))))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_17094])).

tff(c_17130,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14674,c_14681,c_14680,c_14771,c_15142,c_17117])).

tff(c_17132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14816,c_17130])).

tff(c_17133,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_18935,plain,(
    ! [B_1311,A_1312,C_1313] :
      ( k1_xboole_0 = B_1311
      | k1_relset_1(A_1312,B_1311,C_1313) = A_1312
      | ~ v1_funct_2(C_1313,A_1312,B_1311)
      | ~ m1_subset_1(C_1313,k1_zfmisc_1(k2_zfmisc_1(A_1312,B_1311))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18955,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_18935])).

tff(c_18971,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_18267,c_18955])).

tff(c_18973,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18971])).

tff(c_18726,plain,(
    ! [A_1303,B_1304,C_1305] :
      ( m1_subset_1(k1_relset_1(A_1303,B_1304,C_1305),k1_zfmisc_1(A_1303))
      | ~ m1_subset_1(C_1305,k1_zfmisc_1(k2_zfmisc_1(A_1303,B_1304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18787,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18267,c_18726])).

tff(c_18812,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_18787])).

tff(c_18816,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_18812,c_16])).

tff(c_18819,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18816,c_2])).

tff(c_18883,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_18819])).

tff(c_18974,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18973,c_18883])).

tff(c_18987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18974])).

tff(c_18988,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18971])).

tff(c_19020,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18988,c_8])).

tff(c_19018,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18988,c_18988,c_12])).

tff(c_18268,plain,(
    ! [A_1252,B_1253,C_1254] :
      ( k2_relset_1(A_1252,B_1253,C_1254) = k2_relat_1(C_1254)
      | ~ m1_subset_1(C_1254,k1_zfmisc_1(k2_zfmisc_1(A_1252,B_1253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18278,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_18268])).

tff(c_18287,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_18278])).

tff(c_18445,plain,(
    ! [A_1277] :
      ( m1_subset_1(A_1277,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1277),k2_relat_1(A_1277))))
      | ~ v1_funct_1(A_1277)
      | ~ v1_relat_1(A_1277) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_18460,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18287,c_18445])).

tff(c_18472,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17167,c_64,c_18460])).

tff(c_18490,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_18472,c_16])).

tff(c_18502,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_18490,c_2])).

tff(c_18621,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_18502])).

tff(c_19062,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19018,c_18621])).

tff(c_19070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19020,c_19062])).

tff(c_19071,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18819])).

tff(c_17134,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_17165,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_17134,c_17150])).

tff(c_17410,plain,(
    ! [A_1197,B_1198,C_1199] :
      ( k2_relset_1(A_1197,B_1198,C_1199) = k2_relat_1(C_1199)
      | ~ m1_subset_1(C_1199,k1_zfmisc_1(k2_zfmisc_1(A_1197,B_1198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_17423,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_17410])).

tff(c_17434,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_17423])).

tff(c_17303,plain,(
    ! [A_1183,B_1184,C_1185] :
      ( k1_relset_1(A_1183,B_1184,C_1185) = k1_relat_1(C_1185)
      | ~ m1_subset_1(C_1185,k1_zfmisc_1(k2_zfmisc_1(A_1183,B_1184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_17320,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_17134,c_17303])).

tff(c_18033,plain,(
    ! [B_1240,C_1241,A_1242] :
      ( k1_xboole_0 = B_1240
      | v1_funct_2(C_1241,A_1242,B_1240)
      | k1_relset_1(A_1242,B_1240,C_1241) != A_1242
      | ~ m1_subset_1(C_1241,k1_zfmisc_1(k2_zfmisc_1(A_1242,B_1240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18050,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_17134,c_18033])).

tff(c_18072,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17320,c_18050])).

tff(c_18073,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_17133,c_18072])).

tff(c_18078,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18073])).

tff(c_18081,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_18078])).

tff(c_18084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17167,c_64,c_58,c_17434,c_18081])).

tff(c_18085,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18073])).

tff(c_18110,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18085,c_8])).

tff(c_18108,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18085,c_18085,c_12])).

tff(c_17138,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_17134,c_16])).

tff(c_17183,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_17138,c_17174])).

tff(c_17270,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_17183])).

tff(c_18168,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18108,c_17270])).

tff(c_18173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18110,c_18168])).

tff(c_18174,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_17183])).

tff(c_18177,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18174,c_17134])).

tff(c_18301,plain,(
    ! [C_1255] :
      ( k1_relset_1('#skF_2','#skF_1',C_1255) = k1_relat_1(C_1255)
      | ~ m1_subset_1(C_1255,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18174,c_18249])).

tff(c_18309,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18177,c_18301])).

tff(c_18784,plain,
    ( m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18309,c_18726])).

tff(c_18810,plain,(
    m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18177,c_18174,c_18784])).

tff(c_18831,plain,(
    r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_18810,c_16])).

tff(c_18880,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_18831,c_2])).

tff(c_19182,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_18880])).

tff(c_19185,plain,
    ( ~ r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_19182])).

tff(c_19188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17167,c_64,c_58,c_6,c_18287,c_19185])).

tff(c_19189,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18880])).

tff(c_19208,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19189,c_50])).

tff(c_19221,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17165,c_173,c_19208])).

tff(c_19237,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_19221])).

tff(c_19239,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17167,c_64,c_58,c_19071,c_19237])).

tff(c_19241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17133,c_19239])).

tff(c_19242,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18502])).

tff(c_20070,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20065,c_19242])).

tff(c_20113,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20070,c_17214])).

tff(c_20118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20113])).

tff(c_20119,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17184])).

tff(c_20123,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20119,c_60])).

tff(c_20373,plain,(
    ! [A_1380,B_1381,C_1382] :
      ( k2_relset_1(A_1380,B_1381,C_1382) = k2_relat_1(C_1382)
      | ~ m1_subset_1(C_1382,k1_zfmisc_1(k2_zfmisc_1(A_1380,B_1381))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20419,plain,(
    ! [C_1387] :
      ( k2_relset_1('#skF_1','#skF_2',C_1387) = k2_relat_1(C_1387)
      | ~ m1_subset_1(C_1387,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20119,c_20373])).

tff(c_20422,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20123,c_20419])).

tff(c_20428,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_20422])).

tff(c_20252,plain,(
    ! [A_1366,B_1367,C_1368] :
      ( k1_relset_1(A_1366,B_1367,C_1368) = k1_relat_1(C_1368)
      | ~ m1_subset_1(C_1368,k1_zfmisc_1(k2_zfmisc_1(A_1366,B_1367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20269,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_17134,c_20252])).

tff(c_21283,plain,(
    ! [B_1427,C_1428,A_1429] :
      ( k1_xboole_0 = B_1427
      | v1_funct_2(C_1428,A_1429,B_1427)
      | k1_relset_1(A_1429,B_1427,C_1428) != A_1429
      | ~ m1_subset_1(C_1428,k1_zfmisc_1(k2_zfmisc_1(A_1429,B_1427))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_21300,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_17134,c_21283])).

tff(c_21316,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20269,c_21300])).

tff(c_21317,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_17133,c_21316])).

tff(c_21320,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_21317])).

tff(c_21323,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_21320])).

tff(c_21326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17167,c_64,c_58,c_20428,c_21323])).

tff(c_21327,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_21317])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20130,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_20119,c_10])).

tff(c_20185,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20130])).

tff(c_21344,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21327,c_20185])).

tff(c_21352,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21327,c_21327,c_14])).

tff(c_21422,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21352,c_20119])).

tff(c_21424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21344,c_21422])).

tff(c_21426,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20130])).

tff(c_21436,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21426,c_21426,c_14])).

tff(c_21425,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_20130])).

tff(c_21454,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21426,c_21426,c_21425])).

tff(c_21455,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_21454])).

tff(c_21437,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21426,c_8])).

tff(c_21456,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_17183])).

tff(c_21603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21437,c_21436,c_21455,c_21456])).

tff(c_21604,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_17183])).

tff(c_21643,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21436,c_21455,c_21604])).

tff(c_21675,plain,(
    ! [A_1441] :
      ( k2_relat_1(k2_funct_1(A_1441)) = k1_relat_1(A_1441)
      | ~ v2_funct_1(A_1441)
      | ~ v1_funct_1(A_1441)
      | ~ v1_relat_1(A_1441) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_21687,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21643,c_21675])).

tff(c_21691,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17167,c_64,c_58,c_21687])).

tff(c_21435,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21426,c_21426,c_12])).

tff(c_21761,plain,(
    ! [A_1451,B_1452,C_1453] :
      ( k2_relset_1(A_1451,B_1452,C_1453) = k2_relat_1(C_1453)
      | ~ m1_subset_1(C_1453,k1_zfmisc_1(k2_zfmisc_1(A_1451,B_1452))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_21800,plain,(
    ! [A_1459,C_1460] :
      ( k2_relset_1(A_1459,'#skF_3',C_1460) = k2_relat_1(C_1460)
      | ~ m1_subset_1(C_1460,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21435,c_21761])).

tff(c_21802,plain,(
    ! [A_1459] : k2_relset_1(A_1459,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20123,c_21800])).

tff(c_21809,plain,(
    ! [A_1461] : k2_relset_1(A_1461,'#skF_3','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21691,c_21802])).

tff(c_21610,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21455,c_21455,c_56])).

tff(c_21816,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_21809,c_21610])).

tff(c_21907,plain,(
    ! [A_1468,B_1469,C_1470] :
      ( k1_relset_1(A_1468,B_1469,C_1470) = k1_relat_1(C_1470)
      | ~ m1_subset_1(C_1470,k1_zfmisc_1(k2_zfmisc_1(A_1468,B_1469))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_21919,plain,(
    ! [B_1471,C_1472] :
      ( k1_relset_1('#skF_3',B_1471,C_1472) = k1_relat_1(C_1472)
      | ~ m1_subset_1(C_1472,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21436,c_21907])).

tff(c_21921,plain,(
    ! [B_1471] : k1_relset_1('#skF_3',B_1471,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20123,c_21919])).

tff(c_21926,plain,(
    ! [B_1471] : k1_relset_1('#skF_3',B_1471,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21816,c_21921])).

tff(c_22042,plain,(
    ! [C_1487,B_1488] :
      ( v1_funct_2(C_1487,'#skF_3',B_1488)
      | k1_relset_1('#skF_3',B_1488,C_1487) != '#skF_3'
      | ~ m1_subset_1(C_1487,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21426,c_21426,c_21426,c_21426,c_66])).

tff(c_22044,plain,(
    ! [B_1488] :
      ( v1_funct_2('#skF_3','#skF_3',B_1488)
      | k1_relset_1('#skF_3',B_1488,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_20123,c_22042])).

tff(c_22050,plain,(
    ! [B_1488] : v1_funct_2('#skF_3','#skF_3',B_1488) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21926,c_22044])).

tff(c_21609,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21455,c_17133])).

tff(c_21701,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21643,c_21609])).

tff(c_22055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22050,c_21701])).

tff(c_22056,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_21454])).

tff(c_22057,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_21454])).

tff(c_22078,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22056,c_22057])).

tff(c_36,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_22,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_67,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36])).

tff(c_20139,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_20142,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_20139])).

tff(c_20146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20142])).

tff(c_20147,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22 ) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_21428,plain,(
    ! [A_22] :
      ( v1_funct_2('#skF_3',A_22,'#skF_3')
      | A_22 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21426,c_21426,c_21426,c_20147])).

tff(c_22259,plain,(
    ! [A_1499] :
      ( v1_funct_2('#skF_1',A_1499,'#skF_1')
      | A_1499 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22056,c_22056,c_22056,c_21428])).

tff(c_22125,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22056,c_22056,c_21435])).

tff(c_22067,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22056,c_17134])).

tff(c_22183,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22125,c_22067])).

tff(c_22187,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_22183,c_16])).

tff(c_17189,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_17174])).

tff(c_21432,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21426,c_21426,c_17189])).

tff(c_22143,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22056,c_22056,c_21432])).

tff(c_22198,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22187,c_22143])).

tff(c_22068,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22056,c_17133])).

tff(c_22204,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22198,c_22068])).

tff(c_22262,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22259,c_22204])).

tff(c_22266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22078,c_22262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:54:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.26/3.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.43/3.59  
% 9.43/3.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.43/3.60  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.43/3.60  
% 9.43/3.60  %Foreground sorts:
% 9.43/3.60  
% 9.43/3.60  
% 9.43/3.60  %Background operators:
% 9.43/3.60  
% 9.43/3.60  
% 9.43/3.60  %Foreground operators:
% 9.43/3.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.43/3.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.43/3.60  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.43/3.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.43/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.43/3.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.43/3.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.43/3.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.43/3.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.43/3.60  tff('#skF_2', type, '#skF_2': $i).
% 9.43/3.60  tff('#skF_3', type, '#skF_3': $i).
% 9.43/3.60  tff('#skF_1', type, '#skF_1': $i).
% 9.43/3.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.43/3.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.43/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.43/3.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.43/3.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.43/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.43/3.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.43/3.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.43/3.60  
% 9.83/3.64  tff(f_122, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.83/3.64  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.83/3.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.83/3.64  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.83/3.64  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.83/3.64  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 9.83/3.64  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.83/3.64  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.83/3.64  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.83/3.64  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.83/3.64  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.83/3.64  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.83/3.64  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 9.83/3.64  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.83/3.64  tff(c_17150, plain, (![C_1164, A_1165, B_1166]: (v1_relat_1(C_1164) | ~m1_subset_1(C_1164, k1_zfmisc_1(k2_zfmisc_1(A_1165, B_1166))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.83/3.64  tff(c_17167, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_17150])).
% 9.83/3.64  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.83/3.64  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.83/3.64  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.83/3.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.83/3.64  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.83/3.64  tff(c_18249, plain, (![A_1249, B_1250, C_1251]: (k1_relset_1(A_1249, B_1250, C_1251)=k1_relat_1(C_1251) | ~m1_subset_1(C_1251, k1_zfmisc_1(k2_zfmisc_1(A_1249, B_1250))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.83/3.64  tff(c_18267, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_18249])).
% 9.83/3.64  tff(c_19914, plain, (![B_1349, A_1350, C_1351]: (k1_xboole_0=B_1349 | k1_relset_1(A_1350, B_1349, C_1351)=A_1350 | ~v1_funct_2(C_1351, A_1350, B_1349) | ~m1_subset_1(C_1351, k1_zfmisc_1(k2_zfmisc_1(A_1350, B_1349))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.83/3.64  tff(c_19938, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_19914])).
% 9.83/3.64  tff(c_19952, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_18267, c_19938])).
% 9.83/3.64  tff(c_19954, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_19952])).
% 9.83/3.64  tff(c_19614, plain, (![A_1337, B_1338, C_1339]: (m1_subset_1(k1_relset_1(A_1337, B_1338, C_1339), k1_zfmisc_1(A_1337)) | ~m1_subset_1(C_1339, k1_zfmisc_1(k2_zfmisc_1(A_1337, B_1338))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.83/3.64  tff(c_19676, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_18267, c_19614])).
% 9.83/3.64  tff(c_19704, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_19676])).
% 9.83/3.64  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.83/3.64  tff(c_19809, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_19704, c_16])).
% 9.83/3.64  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.83/3.64  tff(c_19812, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_19809, c_2])).
% 9.83/3.64  tff(c_19896, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_19812])).
% 9.83/3.64  tff(c_19955, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19954, c_19896])).
% 9.83/3.64  tff(c_19966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_19955])).
% 9.83/3.64  tff(c_19967, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_19952])).
% 9.83/3.64  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.83/3.64  tff(c_19998, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_19967, c_8])).
% 9.83/3.64  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.83/3.64  tff(c_19996, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19967, c_19967, c_12])).
% 9.83/3.64  tff(c_176, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.83/3.64  tff(c_184, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_176])).
% 9.83/3.64  tff(c_17174, plain, (![B_1168, A_1169]: (B_1168=A_1169 | ~r1_tarski(B_1168, A_1169) | ~r1_tarski(A_1169, B_1168))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.83/3.64  tff(c_17184, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_184, c_17174])).
% 9.83/3.64  tff(c_17214, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_17184])).
% 9.83/3.64  tff(c_20059, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19996, c_17214])).
% 9.83/3.64  tff(c_20064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19998, c_20059])).
% 9.83/3.64  tff(c_20065, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_19812])).
% 9.83/3.64  tff(c_101, plain, (![A_33]: (v1_funct_1(k2_funct_1(A_33)) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.83/3.64  tff(c_54, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.83/3.64  tff(c_98, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 9.83/3.64  tff(c_104, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_101, c_98])).
% 9.83/3.64  tff(c_107, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_104])).
% 9.83/3.64  tff(c_155, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.83/3.64  tff(c_162, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_155])).
% 9.83/3.64  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_162])).
% 9.83/3.64  tff(c_172, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 9.83/3.64  tff(c_186, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_172])).
% 9.83/3.64  tff(c_191, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.83/3.64  tff(c_204, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_191])).
% 9.83/3.64  tff(c_335, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.83/3.64  tff(c_350, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_335])).
% 9.83/3.64  tff(c_1648, plain, (![B_171, A_172, C_173]: (k1_xboole_0=B_171 | k1_relset_1(A_172, B_171, C_173)=A_172 | ~v1_funct_2(C_173, A_172, B_171) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.83/3.64  tff(c_1665, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_1648])).
% 9.83/3.64  tff(c_1677, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_350, c_1665])).
% 9.83/3.64  tff(c_1679, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1677])).
% 9.83/3.64  tff(c_578, plain, (![A_96, B_97, C_98]: (m1_subset_1(k1_relset_1(A_96, B_97, C_98), k1_zfmisc_1(A_96)) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.83/3.64  tff(c_615, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_350, c_578])).
% 9.83/3.64  tff(c_631, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_615])).
% 9.83/3.64  tff(c_635, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_631, c_16])).
% 9.83/3.64  tff(c_638, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_635, c_2])).
% 9.83/3.64  tff(c_646, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_638])).
% 9.83/3.64  tff(c_1683, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1679, c_646])).
% 9.83/3.64  tff(c_1692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1683])).
% 9.83/3.64  tff(c_1693, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1677])).
% 9.83/3.64  tff(c_1725, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_8])).
% 9.83/3.64  tff(c_1723, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1693, c_12])).
% 9.83/3.64  tff(c_211, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.83/3.64  tff(c_218, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_184, c_211])).
% 9.83/3.64  tff(c_248, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_218])).
% 9.83/3.64  tff(c_1804, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_248])).
% 9.83/3.64  tff(c_1809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1725, c_1804])).
% 9.83/3.64  tff(c_1810, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_638])).
% 9.83/3.64  tff(c_24, plain, (![A_9]: (k2_relat_1(k2_funct_1(A_9))=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.83/3.64  tff(c_22, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.83/3.64  tff(c_173, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 9.83/3.64  tff(c_481, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.83/3.64  tff(c_491, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_481])).
% 9.83/3.64  tff(c_501, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_491])).
% 9.83/3.64  tff(c_311, plain, (![A_67]: (k1_relat_1(k2_funct_1(A_67))=k2_relat_1(A_67) | ~v2_funct_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.83/3.64  tff(c_50, plain, (![A_25]: (v1_funct_2(A_25, k1_relat_1(A_25), k2_relat_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.83/3.64  tff(c_4188, plain, (![A_338]: (v1_funct_2(k2_funct_1(A_338), k2_relat_1(A_338), k2_relat_1(k2_funct_1(A_338))) | ~v1_funct_1(k2_funct_1(A_338)) | ~v1_relat_1(k2_funct_1(A_338)) | ~v2_funct_1(A_338) | ~v1_funct_1(A_338) | ~v1_relat_1(A_338))), inference(superposition, [status(thm), theory('equality')], [c_311, c_50])).
% 9.83/3.64  tff(c_4191, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_501, c_4188])).
% 9.83/3.64  tff(c_4199, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_58, c_173, c_4191])).
% 9.83/3.64  tff(c_4200, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4199])).
% 9.83/3.64  tff(c_4203, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_4200])).
% 9.83/3.64  tff(c_4207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_4203])).
% 9.83/3.64  tff(c_4209, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4199])).
% 9.83/3.64  tff(c_26, plain, (![A_9]: (k1_relat_1(k2_funct_1(A_9))=k2_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.83/3.64  tff(c_388, plain, (![A_79]: (m1_subset_1(A_79, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_79), k2_relat_1(A_79)))) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.83/3.64  tff(c_4889, plain, (![A_368]: (m1_subset_1(k2_funct_1(A_368), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_368), k2_relat_1(k2_funct_1(A_368))))) | ~v1_funct_1(k2_funct_1(A_368)) | ~v1_relat_1(k2_funct_1(A_368)) | ~v2_funct_1(A_368) | ~v1_funct_1(A_368) | ~v1_relat_1(A_368))), inference(superposition, [status(thm), theory('equality')], [c_26, c_388])).
% 9.83/3.64  tff(c_4912, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_501, c_4889])).
% 9.83/3.64  tff(c_4927, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_58, c_4209, c_173, c_4912])).
% 9.83/3.64  tff(c_4950, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_4927])).
% 9.83/3.64  tff(c_4963, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_58, c_1810, c_4950])).
% 9.83/3.64  tff(c_4965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_4963])).
% 9.83/3.64  tff(c_4966, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_218])).
% 9.83/3.64  tff(c_4970, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4966, c_60])).
% 9.83/3.64  tff(c_5174, plain, (![A_392, B_393, C_394]: (k1_relset_1(A_392, B_393, C_394)=k1_relat_1(C_394) | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.83/3.64  tff(c_5223, plain, (![C_400]: (k1_relset_1('#skF_1', '#skF_2', C_400)=k1_relat_1(C_400) | ~m1_subset_1(C_400, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4966, c_5174])).
% 9.83/3.64  tff(c_5231, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4970, c_5223])).
% 9.83/3.64  tff(c_8495, plain, (![B_601, C_602, A_603]: (k1_xboole_0=B_601 | v1_funct_2(C_602, A_603, B_601) | k1_relset_1(A_603, B_601, C_602)!=A_603 | ~m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(A_603, B_601))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.83/3.64  tff(c_8512, plain, (![C_602]: (k1_xboole_0='#skF_2' | v1_funct_2(C_602, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_602)!='#skF_1' | ~m1_subset_1(C_602, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4966, c_8495])).
% 9.83/3.64  tff(c_8574, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_8512])).
% 9.83/3.64  tff(c_5026, plain, (![B_374, A_375]: (k1_xboole_0=B_374 | k1_xboole_0=A_375 | k2_zfmisc_1(A_375, B_374)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.83/3.64  tff(c_5029, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4966, c_5026])).
% 9.83/3.64  tff(c_5050, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_5029])).
% 9.83/3.64  tff(c_8598, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8574, c_5050])).
% 9.83/3.64  tff(c_8735, plain, (![A_615]: (k2_zfmisc_1(A_615, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8574, c_8574, c_12])).
% 9.83/3.64  tff(c_6284, plain, (![B_473, C_474, A_475]: (k1_xboole_0=B_473 | v1_funct_2(C_474, A_475, B_473) | k1_relset_1(A_475, B_473, C_474)!=A_475 | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(A_475, B_473))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.83/3.64  tff(c_6301, plain, (![C_474]: (k1_xboole_0='#skF_2' | v1_funct_2(C_474, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_474)!='#skF_1' | ~m1_subset_1(C_474, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4966, c_6284])).
% 9.83/3.64  tff(c_6739, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6301])).
% 9.83/3.64  tff(c_6777, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_6739, c_8])).
% 9.83/3.64  tff(c_6775, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6739, c_6739, c_12])).
% 9.83/3.64  tff(c_5097, plain, (![A_382, B_383, C_384]: (k2_relset_1(A_382, B_383, C_384)=k2_relat_1(C_384) | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(A_382, B_383))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.83/3.64  tff(c_5127, plain, (![C_388]: (k2_relset_1('#skF_1', '#skF_2', C_388)=k2_relat_1(C_388) | ~m1_subset_1(C_388, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4966, c_5097])).
% 9.83/3.64  tff(c_5130, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4970, c_5127])).
% 9.83/3.64  tff(c_5136, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_5130])).
% 9.83/3.64  tff(c_5268, plain, (![A_405]: (m1_subset_1(A_405, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_405), k2_relat_1(A_405)))) | ~v1_funct_1(A_405) | ~v1_relat_1(A_405))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.83/3.64  tff(c_5283, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5136, c_5268])).
% 9.83/3.64  tff(c_5295, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_5283])).
% 9.83/3.64  tff(c_5313, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_5295, c_16])).
% 9.83/3.64  tff(c_5325, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_5313, c_2])).
% 9.83/3.64  tff(c_5461, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5325])).
% 9.83/3.64  tff(c_6912, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6775, c_5461])).
% 9.83/3.64  tff(c_6917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6777, c_6912])).
% 9.83/3.64  tff(c_6919, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_6301])).
% 9.83/3.64  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.83/3.64  tff(c_6572, plain, (![B_492, A_493, C_494]: (k1_xboole_0=B_492 | k1_relset_1(A_493, B_492, C_494)=A_493 | ~v1_funct_2(C_494, A_493, B_492) | ~m1_subset_1(C_494, k1_zfmisc_1(k2_zfmisc_1(A_493, B_492))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.83/3.64  tff(c_7292, plain, (![B_539, A_540, A_541]: (k1_xboole_0=B_539 | k1_relset_1(A_540, B_539, A_541)=A_540 | ~v1_funct_2(A_541, A_540, B_539) | ~r1_tarski(A_541, k2_zfmisc_1(A_540, B_539)))), inference(resolution, [status(thm)], [c_18, c_6572])).
% 9.83/3.64  tff(c_7313, plain, (![A_541]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', A_541)='#skF_1' | ~v1_funct_2(A_541, '#skF_1', '#skF_2') | ~r1_tarski(A_541, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4966, c_7292])).
% 9.83/3.64  tff(c_7342, plain, (![A_542]: (k1_relset_1('#skF_1', '#skF_2', A_542)='#skF_1' | ~v1_funct_2(A_542, '#skF_1', '#skF_2') | ~r1_tarski(A_542, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_6919, c_7313])).
% 9.83/3.64  tff(c_7352, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_7342])).
% 9.83/3.64  tff(c_7360, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5231, c_7352])).
% 9.83/3.64  tff(c_5556, plain, (![A_431, B_432, C_433]: (m1_subset_1(k1_relset_1(A_431, B_432, C_433), k1_zfmisc_1(A_431)) | ~m1_subset_1(C_433, k1_zfmisc_1(k2_zfmisc_1(A_431, B_432))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.83/3.64  tff(c_5614, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5231, c_5556])).
% 9.83/3.64  tff(c_5635, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4970, c_4966, c_5614])).
% 9.83/3.64  tff(c_5639, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_5635, c_16])).
% 9.83/3.64  tff(c_5642, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_5639, c_2])).
% 9.83/3.64  tff(c_5663, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5642])).
% 9.83/3.64  tff(c_7361, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7360, c_5663])).
% 9.83/3.64  tff(c_7374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7361])).
% 9.83/3.64  tff(c_7375, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_5642])).
% 9.83/3.64  tff(c_7380, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7375, c_5461])).
% 9.83/3.64  tff(c_7390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4966, c_7380])).
% 9.83/3.64  tff(c_7391, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_5325])).
% 9.83/3.64  tff(c_8759, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8735, c_7391])).
% 9.83/3.64  tff(c_8794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8598, c_8759])).
% 9.83/3.64  tff(c_8796, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_8512])).
% 9.83/3.64  tff(c_8893, plain, (![B_622, A_623, C_624]: (k1_xboole_0=B_622 | k1_relset_1(A_623, B_622, C_624)=A_623 | ~v1_funct_2(C_624, A_623, B_622) | ~m1_subset_1(C_624, k1_zfmisc_1(k2_zfmisc_1(A_623, B_622))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.83/3.64  tff(c_8910, plain, (![C_624]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_624)='#skF_1' | ~v1_funct_2(C_624, '#skF_1', '#skF_2') | ~m1_subset_1(C_624, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4966, c_8893])).
% 9.83/3.64  tff(c_9374, plain, (![C_649]: (k1_relset_1('#skF_1', '#skF_2', C_649)='#skF_1' | ~v1_funct_2(C_649, '#skF_1', '#skF_2') | ~m1_subset_1(C_649, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_8796, c_8910])).
% 9.83/3.64  tff(c_9385, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4970, c_9374])).
% 9.83/3.64  tff(c_9395, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5231, c_9385])).
% 9.83/3.64  tff(c_8127, plain, (![A_582, B_583, C_584]: (m1_subset_1(k1_relset_1(A_582, B_583, C_584), k1_zfmisc_1(A_582)) | ~m1_subset_1(C_584, k1_zfmisc_1(k2_zfmisc_1(A_582, B_583))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.83/3.64  tff(c_8185, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5231, c_8127])).
% 9.83/3.64  tff(c_8209, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4970, c_4966, c_8185])).
% 9.83/3.64  tff(c_8243, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_8209, c_16])).
% 9.83/3.64  tff(c_8246, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8243, c_2])).
% 9.83/3.64  tff(c_8253, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_8246])).
% 9.83/3.64  tff(c_9400, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9395, c_8253])).
% 9.83/3.64  tff(c_9412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9400])).
% 9.83/3.64  tff(c_9413, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_8246])).
% 9.83/3.64  tff(c_5073, plain, (![A_380]: (k2_relat_1(k2_funct_1(A_380))=k1_relat_1(A_380) | ~v2_funct_1(A_380) | ~v1_funct_1(A_380) | ~v1_relat_1(A_380))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.83/3.64  tff(c_11806, plain, (![A_788]: (v1_funct_2(k2_funct_1(A_788), k1_relat_1(k2_funct_1(A_788)), k1_relat_1(A_788)) | ~v1_funct_1(k2_funct_1(A_788)) | ~v1_relat_1(k2_funct_1(A_788)) | ~v2_funct_1(A_788) | ~v1_funct_1(A_788) | ~v1_relat_1(A_788))), inference(superposition, [status(thm), theory('equality')], [c_5073, c_50])).
% 9.83/3.64  tff(c_11812, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9413, c_11806])).
% 9.83/3.64  tff(c_11823, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_58, c_173, c_11812])).
% 9.83/3.64  tff(c_11826, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_11823])).
% 9.83/3.64  tff(c_11829, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_11826])).
% 9.83/3.64  tff(c_11833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_11829])).
% 9.83/3.64  tff(c_11835, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_11823])).
% 9.83/3.64  tff(c_12493, plain, (![A_827]: (m1_subset_1(k2_funct_1(A_827), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_827), k2_relat_1(k2_funct_1(A_827))))) | ~v1_funct_1(k2_funct_1(A_827)) | ~v1_relat_1(k2_funct_1(A_827)) | ~v2_funct_1(A_827) | ~v1_funct_1(A_827) | ~v1_relat_1(A_827))), inference(superposition, [status(thm), theory('equality')], [c_26, c_5268])).
% 9.83/3.64  tff(c_12516, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5136, c_12493])).
% 9.83/3.64  tff(c_12531, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_58, c_11835, c_173, c_12516])).
% 9.83/3.64  tff(c_12554, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_12531])).
% 9.83/3.64  tff(c_12567, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_58, c_9413, c_12554])).
% 9.83/3.64  tff(c_12569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_12567])).
% 9.83/3.64  tff(c_12571, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5029])).
% 9.83/3.64  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.83/3.64  tff(c_12578, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12571, c_12571, c_14])).
% 9.83/3.64  tff(c_12570, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5029])).
% 9.83/3.64  tff(c_12601, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12571, c_12571, c_12570])).
% 9.83/3.64  tff(c_12602, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_12601])).
% 9.83/3.64  tff(c_12605, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_12602, c_186])).
% 9.83/3.64  tff(c_12667, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12578, c_12605])).
% 9.83/3.64  tff(c_12577, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12571, c_12571, c_12])).
% 9.83/3.64  tff(c_12740, plain, (![A_840, B_841, C_842]: (k2_relset_1(A_840, B_841, C_842)=k2_relat_1(C_842) | ~m1_subset_1(C_842, k1_zfmisc_1(k2_zfmisc_1(A_840, B_841))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.83/3.64  tff(c_12772, plain, (![A_846, C_847]: (k2_relset_1(A_846, '#skF_3', C_847)=k2_relat_1(C_847) | ~m1_subset_1(C_847, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12577, c_12740])).
% 9.83/3.64  tff(c_12780, plain, (![A_848]: (k2_relset_1(A_848, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4970, c_12772])).
% 9.83/3.64  tff(c_12606, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12602, c_12602, c_56])).
% 9.83/3.64  tff(c_12784, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_12780, c_12606])).
% 9.83/3.64  tff(c_12687, plain, (![A_836]: (k1_relat_1(k2_funct_1(A_836))=k2_relat_1(A_836) | ~v2_funct_1(A_836) | ~v1_funct_1(A_836) | ~v1_relat_1(A_836))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.83/3.64  tff(c_14133, plain, (![A_959]: (v1_funct_2(k2_funct_1(A_959), k2_relat_1(A_959), k2_relat_1(k2_funct_1(A_959))) | ~v1_funct_1(k2_funct_1(A_959)) | ~v1_relat_1(k2_funct_1(A_959)) | ~v2_funct_1(A_959) | ~v1_funct_1(A_959) | ~v1_relat_1(A_959))), inference(superposition, [status(thm), theory('equality')], [c_12687, c_50])).
% 9.83/3.64  tff(c_14136, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12784, c_14133])).
% 9.83/3.64  tff(c_14144, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_58, c_173, c_14136])).
% 9.83/3.64  tff(c_14162, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_14144])).
% 9.83/3.64  tff(c_14165, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_14162])).
% 9.83/3.64  tff(c_14169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_14165])).
% 9.83/3.64  tff(c_14171, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_14144])).
% 9.83/3.64  tff(c_12756, plain, (![A_843, B_844, C_845]: (k1_relset_1(A_843, B_844, C_845)=k1_relat_1(C_845) | ~m1_subset_1(C_845, k1_zfmisc_1(k2_zfmisc_1(A_843, B_844))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.83/3.64  tff(c_12877, plain, (![B_859, C_860]: (k1_relset_1('#skF_3', B_859, C_860)=k1_relat_1(C_860) | ~m1_subset_1(C_860, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12578, c_12756])).
% 9.83/3.64  tff(c_12883, plain, (![B_859]: (k1_relset_1('#skF_3', B_859, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4970, c_12877])).
% 9.83/3.64  tff(c_40, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.83/3.64  tff(c_66, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 9.83/3.64  tff(c_12921, plain, (![C_866, B_867]: (v1_funct_2(C_866, '#skF_3', B_867) | k1_relset_1('#skF_3', B_867, C_866)!='#skF_3' | ~m1_subset_1(C_866, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12571, c_12571, c_12571, c_12571, c_66])).
% 9.83/3.64  tff(c_12923, plain, (![B_867]: (v1_funct_2('#skF_3', '#skF_3', B_867) | k1_relset_1('#skF_3', B_867, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_4970, c_12921])).
% 9.83/3.64  tff(c_12928, plain, (![B_867]: (v1_funct_2('#skF_3', '#skF_3', B_867) | k1_relat_1('#skF_3')!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12883, c_12923])).
% 9.83/3.64  tff(c_12945, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_12928])).
% 9.83/3.64  tff(c_12946, plain, (![A_869, B_870, C_871]: (m1_subset_1(k1_relset_1(A_869, B_870, C_871), k1_zfmisc_1(A_869)) | ~m1_subset_1(C_871, k1_zfmisc_1(k2_zfmisc_1(A_869, B_870))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.83/3.64  tff(c_12983, plain, (![B_859]: (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_859))))), inference(superposition, [status(thm), theory('equality')], [c_12883, c_12946])).
% 9.83/3.64  tff(c_13004, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4970, c_12578, c_12983])).
% 9.83/3.64  tff(c_13029, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_13004, c_16])).
% 9.83/3.64  tff(c_223, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_211])).
% 9.83/3.64  tff(c_12575, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12571, c_12571, c_223])).
% 9.83/3.64  tff(c_13038, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_13029, c_12575])).
% 9.83/3.64  tff(c_13050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12945, c_13038])).
% 9.83/3.64  tff(c_13052, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_12928])).
% 9.83/3.64  tff(c_12711, plain, (![A_838]: (m1_subset_1(A_838, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_838), k2_relat_1(A_838)))) | ~v1_funct_1(A_838) | ~v1_relat_1(A_838))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.83/3.64  tff(c_14621, plain, (![A_987]: (m1_subset_1(k2_funct_1(A_987), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_987)), k1_relat_1(A_987)))) | ~v1_funct_1(k2_funct_1(A_987)) | ~v1_relat_1(k2_funct_1(A_987)) | ~v2_funct_1(A_987) | ~v1_funct_1(A_987) | ~v1_relat_1(A_987))), inference(superposition, [status(thm), theory('equality')], [c_24, c_12711])).
% 9.83/3.64  tff(c_14647, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13052, c_14621])).
% 9.83/3.64  tff(c_14663, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_64, c_58, c_14171, c_173, c_12577, c_14647])).
% 9.83/3.64  tff(c_14665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12667, c_14663])).
% 9.83/3.64  tff(c_14666, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_12601])).
% 9.83/3.64  tff(c_14771, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14666, c_14666, c_12577])).
% 9.83/3.64  tff(c_14676, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14666, c_186])).
% 9.83/3.64  tff(c_14816, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14771, c_14676])).
% 9.83/3.64  tff(c_14674, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14666, c_204])).
% 9.83/3.64  tff(c_14681, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14666, c_64])).
% 9.83/3.64  tff(c_14680, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14666, c_58])).
% 9.83/3.64  tff(c_14672, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14666, c_14666, c_4970])).
% 9.83/3.64  tff(c_14906, plain, (![A_1004, B_1005, C_1006]: (k1_relset_1(A_1004, B_1005, C_1006)=k1_relat_1(C_1006) | ~m1_subset_1(C_1006, k1_zfmisc_1(k2_zfmisc_1(A_1004, B_1005))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.83/3.64  tff(c_14963, plain, (![A_1013, C_1014]: (k1_relset_1(A_1013, '#skF_1', C_1014)=k1_relat_1(C_1014) | ~m1_subset_1(C_1014, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_14771, c_14906])).
% 9.83/3.64  tff(c_14969, plain, (![A_1013]: (k1_relset_1(A_1013, '#skF_1', '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_14672, c_14963])).
% 9.83/3.64  tff(c_15028, plain, (![A_1024, B_1025, C_1026]: (m1_subset_1(k1_relset_1(A_1024, B_1025, C_1026), k1_zfmisc_1(A_1024)) | ~m1_subset_1(C_1026, k1_zfmisc_1(k2_zfmisc_1(A_1024, B_1025))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.83/3.64  tff(c_15059, plain, (![A_1013]: (m1_subset_1(k1_relat_1('#skF_1'), k1_zfmisc_1(A_1013)) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_1013, '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_14969, c_15028])).
% 9.83/3.64  tff(c_15079, plain, (![A_1027]: (m1_subset_1(k1_relat_1('#skF_1'), k1_zfmisc_1(A_1027)))), inference(demodulation, [status(thm), theory('equality')], [c_14672, c_14771, c_15059])).
% 9.83/3.64  tff(c_15117, plain, (![A_1028]: (r1_tarski(k1_relat_1('#skF_1'), A_1028))), inference(resolution, [status(thm)], [c_15079, c_16])).
% 9.83/3.64  tff(c_14821, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14666, c_14666, c_12575])).
% 9.83/3.64  tff(c_15142, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_15117, c_14821])).
% 9.83/3.64  tff(c_14677, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14666, c_173])).
% 9.83/3.64  tff(c_14874, plain, (![A_999]: (k2_relat_1(k2_funct_1(A_999))=k1_relat_1(A_999) | ~v2_funct_1(A_999) | ~v1_funct_1(A_999) | ~v1_relat_1(A_999))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.83/3.64  tff(c_16473, plain, (![A_1135]: (v1_funct_2(k2_funct_1(A_1135), k1_relat_1(k2_funct_1(A_1135)), k1_relat_1(A_1135)) | ~v1_funct_1(k2_funct_1(A_1135)) | ~v1_relat_1(k2_funct_1(A_1135)) | ~v2_funct_1(A_1135) | ~v1_funct_1(A_1135) | ~v1_relat_1(A_1135))), inference(superposition, [status(thm), theory('equality')], [c_14874, c_50])).
% 9.83/3.64  tff(c_16476, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15142, c_16473])).
% 9.83/3.64  tff(c_16484, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14674, c_14681, c_14680, c_14677, c_16476])).
% 9.83/3.64  tff(c_16485, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_16484])).
% 9.83/3.64  tff(c_16488, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_16485])).
% 9.83/3.64  tff(c_16492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14674, c_14681, c_16488])).
% 9.83/3.64  tff(c_16494, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_16484])).
% 9.83/3.64  tff(c_15076, plain, (![A_1013]: (m1_subset_1(k1_relat_1('#skF_1'), k1_zfmisc_1(A_1013)))), inference(demodulation, [status(thm), theory('equality')], [c_14672, c_14771, c_15059])).
% 9.83/3.64  tff(c_15182, plain, (![A_1031]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_1031)))), inference(demodulation, [status(thm), theory('equality')], [c_15142, c_15076])).
% 9.83/3.64  tff(c_34, plain, (![A_19, B_20, C_21]: (k2_relset_1(A_19, B_20, C_21)=k2_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.83/3.64  tff(c_15306, plain, (![A_1039, B_1040]: (k2_relset_1(A_1039, B_1040, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_15182, c_34])).
% 9.83/3.64  tff(c_14678, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14666, c_56])).
% 9.83/3.64  tff(c_15310, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_15306, c_14678])).
% 9.83/3.64  tff(c_14918, plain, (![A_1007]: (m1_subset_1(A_1007, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1007), k2_relat_1(A_1007)))) | ~v1_funct_1(A_1007) | ~v1_relat_1(A_1007))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.83/3.64  tff(c_17056, plain, (![A_1161]: (m1_subset_1(k2_funct_1(A_1161), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1161), k2_relat_1(k2_funct_1(A_1161))))) | ~v1_funct_1(k2_funct_1(A_1161)) | ~v1_relat_1(k2_funct_1(A_1161)) | ~v2_funct_1(A_1161) | ~v1_funct_1(A_1161) | ~v1_relat_1(A_1161))), inference(superposition, [status(thm), theory('equality')], [c_26, c_14918])).
% 9.83/3.64  tff(c_17079, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_1'))))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15310, c_17056])).
% 9.83/3.64  tff(c_17094, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_14674, c_14681, c_14680, c_16494, c_14677, c_17079])).
% 9.83/3.64  tff(c_17117, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_1')))) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_17094])).
% 9.83/3.64  tff(c_17130, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14674, c_14681, c_14680, c_14771, c_15142, c_17117])).
% 9.83/3.64  tff(c_17132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14816, c_17130])).
% 9.83/3.64  tff(c_17133, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_172])).
% 9.83/3.64  tff(c_18935, plain, (![B_1311, A_1312, C_1313]: (k1_xboole_0=B_1311 | k1_relset_1(A_1312, B_1311, C_1313)=A_1312 | ~v1_funct_2(C_1313, A_1312, B_1311) | ~m1_subset_1(C_1313, k1_zfmisc_1(k2_zfmisc_1(A_1312, B_1311))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.83/3.64  tff(c_18955, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_18935])).
% 9.83/3.64  tff(c_18971, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_18267, c_18955])).
% 9.83/3.64  tff(c_18973, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_18971])).
% 9.83/3.64  tff(c_18726, plain, (![A_1303, B_1304, C_1305]: (m1_subset_1(k1_relset_1(A_1303, B_1304, C_1305), k1_zfmisc_1(A_1303)) | ~m1_subset_1(C_1305, k1_zfmisc_1(k2_zfmisc_1(A_1303, B_1304))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.83/3.64  tff(c_18787, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_18267, c_18726])).
% 9.83/3.64  tff(c_18812, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_18787])).
% 9.83/3.64  tff(c_18816, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_18812, c_16])).
% 9.83/3.64  tff(c_18819, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_18816, c_2])).
% 9.83/3.64  tff(c_18883, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_18819])).
% 9.83/3.64  tff(c_18974, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18973, c_18883])).
% 9.83/3.64  tff(c_18987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_18974])).
% 9.83/3.64  tff(c_18988, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_18971])).
% 9.83/3.64  tff(c_19020, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_18988, c_8])).
% 9.83/3.64  tff(c_19018, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18988, c_18988, c_12])).
% 9.83/3.64  tff(c_18268, plain, (![A_1252, B_1253, C_1254]: (k2_relset_1(A_1252, B_1253, C_1254)=k2_relat_1(C_1254) | ~m1_subset_1(C_1254, k1_zfmisc_1(k2_zfmisc_1(A_1252, B_1253))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.83/3.64  tff(c_18278, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_18268])).
% 9.83/3.64  tff(c_18287, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_18278])).
% 9.83/3.64  tff(c_18445, plain, (![A_1277]: (m1_subset_1(A_1277, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1277), k2_relat_1(A_1277)))) | ~v1_funct_1(A_1277) | ~v1_relat_1(A_1277))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.83/3.64  tff(c_18460, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18287, c_18445])).
% 9.83/3.64  tff(c_18472, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_17167, c_64, c_18460])).
% 9.83/3.64  tff(c_18490, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_18472, c_16])).
% 9.83/3.64  tff(c_18502, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_18490, c_2])).
% 9.83/3.64  tff(c_18621, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_18502])).
% 9.83/3.64  tff(c_19062, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19018, c_18621])).
% 9.83/3.64  tff(c_19070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19020, c_19062])).
% 9.83/3.64  tff(c_19071, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_18819])).
% 9.83/3.64  tff(c_17134, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_172])).
% 9.83/3.64  tff(c_17165, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_17134, c_17150])).
% 9.83/3.64  tff(c_17410, plain, (![A_1197, B_1198, C_1199]: (k2_relset_1(A_1197, B_1198, C_1199)=k2_relat_1(C_1199) | ~m1_subset_1(C_1199, k1_zfmisc_1(k2_zfmisc_1(A_1197, B_1198))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.83/3.64  tff(c_17423, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_17410])).
% 9.83/3.64  tff(c_17434, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_17423])).
% 9.83/3.64  tff(c_17303, plain, (![A_1183, B_1184, C_1185]: (k1_relset_1(A_1183, B_1184, C_1185)=k1_relat_1(C_1185) | ~m1_subset_1(C_1185, k1_zfmisc_1(k2_zfmisc_1(A_1183, B_1184))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.83/3.64  tff(c_17320, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_17134, c_17303])).
% 9.83/3.64  tff(c_18033, plain, (![B_1240, C_1241, A_1242]: (k1_xboole_0=B_1240 | v1_funct_2(C_1241, A_1242, B_1240) | k1_relset_1(A_1242, B_1240, C_1241)!=A_1242 | ~m1_subset_1(C_1241, k1_zfmisc_1(k2_zfmisc_1(A_1242, B_1240))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.83/3.64  tff(c_18050, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_17134, c_18033])).
% 9.83/3.64  tff(c_18072, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17320, c_18050])).
% 9.83/3.64  tff(c_18073, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_17133, c_18072])).
% 9.83/3.64  tff(c_18078, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_18073])).
% 9.83/3.64  tff(c_18081, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_18078])).
% 9.83/3.64  tff(c_18084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17167, c_64, c_58, c_17434, c_18081])).
% 9.83/3.64  tff(c_18085, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_18073])).
% 9.83/3.64  tff(c_18110, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_18085, c_8])).
% 9.83/3.64  tff(c_18108, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18085, c_18085, c_12])).
% 9.83/3.64  tff(c_17138, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_17134, c_16])).
% 9.83/3.64  tff(c_17183, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_17138, c_17174])).
% 9.83/3.64  tff(c_17270, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_17183])).
% 9.83/3.64  tff(c_18168, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18108, c_17270])).
% 9.83/3.64  tff(c_18173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18110, c_18168])).
% 9.83/3.64  tff(c_18174, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_17183])).
% 9.83/3.64  tff(c_18177, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_18174, c_17134])).
% 9.83/3.64  tff(c_18301, plain, (![C_1255]: (k1_relset_1('#skF_2', '#skF_1', C_1255)=k1_relat_1(C_1255) | ~m1_subset_1(C_1255, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_18174, c_18249])).
% 9.83/3.64  tff(c_18309, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_18177, c_18301])).
% 9.83/3.64  tff(c_18784, plain, (m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_18309, c_18726])).
% 9.83/3.64  tff(c_18810, plain, (m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18177, c_18174, c_18784])).
% 9.83/3.64  tff(c_18831, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_18810, c_16])).
% 9.83/3.64  tff(c_18880, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_18831, c_2])).
% 9.83/3.64  tff(c_19182, plain, (~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_18880])).
% 9.83/3.64  tff(c_19185, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_19182])).
% 9.83/3.64  tff(c_19188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17167, c_64, c_58, c_6, c_18287, c_19185])).
% 9.83/3.64  tff(c_19189, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_18880])).
% 9.83/3.64  tff(c_19208, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_19189, c_50])).
% 9.83/3.64  tff(c_19221, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_17165, c_173, c_19208])).
% 9.83/3.64  tff(c_19237, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_19221])).
% 9.83/3.64  tff(c_19239, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17167, c_64, c_58, c_19071, c_19237])).
% 9.83/3.64  tff(c_19241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17133, c_19239])).
% 9.83/3.64  tff(c_19242, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_18502])).
% 9.83/3.64  tff(c_20070, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20065, c_19242])).
% 9.83/3.64  tff(c_20113, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20070, c_17214])).
% 9.83/3.64  tff(c_20118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_20113])).
% 9.83/3.64  tff(c_20119, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_17184])).
% 9.83/3.64  tff(c_20123, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20119, c_60])).
% 9.83/3.64  tff(c_20373, plain, (![A_1380, B_1381, C_1382]: (k2_relset_1(A_1380, B_1381, C_1382)=k2_relat_1(C_1382) | ~m1_subset_1(C_1382, k1_zfmisc_1(k2_zfmisc_1(A_1380, B_1381))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.83/3.64  tff(c_20419, plain, (![C_1387]: (k2_relset_1('#skF_1', '#skF_2', C_1387)=k2_relat_1(C_1387) | ~m1_subset_1(C_1387, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_20119, c_20373])).
% 9.83/3.64  tff(c_20422, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20123, c_20419])).
% 9.83/3.64  tff(c_20428, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_20422])).
% 9.83/3.64  tff(c_20252, plain, (![A_1366, B_1367, C_1368]: (k1_relset_1(A_1366, B_1367, C_1368)=k1_relat_1(C_1368) | ~m1_subset_1(C_1368, k1_zfmisc_1(k2_zfmisc_1(A_1366, B_1367))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.83/3.64  tff(c_20269, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_17134, c_20252])).
% 9.83/3.64  tff(c_21283, plain, (![B_1427, C_1428, A_1429]: (k1_xboole_0=B_1427 | v1_funct_2(C_1428, A_1429, B_1427) | k1_relset_1(A_1429, B_1427, C_1428)!=A_1429 | ~m1_subset_1(C_1428, k1_zfmisc_1(k2_zfmisc_1(A_1429, B_1427))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.83/3.64  tff(c_21300, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_17134, c_21283])).
% 9.83/3.64  tff(c_21316, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20269, c_21300])).
% 9.83/3.64  tff(c_21317, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_17133, c_21316])).
% 9.83/3.64  tff(c_21320, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_21317])).
% 9.83/3.64  tff(c_21323, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_21320])).
% 9.83/3.64  tff(c_21326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17167, c_64, c_58, c_20428, c_21323])).
% 9.83/3.64  tff(c_21327, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_21317])).
% 9.83/3.64  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.83/3.64  tff(c_20130, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_20119, c_10])).
% 9.83/3.64  tff(c_20185, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_20130])).
% 9.83/3.64  tff(c_21344, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21327, c_20185])).
% 9.83/3.64  tff(c_21352, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21327, c_21327, c_14])).
% 9.83/3.64  tff(c_21422, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21352, c_20119])).
% 9.83/3.64  tff(c_21424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21344, c_21422])).
% 9.83/3.64  tff(c_21426, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_20130])).
% 9.83/3.64  tff(c_21436, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21426, c_21426, c_14])).
% 9.83/3.64  tff(c_21425, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_20130])).
% 9.83/3.64  tff(c_21454, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21426, c_21426, c_21425])).
% 9.83/3.64  tff(c_21455, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_21454])).
% 9.83/3.64  tff(c_21437, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_21426, c_8])).
% 9.83/3.64  tff(c_21456, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_17183])).
% 9.83/3.64  tff(c_21603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21437, c_21436, c_21455, c_21456])).
% 9.83/3.64  tff(c_21604, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_17183])).
% 9.83/3.64  tff(c_21643, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21436, c_21455, c_21604])).
% 9.83/3.64  tff(c_21675, plain, (![A_1441]: (k2_relat_1(k2_funct_1(A_1441))=k1_relat_1(A_1441) | ~v2_funct_1(A_1441) | ~v1_funct_1(A_1441) | ~v1_relat_1(A_1441))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.83/3.64  tff(c_21687, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21643, c_21675])).
% 9.83/3.64  tff(c_21691, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17167, c_64, c_58, c_21687])).
% 9.83/3.64  tff(c_21435, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21426, c_21426, c_12])).
% 9.83/3.64  tff(c_21761, plain, (![A_1451, B_1452, C_1453]: (k2_relset_1(A_1451, B_1452, C_1453)=k2_relat_1(C_1453) | ~m1_subset_1(C_1453, k1_zfmisc_1(k2_zfmisc_1(A_1451, B_1452))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.83/3.64  tff(c_21800, plain, (![A_1459, C_1460]: (k2_relset_1(A_1459, '#skF_3', C_1460)=k2_relat_1(C_1460) | ~m1_subset_1(C_1460, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_21435, c_21761])).
% 9.83/3.64  tff(c_21802, plain, (![A_1459]: (k2_relset_1(A_1459, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_20123, c_21800])).
% 9.83/3.64  tff(c_21809, plain, (![A_1461]: (k2_relset_1(A_1461, '#skF_3', '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21691, c_21802])).
% 9.83/3.64  tff(c_21610, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21455, c_21455, c_56])).
% 9.83/3.64  tff(c_21816, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_21809, c_21610])).
% 9.83/3.64  tff(c_21907, plain, (![A_1468, B_1469, C_1470]: (k1_relset_1(A_1468, B_1469, C_1470)=k1_relat_1(C_1470) | ~m1_subset_1(C_1470, k1_zfmisc_1(k2_zfmisc_1(A_1468, B_1469))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.83/3.64  tff(c_21919, plain, (![B_1471, C_1472]: (k1_relset_1('#skF_3', B_1471, C_1472)=k1_relat_1(C_1472) | ~m1_subset_1(C_1472, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_21436, c_21907])).
% 9.83/3.64  tff(c_21921, plain, (![B_1471]: (k1_relset_1('#skF_3', B_1471, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_20123, c_21919])).
% 9.83/3.64  tff(c_21926, plain, (![B_1471]: (k1_relset_1('#skF_3', B_1471, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21816, c_21921])).
% 9.83/3.64  tff(c_22042, plain, (![C_1487, B_1488]: (v1_funct_2(C_1487, '#skF_3', B_1488) | k1_relset_1('#skF_3', B_1488, C_1487)!='#skF_3' | ~m1_subset_1(C_1487, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_21426, c_21426, c_21426, c_21426, c_66])).
% 9.83/3.64  tff(c_22044, plain, (![B_1488]: (v1_funct_2('#skF_3', '#skF_3', B_1488) | k1_relset_1('#skF_3', B_1488, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_20123, c_22042])).
% 9.83/3.64  tff(c_22050, plain, (![B_1488]: (v1_funct_2('#skF_3', '#skF_3', B_1488))), inference(demodulation, [status(thm), theory('equality')], [c_21926, c_22044])).
% 9.83/3.64  tff(c_21609, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21455, c_17133])).
% 9.83/3.64  tff(c_21701, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21643, c_21609])).
% 9.83/3.64  tff(c_22055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22050, c_21701])).
% 9.83/3.64  tff(c_22056, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_21454])).
% 9.83/3.64  tff(c_22057, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_21454])).
% 9.83/3.64  tff(c_22078, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22056, c_22057])).
% 9.83/3.64  tff(c_36, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_22, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.83/3.64  tff(c_67, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_36])).
% 9.83/3.64  tff(c_20139, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_67])).
% 9.83/3.64  tff(c_20142, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_20139])).
% 9.83/3.64  tff(c_20146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_20142])).
% 9.83/3.64  tff(c_20147, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22)), inference(splitRight, [status(thm)], [c_67])).
% 9.83/3.64  tff(c_21428, plain, (![A_22]: (v1_funct_2('#skF_3', A_22, '#skF_3') | A_22='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21426, c_21426, c_21426, c_20147])).
% 9.83/3.64  tff(c_22259, plain, (![A_1499]: (v1_funct_2('#skF_1', A_1499, '#skF_1') | A_1499='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22056, c_22056, c_22056, c_21428])).
% 9.83/3.64  tff(c_22125, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22056, c_22056, c_21435])).
% 9.83/3.64  tff(c_22067, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22056, c_17134])).
% 9.83/3.64  tff(c_22183, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22125, c_22067])).
% 9.83/3.64  tff(c_22187, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_22183, c_16])).
% 9.83/3.64  tff(c_17189, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_17174])).
% 9.83/3.64  tff(c_21432, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21426, c_21426, c_17189])).
% 9.83/3.64  tff(c_22143, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22056, c_22056, c_21432])).
% 9.83/3.64  tff(c_22198, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_22187, c_22143])).
% 9.83/3.64  tff(c_22068, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22056, c_17133])).
% 9.83/3.64  tff(c_22204, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22198, c_22068])).
% 9.83/3.64  tff(c_22262, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_22259, c_22204])).
% 9.83/3.64  tff(c_22266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22078, c_22262])).
% 9.83/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.83/3.64  
% 9.83/3.64  Inference rules
% 9.83/3.64  ----------------------
% 9.83/3.64  #Ref     : 0
% 9.83/3.64  #Sup     : 4660
% 9.83/3.64  #Fact    : 0
% 9.83/3.64  #Define  : 0
% 9.83/3.64  #Split   : 63
% 9.83/3.64  #Chain   : 0
% 9.83/3.64  #Close   : 0
% 9.83/3.64  
% 9.83/3.64  Ordering : KBO
% 9.83/3.64  
% 9.83/3.64  Simplification rules
% 9.83/3.64  ----------------------
% 9.83/3.64  #Subsume      : 451
% 9.83/3.64  #Demod        : 6578
% 9.83/3.64  #Tautology    : 2494
% 9.83/3.64  #SimpNegUnit  : 56
% 9.83/3.64  #BackRed      : 651
% 9.83/3.64  
% 9.83/3.64  #Partial instantiations: 0
% 9.83/3.64  #Strategies tried      : 1
% 9.83/3.64  
% 9.83/3.64  Timing (in seconds)
% 9.83/3.64  ----------------------
% 9.83/3.65  Preprocessing        : 0.34
% 9.83/3.65  Parsing              : 0.18
% 9.83/3.65  CNF conversion       : 0.02
% 9.83/3.65  Main loop            : 2.45
% 9.83/3.65  Inferencing          : 0.79
% 9.83/3.65  Reduction            : 0.92
% 9.83/3.65  Demodulation         : 0.67
% 9.83/3.65  BG Simplification    : 0.09
% 9.83/3.65  Subsumption          : 0.45
% 9.83/3.65  Abstraction          : 0.11
% 9.83/3.65  MUC search           : 0.00
% 9.83/3.65  Cooper               : 0.00
% 9.83/3.65  Total                : 2.93
% 9.83/3.65  Index Insertion      : 0.00
% 9.83/3.65  Index Deletion       : 0.00
% 9.83/3.65  Index Matching       : 0.00
% 9.83/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
