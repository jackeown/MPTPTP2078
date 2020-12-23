%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:49 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 505 expanded)
%              Number of leaves         :   44 ( 182 expanded)
%              Depth                    :   17
%              Number of atoms          :  227 (1297 expanded)
%              Number of equality atoms :   55 ( 195 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_194,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_154,axiom,(
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

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_177,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_24,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_94,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_254,plain,(
    ! [B_85,A_86] :
      ( v1_relat_1(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_260,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_94,c_254])).

tff(c_264,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_260])).

tff(c_98,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_92,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_7859,plain,(
    ! [A_9705] :
      ( k4_relat_1(A_9705) = k2_funct_1(A_9705)
      | ~ v2_funct_1(A_9705)
      | ~ v1_funct_1(A_9705)
      | ~ v1_relat_1(A_9705) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7862,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_7859])).

tff(c_7865,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_98,c_7862])).

tff(c_22,plain,(
    ! [A_14] :
      ( v1_relat_1(k4_relat_1(A_14))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7875,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7865,c_22])).

tff(c_7883,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_7875])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_8658,plain,(
    ! [A_9753,B_9754,C_9755] :
      ( k2_relset_1(A_9753,B_9754,C_9755) = k2_relat_1(C_9755)
      | ~ m1_subset_1(C_9755,k1_zfmisc_1(k2_zfmisc_1(A_9753,B_9754))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8677,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_8658])).

tff(c_8685,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_8677])).

tff(c_32,plain,(
    ! [A_19] :
      ( k1_relat_1(k4_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_7872,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7865,c_32])).

tff(c_7881,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_7872])).

tff(c_8698,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8685,c_7881])).

tff(c_8422,plain,(
    ! [A_9728,B_9729,C_9730] :
      ( k1_relset_1(A_9728,B_9729,C_9730) = k1_relat_1(C_9730)
      | ~ m1_subset_1(C_9730,k1_zfmisc_1(k2_zfmisc_1(A_9728,B_9729))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8449,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_8422])).

tff(c_8807,plain,(
    ! [A_9756,B_9757,C_9758] :
      ( m1_subset_1(k1_relset_1(A_9756,B_9757,C_9758),k1_zfmisc_1(A_9756))
      | ~ m1_subset_1(C_9758,k1_zfmisc_1(k2_zfmisc_1(A_9756,B_9757))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8838,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8449,c_8807])).

tff(c_8850,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_8838])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8869,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8850,c_12])).

tff(c_30,plain,(
    ! [A_19] :
      ( k2_relat_1(k4_relat_1(A_19)) = k1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_7869,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7865,c_30])).

tff(c_7879,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_7869])).

tff(c_10379,plain,(
    ! [C_12322,A_12323,B_12324] :
      ( m1_subset_1(C_12322,k1_zfmisc_1(k2_zfmisc_1(A_12323,B_12324)))
      | ~ r1_tarski(k2_relat_1(C_12322),B_12324)
      | ~ r1_tarski(k1_relat_1(C_12322),A_12323)
      | ~ v1_relat_1(C_12322) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    ! [A_21] :
      ( v1_funct_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_88,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_134,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_137,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_134])).

tff(c_140,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_137])).

tff(c_198,plain,(
    ! [B_78,A_79] :
      ( v1_relat_1(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_207,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_94,c_198])).

tff(c_214,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_207])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_214])).

tff(c_217,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_265,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_10406,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_4')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_10379,c_265])).

tff(c_10423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7883,c_6,c_8698,c_8869,c_7879,c_10406])).

tff(c_10424,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_25763,plain,(
    ! [A_30379,B_30380,C_30381] :
      ( k2_relset_1(A_30379,B_30380,C_30381) = k2_relat_1(C_30381)
      | ~ m1_subset_1(C_30381,k1_zfmisc_1(k2_zfmisc_1(A_30379,B_30380))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_25785,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_25763])).

tff(c_25795,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_25785])).

tff(c_10425,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_10623,plain,(
    ! [C_12350,A_12351,B_12352] :
      ( v4_relat_1(C_12350,A_12351)
      | ~ m1_subset_1(C_12350,k1_zfmisc_1(k2_zfmisc_1(A_12351,B_12352))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_10639,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10425,c_10623])).

tff(c_16,plain,(
    ! [B_11,A_9] :
      ( v1_relat_1(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10428,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10425,c_16])).

tff(c_10434,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10428])).

tff(c_21667,plain,(
    ! [A_30198] :
      ( k4_relat_1(A_30198) = k2_funct_1(A_30198)
      | ~ v2_funct_1(A_30198)
      | ~ v1_funct_1(A_30198)
      | ~ v1_relat_1(A_30198) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_21670,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_21667])).

tff(c_21673,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_98,c_21670])).

tff(c_21680,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21673,c_32])).

tff(c_21689,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_21680])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_21716,plain,(
    ! [A_12] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_12)
      | ~ v4_relat_1(k2_funct_1('#skF_4'),A_12)
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21689,c_20])).

tff(c_25144,plain,(
    ! [A_30359] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_30359)
      | ~ v4_relat_1(k2_funct_1('#skF_4'),A_30359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10434,c_21716])).

tff(c_25176,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10639,c_25144])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_25217,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_25176,c_2])).

tff(c_25283,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_25217])).

tff(c_25804,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25795,c_25283])).

tff(c_25819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_25804])).

tff(c_25820,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_25217])).

tff(c_25833,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25820,c_21689])).

tff(c_26222,plain,(
    ! [A_30392,B_30393,C_30394] :
      ( k1_relset_1(A_30392,B_30393,C_30394) = k1_relat_1(C_30394)
      | ~ m1_subset_1(C_30394,k1_zfmisc_1(k2_zfmisc_1(A_30392,B_30393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_26237,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_10425,c_26222])).

tff(c_26251,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25833,c_26237])).

tff(c_28474,plain,(
    ! [B_30501,C_30502,A_30503] :
      ( k1_xboole_0 = B_30501
      | v1_funct_2(C_30502,A_30503,B_30501)
      | k1_relset_1(A_30503,B_30501,C_30502) != A_30503
      | ~ m1_subset_1(C_30502,k1_zfmisc_1(k2_zfmisc_1(A_30503,B_30501))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_28502,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_10425,c_28474])).

tff(c_28527,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26251,c_28502])).

tff(c_28528,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_10424,c_28527])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28570,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28528,c_10])).

tff(c_26253,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_26222])).

tff(c_26452,plain,(
    ! [A_30400,B_30401,C_30402] :
      ( m1_subset_1(k1_relset_1(A_30400,B_30401,C_30402),k1_zfmisc_1(A_30400))
      | ~ m1_subset_1(C_30402,k1_zfmisc_1(k2_zfmisc_1(A_30400,B_30401))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_26489,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26253,c_26452])).

tff(c_26505,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_26489])).

tff(c_26536,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_26505,c_12])).

tff(c_26555,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26536,c_2])).

tff(c_27553,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_26555])).

tff(c_28635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28570,c_27553])).

tff(c_28636,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26555])).

tff(c_218,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_21677,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21673,c_30])).

tff(c_21687,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_21677])).

tff(c_84,plain,(
    ! [A_46] :
      ( v1_funct_2(A_46,k1_relat_1(A_46),k2_relat_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_21713,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21689,c_84])).

tff(c_21731,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10434,c_218,c_21687,c_21713])).

tff(c_25830,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25820,c_21731])).

tff(c_28657,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28636,c_25830])).

tff(c_28672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10424,c_28657])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:07:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.41/4.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/4.47  
% 11.41/4.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/4.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 11.41/4.47  
% 11.41/4.47  %Foreground sorts:
% 11.41/4.47  
% 11.41/4.47  
% 11.41/4.47  %Background operators:
% 11.41/4.47  
% 11.41/4.47  
% 11.41/4.47  %Foreground operators:
% 11.41/4.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.41/4.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.41/4.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.41/4.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.41/4.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.41/4.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.41/4.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.41/4.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.41/4.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.41/4.47  tff('#skF_2', type, '#skF_2': $i).
% 11.41/4.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.41/4.47  tff('#skF_3', type, '#skF_3': $i).
% 11.41/4.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.41/4.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.41/4.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.41/4.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.41/4.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.41/4.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.41/4.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.41/4.47  tff('#skF_4', type, '#skF_4': $i).
% 11.41/4.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.41/4.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.41/4.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.41/4.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.41/4.47  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 11.41/4.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.41/4.47  
% 11.41/4.49  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.41/4.49  tff(f_194, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 11.41/4.49  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.41/4.49  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 11.41/4.49  tff(f_60, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 11.41/4.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.41/4.49  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.41/4.49  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 11.41/4.49  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.41/4.49  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 11.41/4.49  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.41/4.50  tff(f_136, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 11.41/4.50  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.41/4.50  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.41/4.50  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 11.41/4.50  tff(f_154, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.41/4.50  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.41/4.50  tff(f_177, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 11.41/4.50  tff(c_24, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.41/4.50  tff(c_94, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.41/4.50  tff(c_254, plain, (![B_85, A_86]: (v1_relat_1(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.41/4.50  tff(c_260, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_94, c_254])).
% 11.41/4.50  tff(c_264, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_260])).
% 11.41/4.50  tff(c_98, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.41/4.50  tff(c_92, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.41/4.50  tff(c_7859, plain, (![A_9705]: (k4_relat_1(A_9705)=k2_funct_1(A_9705) | ~v2_funct_1(A_9705) | ~v1_funct_1(A_9705) | ~v1_relat_1(A_9705))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.41/4.50  tff(c_7862, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_7859])).
% 11.41/4.50  tff(c_7865, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_98, c_7862])).
% 11.41/4.50  tff(c_22, plain, (![A_14]: (v1_relat_1(k4_relat_1(A_14)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.41/4.50  tff(c_7875, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7865, c_22])).
% 11.41/4.50  tff(c_7883, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_7875])).
% 11.41/4.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.41/4.50  tff(c_90, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.41/4.50  tff(c_8658, plain, (![A_9753, B_9754, C_9755]: (k2_relset_1(A_9753, B_9754, C_9755)=k2_relat_1(C_9755) | ~m1_subset_1(C_9755, k1_zfmisc_1(k2_zfmisc_1(A_9753, B_9754))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.41/4.50  tff(c_8677, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_8658])).
% 11.41/4.50  tff(c_8685, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_8677])).
% 11.41/4.50  tff(c_32, plain, (![A_19]: (k1_relat_1(k4_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.41/4.50  tff(c_7872, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7865, c_32])).
% 11.41/4.50  tff(c_7881, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_7872])).
% 11.41/4.50  tff(c_8698, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8685, c_7881])).
% 11.41/4.50  tff(c_8422, plain, (![A_9728, B_9729, C_9730]: (k1_relset_1(A_9728, B_9729, C_9730)=k1_relat_1(C_9730) | ~m1_subset_1(C_9730, k1_zfmisc_1(k2_zfmisc_1(A_9728, B_9729))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.41/4.50  tff(c_8449, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_8422])).
% 11.41/4.50  tff(c_8807, plain, (![A_9756, B_9757, C_9758]: (m1_subset_1(k1_relset_1(A_9756, B_9757, C_9758), k1_zfmisc_1(A_9756)) | ~m1_subset_1(C_9758, k1_zfmisc_1(k2_zfmisc_1(A_9756, B_9757))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.41/4.50  tff(c_8838, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_8449, c_8807])).
% 11.41/4.50  tff(c_8850, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_8838])).
% 11.41/4.50  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.41/4.50  tff(c_8869, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_8850, c_12])).
% 11.41/4.50  tff(c_30, plain, (![A_19]: (k2_relat_1(k4_relat_1(A_19))=k1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.41/4.50  tff(c_7869, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7865, c_30])).
% 11.41/4.50  tff(c_7879, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_7869])).
% 11.41/4.50  tff(c_10379, plain, (![C_12322, A_12323, B_12324]: (m1_subset_1(C_12322, k1_zfmisc_1(k2_zfmisc_1(A_12323, B_12324))) | ~r1_tarski(k2_relat_1(C_12322), B_12324) | ~r1_tarski(k1_relat_1(C_12322), A_12323) | ~v1_relat_1(C_12322))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.41/4.50  tff(c_36, plain, (![A_21]: (v1_funct_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.41/4.50  tff(c_88, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.41/4.50  tff(c_134, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_88])).
% 11.41/4.50  tff(c_137, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_134])).
% 11.41/4.50  tff(c_140, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_137])).
% 11.41/4.50  tff(c_198, plain, (![B_78, A_79]: (v1_relat_1(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.41/4.50  tff(c_207, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_94, c_198])).
% 11.41/4.50  tff(c_214, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_207])).
% 11.41/4.50  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_214])).
% 11.41/4.50  tff(c_217, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_88])).
% 11.41/4.50  tff(c_265, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_217])).
% 11.41/4.50  tff(c_10406, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_4')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10379, c_265])).
% 11.41/4.50  tff(c_10423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7883, c_6, c_8698, c_8869, c_7879, c_10406])).
% 11.41/4.50  tff(c_10424, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_217])).
% 11.41/4.50  tff(c_25763, plain, (![A_30379, B_30380, C_30381]: (k2_relset_1(A_30379, B_30380, C_30381)=k2_relat_1(C_30381) | ~m1_subset_1(C_30381, k1_zfmisc_1(k2_zfmisc_1(A_30379, B_30380))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.41/4.50  tff(c_25785, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_25763])).
% 11.41/4.50  tff(c_25795, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_25785])).
% 11.41/4.50  tff(c_10425, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_217])).
% 11.41/4.50  tff(c_10623, plain, (![C_12350, A_12351, B_12352]: (v4_relat_1(C_12350, A_12351) | ~m1_subset_1(C_12350, k1_zfmisc_1(k2_zfmisc_1(A_12351, B_12352))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.41/4.50  tff(c_10639, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_10425, c_10623])).
% 11.41/4.50  tff(c_16, plain, (![B_11, A_9]: (v1_relat_1(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.41/4.50  tff(c_10428, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_10425, c_16])).
% 11.41/4.50  tff(c_10434, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_10428])).
% 11.41/4.50  tff(c_21667, plain, (![A_30198]: (k4_relat_1(A_30198)=k2_funct_1(A_30198) | ~v2_funct_1(A_30198) | ~v1_funct_1(A_30198) | ~v1_relat_1(A_30198))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.41/4.50  tff(c_21670, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_21667])).
% 11.41/4.50  tff(c_21673, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_98, c_21670])).
% 11.41/4.50  tff(c_21680, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21673, c_32])).
% 11.41/4.50  tff(c_21689, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_21680])).
% 11.41/4.50  tff(c_20, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.41/4.50  tff(c_21716, plain, (![A_12]: (r1_tarski(k2_relat_1('#skF_4'), A_12) | ~v4_relat_1(k2_funct_1('#skF_4'), A_12) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_21689, c_20])).
% 11.41/4.50  tff(c_25144, plain, (![A_30359]: (r1_tarski(k2_relat_1('#skF_4'), A_30359) | ~v4_relat_1(k2_funct_1('#skF_4'), A_30359))), inference(demodulation, [status(thm), theory('equality')], [c_10434, c_21716])).
% 11.41/4.50  tff(c_25176, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_10639, c_25144])).
% 11.41/4.50  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.41/4.50  tff(c_25217, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_25176, c_2])).
% 11.41/4.50  tff(c_25283, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_25217])).
% 11.41/4.50  tff(c_25804, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25795, c_25283])).
% 11.41/4.50  tff(c_25819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_25804])).
% 11.41/4.50  tff(c_25820, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_25217])).
% 11.41/4.50  tff(c_25833, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25820, c_21689])).
% 11.41/4.50  tff(c_26222, plain, (![A_30392, B_30393, C_30394]: (k1_relset_1(A_30392, B_30393, C_30394)=k1_relat_1(C_30394) | ~m1_subset_1(C_30394, k1_zfmisc_1(k2_zfmisc_1(A_30392, B_30393))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.41/4.50  tff(c_26237, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10425, c_26222])).
% 11.41/4.50  tff(c_26251, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25833, c_26237])).
% 11.41/4.50  tff(c_28474, plain, (![B_30501, C_30502, A_30503]: (k1_xboole_0=B_30501 | v1_funct_2(C_30502, A_30503, B_30501) | k1_relset_1(A_30503, B_30501, C_30502)!=A_30503 | ~m1_subset_1(C_30502, k1_zfmisc_1(k2_zfmisc_1(A_30503, B_30501))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.41/4.50  tff(c_28502, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_10425, c_28474])).
% 11.41/4.50  tff(c_28527, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26251, c_28502])).
% 11.41/4.50  tff(c_28528, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_10424, c_28527])).
% 11.41/4.50  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.41/4.50  tff(c_28570, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_28528, c_10])).
% 11.41/4.50  tff(c_26253, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_26222])).
% 11.41/4.50  tff(c_26452, plain, (![A_30400, B_30401, C_30402]: (m1_subset_1(k1_relset_1(A_30400, B_30401, C_30402), k1_zfmisc_1(A_30400)) | ~m1_subset_1(C_30402, k1_zfmisc_1(k2_zfmisc_1(A_30400, B_30401))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.41/4.50  tff(c_26489, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_26253, c_26452])).
% 11.41/4.50  tff(c_26505, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_26489])).
% 11.41/4.50  tff(c_26536, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_26505, c_12])).
% 11.41/4.50  tff(c_26555, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26536, c_2])).
% 11.41/4.50  tff(c_27553, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_26555])).
% 11.41/4.50  tff(c_28635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28570, c_27553])).
% 11.41/4.50  tff(c_28636, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_26555])).
% 11.41/4.50  tff(c_218, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_88])).
% 11.41/4.50  tff(c_21677, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21673, c_30])).
% 11.41/4.50  tff(c_21687, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_21677])).
% 11.41/4.50  tff(c_84, plain, (![A_46]: (v1_funct_2(A_46, k1_relat_1(A_46), k2_relat_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_177])).
% 11.41/4.50  tff(c_21713, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21689, c_84])).
% 11.41/4.50  tff(c_21731, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10434, c_218, c_21687, c_21713])).
% 11.41/4.50  tff(c_25830, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_25820, c_21731])).
% 11.41/4.50  tff(c_28657, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28636, c_25830])).
% 11.41/4.50  tff(c_28672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10424, c_28657])).
% 11.41/4.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/4.50  
% 11.41/4.50  Inference rules
% 11.41/4.50  ----------------------
% 11.41/4.50  #Ref     : 0
% 11.41/4.50  #Sup     : 7236
% 11.41/4.50  #Fact    : 0
% 11.41/4.50  #Define  : 0
% 11.41/4.50  #Split   : 128
% 11.41/4.50  #Chain   : 0
% 11.41/4.50  #Close   : 0
% 11.41/4.50  
% 11.41/4.50  Ordering : KBO
% 11.41/4.50  
% 11.41/4.50  Simplification rules
% 11.41/4.50  ----------------------
% 11.41/4.50  #Subsume      : 877
% 11.41/4.50  #Demod        : 4960
% 11.41/4.50  #Tautology    : 2310
% 11.41/4.50  #SimpNegUnit  : 59
% 11.41/4.50  #BackRed      : 576
% 11.41/4.50  
% 11.41/4.50  #Partial instantiations: 4635
% 11.41/4.50  #Strategies tried      : 1
% 11.41/4.50  
% 11.41/4.50  Timing (in seconds)
% 11.41/4.50  ----------------------
% 11.41/4.50  Preprocessing        : 0.37
% 11.41/4.50  Parsing              : 0.20
% 11.41/4.50  CNF conversion       : 0.03
% 11.41/4.50  Main loop            : 3.35
% 11.41/4.50  Inferencing          : 1.14
% 11.41/4.50  Reduction            : 1.25
% 11.41/4.50  Demodulation         : 0.92
% 11.41/4.50  BG Simplification    : 0.09
% 11.41/4.50  Subsumption          : 0.62
% 11.41/4.50  Abstraction          : 0.11
% 11.41/4.50  MUC search           : 0.00
% 11.41/4.50  Cooper               : 0.00
% 11.41/4.50  Total                : 3.77
% 11.41/4.50  Index Insertion      : 0.00
% 11.41/4.50  Index Deletion       : 0.00
% 11.41/4.50  Index Matching       : 0.00
% 11.41/4.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
