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
% DateTime   : Thu Dec  3 10:12:49 EST 2020

% Result     : Theorem 12.02s
% Output     : CNFRefutation 12.70s
% Verified   : 
% Statistics : Number of formulae       :  481 (7211 expanded)
%              Number of leaves         :   39 (2202 expanded)
%              Depth                    :   22
%              Number of atoms          :  917 (18851 expanded)
%              Number of equality atoms :  295 (6781 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_145,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_30,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_197,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_203,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_197])).

tff(c_210,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_203])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_22063,plain,(
    ! [A_1484,B_1485,C_1486] :
      ( k1_relset_1(A_1484,B_1485,C_1486) = k1_relat_1(C_1486)
      | ~ m1_subset_1(C_1486,k1_zfmisc_1(k2_zfmisc_1(A_1484,B_1485))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22089,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_22063])).

tff(c_24928,plain,(
    ! [B_1626,A_1627,C_1628] :
      ( k1_xboole_0 = B_1626
      | k1_relset_1(A_1627,B_1626,C_1628) = A_1627
      | ~ v1_funct_2(C_1628,A_1627,B_1626)
      | ~ m1_subset_1(C_1628,k1_zfmisc_1(k2_zfmisc_1(A_1627,B_1626))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24944,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_24928])).

tff(c_24959,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22089,c_24944])).

tff(c_24963,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_24959])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_127,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_139,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_16,c_127])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22176,plain,(
    ! [A_1499,B_1500,C_1501] :
      ( k2_relset_1(A_1499,B_1500,C_1501) = k2_relat_1(C_1501)
      | ~ m1_subset_1(C_1501,k1_zfmisc_1(k2_zfmisc_1(A_1499,B_1500))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22189,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_22176])).

tff(c_22203,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_22189])).

tff(c_38,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [A_19] :
      ( v1_funct_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_148,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_151,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_148])).

tff(c_154,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_151])).

tff(c_179,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_185,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_179])).

tff(c_192,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_185])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_192])).

tff(c_195,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_229,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_233,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_229])).

tff(c_609,plain,(
    ! [A_116,B_117,C_118] :
      ( k1_relset_1(A_116,B_117,C_118) = k1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_628,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_609])).

tff(c_4835,plain,(
    ! [B_314,A_315,C_316] :
      ( k1_xboole_0 = B_314
      | k1_relset_1(A_315,B_314,C_316) = A_315
      | ~ v1_funct_2(C_316,A_315,B_314)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_315,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4848,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_4835])).

tff(c_4863,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_628,c_4848])).

tff(c_4867,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4863])).

tff(c_1045,plain,(
    ! [B_162,A_163,C_164] :
      ( k1_xboole_0 = B_162
      | k1_relset_1(A_163,B_162,C_164) = A_163
      | ~ v1_funct_2(C_164,A_163,B_162)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1058,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1045])).

tff(c_1076,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_628,c_1058])).

tff(c_1080,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1076])).

tff(c_36,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_762,plain,(
    ! [A_132,B_133,C_134] :
      ( k2_relset_1(A_132,B_133,C_134) = k2_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_772,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_762])).

tff(c_786,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_772])).

tff(c_502,plain,(
    ! [A_106] :
      ( k1_relat_1(k2_funct_1(A_106)) = k2_relat_1(A_106)
      | ~ v2_funct_1(A_106)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_258,plain,(
    ! [B_63,A_64] :
      ( v4_relat_1(B_63,A_64)
      | ~ r1_tarski(k1_relat_1(B_63),A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_263,plain,(
    ! [B_63] :
      ( v4_relat_1(B_63,k1_relat_1(B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_2328,plain,(
    ! [A_225] :
      ( v4_relat_1(k2_funct_1(A_225),k2_relat_1(A_225))
      | ~ v1_relat_1(k2_funct_1(A_225))
      | ~ v2_funct_1(A_225)
      | ~ v1_funct_1(A_225)
      | ~ v1_relat_1(A_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_263])).

tff(c_2333,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_2328])).

tff(c_2339,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_70,c_2333])).

tff(c_2340,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2339])).

tff(c_2343,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2340])).

tff(c_2347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_2343])).

tff(c_2349,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2339])).

tff(c_196,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2348,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2339])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3898,plain,(
    ! [A_277,A_278] :
      ( r1_tarski(k2_relat_1(A_277),A_278)
      | ~ v4_relat_1(k2_funct_1(A_277),A_278)
      | ~ v1_relat_1(k2_funct_1(A_277))
      | ~ v2_funct_1(A_277)
      | ~ v1_funct_1(A_277)
      | ~ v1_relat_1(A_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_28])).

tff(c_3924,plain,(
    ! [A_279] :
      ( r1_tarski(k2_relat_1(A_279),k1_relat_1(k2_funct_1(A_279)))
      | ~ v2_funct_1(A_279)
      | ~ v1_funct_1(A_279)
      | ~ v1_relat_1(A_279)
      | ~ v1_relat_1(k2_funct_1(A_279)) ) ),
    inference(resolution,[status(thm)],[c_263,c_3898])).

tff(c_3938,plain,
    ( r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_3924])).

tff(c_3950,plain,(
    r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2349,c_210,c_76,c_70,c_3938])).

tff(c_353,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(k1_relat_1(B_83),A_84)
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_372,plain,(
    ! [B_83,A_84] :
      ( k1_relat_1(B_83) = A_84
      | ~ r1_tarski(A_84,k1_relat_1(B_83))
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_353,c_2])).

tff(c_3957,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3950,c_372])).

tff(c_3971,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2349,c_2348,c_3957])).

tff(c_669,plain,(
    ! [A_124] :
      ( m1_subset_1(A_124,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_124),k2_relat_1(A_124))))
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_703,plain,(
    ! [A_124] :
      ( r1_tarski(A_124,k2_zfmisc_1(k1_relat_1(A_124),k2_relat_1(A_124)))
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(resolution,[status(thm)],[c_669,c_18])).

tff(c_4069,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3971,c_703])).

tff(c_4161,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2349,c_196,c_4069])).

tff(c_4415,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4161])).

tff(c_4432,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_70,c_1080,c_4415])).

tff(c_4434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_4432])).

tff(c_4435,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1076])).

tff(c_4466,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4435,c_139])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4471,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4435,c_4435,c_12])).

tff(c_60,plain,(
    ! [A_33] :
      ( m1_subset_1(A_33,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33),k2_relat_1(A_33))))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_794,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_60])).

tff(c_803,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_794])).

tff(c_844,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_803,c_18])).

tff(c_869,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_844,c_2])).

tff(c_925,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_869])).

tff(c_4629,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4471,c_925])).

tff(c_4639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4466,c_4629])).

tff(c_4640,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_869])).

tff(c_4872,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4867,c_4640])).

tff(c_138,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_127])).

tff(c_245,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_252,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_245])).

tff(c_287,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_4931,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4872,c_287])).

tff(c_4936,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4931])).

tff(c_4937,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4863])).

tff(c_4970,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4937,c_139])).

tff(c_4975,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4937,c_4937,c_12])).

tff(c_5134,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4975,c_287])).

tff(c_5139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4970,c_5134])).

tff(c_5140,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_5165,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5140,c_72])).

tff(c_5776,plain,(
    ! [A_398,B_399,C_400] :
      ( k1_relset_1(A_398,B_399,C_400) = k1_relat_1(C_400)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5963,plain,(
    ! [C_411] :
      ( k1_relset_1('#skF_1','#skF_2',C_411) = k1_relat_1(C_411)
      | ~ m1_subset_1(C_411,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5140,c_5776])).

tff(c_5975,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5165,c_5963])).

tff(c_7004,plain,(
    ! [B_481,A_482,C_483] :
      ( k1_xboole_0 = B_481
      | k1_relset_1(A_482,B_481,C_483) = A_482
      | ~ v1_funct_2(C_483,A_482,B_481)
      | ~ m1_subset_1(C_483,k1_zfmisc_1(k2_zfmisc_1(A_482,B_481))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7013,plain,(
    ! [C_483] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_483) = '#skF_1'
      | ~ v1_funct_2(C_483,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_483,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5140,c_7004])).

tff(c_7067,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7013])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5176,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5140,c_10])).

tff(c_5195,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5176])).

tff(c_7097,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7067,c_5195])).

tff(c_7289,plain,(
    ! [A_495] : k2_zfmisc_1(A_495,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7067,c_7067,c_12])).

tff(c_6444,plain,(
    ! [B_461,C_462,A_463] :
      ( k1_xboole_0 = B_461
      | v1_funct_2(C_462,A_463,B_461)
      | k1_relset_1(A_463,B_461,C_462) != A_463
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(A_463,B_461))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6453,plain,(
    ! [C_462] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_462,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_462) != '#skF_1'
      | ~ m1_subset_1(C_462,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5140,c_6444])).

tff(c_6532,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6453])).

tff(c_6571,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6532,c_139])).

tff(c_6576,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6532,c_6532,c_12])).

tff(c_5628,plain,(
    ! [A_380,B_381,C_382] :
      ( k2_relset_1(A_380,B_381,C_382) = k2_relat_1(C_382)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_380,B_381))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5833,plain,(
    ! [C_407] :
      ( k2_relset_1('#skF_1','#skF_2',C_407) = k2_relat_1(C_407)
      | ~ m1_subset_1(C_407,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5140,c_5628])).

tff(c_5836,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5165,c_5833])).

tff(c_5846,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5836])).

tff(c_5501,plain,(
    ! [A_371] :
      ( m1_subset_1(A_371,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_371),k2_relat_1(A_371))))
      | ~ v1_funct_1(A_371)
      | ~ v1_relat_1(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_5531,plain,(
    ! [A_371] :
      ( r1_tarski(A_371,k2_zfmisc_1(k1_relat_1(A_371),k2_relat_1(A_371)))
      | ~ v1_funct_1(A_371)
      | ~ v1_relat_1(A_371) ) ),
    inference(resolution,[status(thm)],[c_5501,c_18])).

tff(c_5853,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5846,c_5531])).

tff(c_5866,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_5853])).

tff(c_5888,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5866,c_2])).

tff(c_6167,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5888])).

tff(c_6857,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6576,c_6167])).

tff(c_6863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6571,c_6857])).

tff(c_6865,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6453])).

tff(c_6275,plain,(
    ! [B_444,A_445,C_446] :
      ( k1_xboole_0 = B_444
      | k1_relset_1(A_445,B_444,C_446) = A_445
      | ~ v1_funct_2(C_446,A_445,B_444)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_445,B_444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6284,plain,(
    ! [C_446] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_446) = '#skF_1'
      | ~ v1_funct_2(C_446,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_446,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5140,c_6275])).

tff(c_6903,plain,(
    ! [C_478] :
      ( k1_relset_1('#skF_1','#skF_2',C_478) = '#skF_1'
      | ~ v1_funct_2(C_478,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_478,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6865,c_6284])).

tff(c_6906,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5165,c_6903])).

tff(c_6917,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5975,c_6906])).

tff(c_6921,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6917,c_6167])).

tff(c_6932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5140,c_6921])).

tff(c_6933,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5888])).

tff(c_7302,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7289,c_6933])).

tff(c_7365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7097,c_7302])).

tff(c_7521,plain,(
    ! [C_507] :
      ( k1_relset_1('#skF_1','#skF_2',C_507) = '#skF_1'
      | ~ v1_funct_2(C_507,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_507,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_7013])).

tff(c_7524,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5165,c_7521])).

tff(c_7535,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5975,c_7524])).

tff(c_5142,plain,(
    ! [C_325,A_326,B_327] :
      ( v4_relat_1(C_325,A_326)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_5285,plain,(
    ! [A_346,A_347,B_348] :
      ( v4_relat_1(A_346,A_347)
      | ~ r1_tarski(A_346,k2_zfmisc_1(A_347,B_348)) ) ),
    inference(resolution,[status(thm)],[c_20,c_5142])).

tff(c_5605,plain,(
    ! [B_377,A_378,B_379] :
      ( v4_relat_1(k1_relat_1(B_377),A_378)
      | ~ v4_relat_1(B_377,k2_zfmisc_1(A_378,B_379))
      | ~ v1_relat_1(B_377) ) ),
    inference(resolution,[status(thm)],[c_28,c_5285])).

tff(c_5697,plain,(
    ! [B_389] :
      ( v4_relat_1(k1_relat_1(B_389),'#skF_1')
      | ~ v4_relat_1(B_389,'#skF_3')
      | ~ v1_relat_1(B_389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5140,c_5605])).

tff(c_6095,plain,(
    ! [A_427] :
      ( v4_relat_1(k2_relat_1(A_427),'#skF_1')
      | ~ v4_relat_1(k2_funct_1(A_427),'#skF_3')
      | ~ v1_relat_1(k2_funct_1(A_427))
      | ~ v2_funct_1(A_427)
      | ~ v1_funct_1(A_427)
      | ~ v1_relat_1(A_427) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5697])).

tff(c_6100,plain,
    ( v4_relat_1('#skF_2','#skF_1')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5846,c_6095])).

tff(c_6106,plain,
    ( v4_relat_1('#skF_2','#skF_1')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_70,c_6100])).

tff(c_6128,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6106])).

tff(c_6131,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_6128])).

tff(c_6135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_6131])).

tff(c_6137,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6106])).

tff(c_5382,plain,(
    ! [A_358] :
      ( k1_relat_1(k2_funct_1(A_358)) = k2_relat_1(A_358)
      | ~ v2_funct_1(A_358)
      | ~ v1_funct_1(A_358)
      | ~ v1_relat_1(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8997,plain,(
    ! [A_572] :
      ( v4_relat_1(k2_funct_1(A_572),k2_relat_1(A_572))
      | ~ v1_relat_1(k2_funct_1(A_572))
      | ~ v2_funct_1(A_572)
      | ~ v1_funct_1(A_572)
      | ~ v1_relat_1(A_572) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5382,c_263])).

tff(c_9002,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5846,c_8997])).

tff(c_9008,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_70,c_6137,c_9002])).

tff(c_9143,plain,(
    ! [A_578,A_579] :
      ( r1_tarski(k2_relat_1(A_578),A_579)
      | ~ v4_relat_1(k2_funct_1(A_578),A_579)
      | ~ v1_relat_1(k2_funct_1(A_578))
      | ~ v2_funct_1(A_578)
      | ~ v1_funct_1(A_578)
      | ~ v1_relat_1(A_578) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5382,c_28])).

tff(c_9527,plain,(
    ! [A_595] :
      ( r1_tarski(k2_relat_1(A_595),k1_relat_1(k2_funct_1(A_595)))
      | ~ v2_funct_1(A_595)
      | ~ v1_funct_1(A_595)
      | ~ v1_relat_1(A_595)
      | ~ v1_relat_1(k2_funct_1(A_595)) ) ),
    inference(resolution,[status(thm)],[c_263,c_9143])).

tff(c_9538,plain,
    ( r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5846,c_9527])).

tff(c_9549,plain,(
    r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6137,c_210,c_76,c_70,c_9538])).

tff(c_5209,plain,(
    ! [B_331,A_332] :
      ( r1_tarski(k1_relat_1(B_331),A_332)
      | ~ v4_relat_1(B_331,A_332)
      | ~ v1_relat_1(B_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5223,plain,(
    ! [B_331,A_332] :
      ( k1_relat_1(B_331) = A_332
      | ~ r1_tarski(A_332,k1_relat_1(B_331))
      | ~ v4_relat_1(B_331,A_332)
      | ~ v1_relat_1(B_331) ) ),
    inference(resolution,[status(thm)],[c_5209,c_2])).

tff(c_9553,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9549,c_5223])).

tff(c_9564,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6137,c_9008,c_9553])).

tff(c_9657,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9564,c_5531])).

tff(c_9739,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6137,c_196,c_9657])).

tff(c_9955,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_9739])).

tff(c_9973,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_70,c_7535,c_9955])).

tff(c_9975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_9973])).

tff(c_9977,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5176])).

tff(c_9984,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9977,c_9977,c_14])).

tff(c_9976,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5176])).

tff(c_10029,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9977,c_9977,c_9976])).

tff(c_10030,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10029])).

tff(c_10032,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10030,c_233])).

tff(c_10135,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9984,c_10032])).

tff(c_9987,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9977,c_16])).

tff(c_10429,plain,(
    ! [A_651,B_652,C_653] :
      ( k2_relset_1(A_651,B_652,C_653) = k2_relat_1(C_653)
      | ~ m1_subset_1(C_653,k1_zfmisc_1(k2_zfmisc_1(A_651,B_652))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10450,plain,(
    ! [A_654,B_655] : k2_relset_1(A_654,B_655,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9987,c_10429])).

tff(c_10034,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10030,c_10030,c_68])).

tff(c_10454,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_10450,c_10034])).

tff(c_10202,plain,(
    ! [A_629] :
      ( k1_relat_1(k2_funct_1(A_629)) = k2_relat_1(A_629)
      | ~ v2_funct_1(A_629)
      | ~ v1_funct_1(A_629)
      | ~ v1_relat_1(A_629) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12045,plain,(
    ! [A_771] :
      ( v4_relat_1(k2_funct_1(A_771),k2_relat_1(A_771))
      | ~ v1_relat_1(k2_funct_1(A_771))
      | ~ v2_funct_1(A_771)
      | ~ v1_funct_1(A_771)
      | ~ v1_relat_1(A_771) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10202,c_263])).

tff(c_12053,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10454,c_12045])).

tff(c_12061,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_70,c_12053])).

tff(c_12062,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12061])).

tff(c_12065,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_12062])).

tff(c_12069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_12065])).

tff(c_12071,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12061])).

tff(c_12070,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_12061])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10112,plain,(
    ! [A_610] :
      ( A_610 = '#skF_3'
      | ~ r1_tarski(A_610,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9977,c_9977,c_8])).

tff(c_10127,plain,(
    ! [B_16] :
      ( k1_relat_1(B_16) = '#skF_3'
      | ~ v4_relat_1(B_16,'#skF_3')
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_28,c_10112])).

tff(c_12079,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12070,c_10127])).

tff(c_12088,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12071,c_12079])).

tff(c_10287,plain,(
    ! [A_640] :
      ( m1_subset_1(A_640,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_640),k2_relat_1(A_640))))
      | ~ v1_funct_1(A_640)
      | ~ v1_relat_1(A_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10314,plain,(
    ! [A_640] :
      ( r1_tarski(A_640,k2_zfmisc_1(k1_relat_1(A_640),k2_relat_1(A_640)))
      | ~ v1_funct_1(A_640)
      | ~ v1_relat_1(A_640) ) ),
    inference(resolution,[status(thm)],[c_10287,c_18])).

tff(c_12162,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12088,c_10314])).

tff(c_12228,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12071,c_196,c_9984,c_12162])).

tff(c_12230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10135,c_12228])).

tff(c_12231,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10029])).

tff(c_9986,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9977,c_9977,c_12])).

tff(c_12304,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12231,c_12231,c_9986])).

tff(c_12240,plain,(
    ~ r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12231,c_233])).

tff(c_12403,plain,(
    ~ r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12304,c_12240])).

tff(c_12242,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12231,c_210])).

tff(c_12247,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12231,c_76])).

tff(c_12246,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12231,c_70])).

tff(c_12287,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12231,c_12231,c_9984])).

tff(c_12462,plain,(
    ! [A_800,A_801,B_802] :
      ( v4_relat_1(A_800,A_801)
      | ~ r1_tarski(A_800,k2_zfmisc_1(A_801,B_802)) ) ),
    inference(resolution,[status(thm)],[c_20,c_5142])).

tff(c_12484,plain,(
    ! [A_801,B_802] : v4_relat_1(k2_zfmisc_1(A_801,B_802),A_801) ),
    inference(resolution,[status(thm)],[c_6,c_12462])).

tff(c_9983,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9977,c_9977,c_8])).

tff(c_12363,plain,(
    ! [A_782] :
      ( A_782 = '#skF_1'
      | ~ r1_tarski(A_782,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12231,c_12231,c_9983])).

tff(c_12562,plain,(
    ! [B_817] :
      ( k1_relat_1(B_817) = '#skF_1'
      | ~ v4_relat_1(B_817,'#skF_1')
      | ~ v1_relat_1(B_817) ) ),
    inference(resolution,[status(thm)],[c_28,c_12363])).

tff(c_12566,plain,(
    ! [B_802] :
      ( k1_relat_1(k2_zfmisc_1('#skF_1',B_802)) = '#skF_1'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1',B_802)) ) ),
    inference(resolution,[status(thm)],[c_12484,c_12562])).

tff(c_12577,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12287,c_12566])).

tff(c_12334,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12231,c_9987])).

tff(c_12607,plain,(
    ! [A_818,B_819,C_820] :
      ( k2_relset_1(A_818,B_819,C_820) = k2_relat_1(C_820)
      | ~ m1_subset_1(C_820,k1_zfmisc_1(k2_zfmisc_1(A_818,B_819))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12673,plain,(
    ! [A_824,B_825] : k2_relset_1(A_824,B_825,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12334,c_12607])).

tff(c_12244,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12231,c_68])).

tff(c_12677,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_12673,c_12244])).

tff(c_12382,plain,(
    ! [A_783] :
      ( k1_relat_1(k2_funct_1(A_783)) = k2_relat_1(A_783)
      | ~ v2_funct_1(A_783)
      | ~ v1_funct_1(A_783)
      | ~ v1_relat_1(A_783) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14117,plain,(
    ! [A_935] :
      ( v4_relat_1(k2_funct_1(A_935),k2_relat_1(A_935))
      | ~ v1_relat_1(k2_funct_1(A_935))
      | ~ v2_funct_1(A_935)
      | ~ v1_funct_1(A_935)
      | ~ v1_relat_1(A_935) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12382,c_263])).

tff(c_14122,plain,
    ( v4_relat_1(k2_funct_1('#skF_1'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12677,c_14117])).

tff(c_14128,plain,
    ( v4_relat_1(k2_funct_1('#skF_1'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12242,c_12247,c_12246,c_14122])).

tff(c_14129,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_14128])).

tff(c_14132,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_14129])).

tff(c_14136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12242,c_12247,c_14132])).

tff(c_14138,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_14128])).

tff(c_12243,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12231,c_196])).

tff(c_14137,plain,(
    v4_relat_1(k2_funct_1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_14128])).

tff(c_14157,plain,(
    ! [A_936,A_937] :
      ( r1_tarski(k2_relat_1(A_936),A_937)
      | ~ v4_relat_1(k2_funct_1(A_936),A_937)
      | ~ v1_relat_1(k2_funct_1(A_936))
      | ~ v2_funct_1(A_936)
      | ~ v1_funct_1(A_936)
      | ~ v1_relat_1(A_936) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12382,c_28])).

tff(c_14387,plain,(
    ! [A_946] :
      ( r1_tarski(k2_relat_1(A_946),k1_relat_1(k2_funct_1(A_946)))
      | ~ v2_funct_1(A_946)
      | ~ v1_funct_1(A_946)
      | ~ v1_relat_1(A_946)
      | ~ v1_relat_1(k2_funct_1(A_946)) ) ),
    inference(resolution,[status(thm)],[c_263,c_14157])).

tff(c_14398,plain,
    ( r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_1')))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12677,c_14387])).

tff(c_14409,plain,(
    r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14138,c_12242,c_12247,c_12246,c_14398])).

tff(c_9993,plain,(
    ! [B_600,A_601] :
      ( r1_tarski(k1_relat_1(B_600),A_601)
      | ~ v4_relat_1(B_600,A_601)
      | ~ v1_relat_1(B_600) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10003,plain,(
    ! [B_600,A_601] :
      ( k1_relat_1(B_600) = A_601
      | ~ r1_tarski(A_601,k1_relat_1(B_600))
      | ~ v4_relat_1(B_600,A_601)
      | ~ v1_relat_1(B_600) ) ),
    inference(resolution,[status(thm)],[c_9993,c_2])).

tff(c_14413,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = '#skF_2'
    | ~ v4_relat_1(k2_funct_1('#skF_1'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14409,c_10003])).

tff(c_14424,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14138,c_14137,c_14413])).

tff(c_12632,plain,(
    ! [A_823] :
      ( m1_subset_1(A_823,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_823),k2_relat_1(A_823))))
      | ~ v1_funct_1(A_823)
      | ~ v1_relat_1(A_823) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_12670,plain,(
    ! [A_823] :
      ( r1_tarski(A_823,k2_zfmisc_1(k1_relat_1(A_823),k2_relat_1(A_823)))
      | ~ v1_funct_1(A_823)
      | ~ v1_relat_1(A_823) ) ),
    inference(resolution,[status(thm)],[c_12632,c_18])).

tff(c_14502,plain,
    ( r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_1'))))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14424,c_12670])).

tff(c_14574,plain,(
    r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14138,c_12243,c_14502])).

tff(c_14773,plain,
    ( r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_14574])).

tff(c_14785,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12242,c_12247,c_12246,c_12304,c_12577,c_14773])).

tff(c_14787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12403,c_14785])).

tff(c_14788,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_16250,plain,(
    ! [A_1102,B_1103,C_1104] :
      ( k2_relset_1(A_1102,B_1103,C_1104) = k2_relat_1(C_1104)
      | ~ m1_subset_1(C_1104,k1_zfmisc_1(k2_zfmisc_1(A_1102,B_1103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_16260,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_16250])).

tff(c_16274,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16260])).

tff(c_14789,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_16119,plain,(
    ! [A_1084,B_1085,C_1086] :
      ( k1_relset_1(A_1084,B_1085,C_1086) = k1_relat_1(C_1086)
      | ~ m1_subset_1(C_1086,k1_zfmisc_1(k2_zfmisc_1(A_1084,B_1085))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16140,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14789,c_16119])).

tff(c_16665,plain,(
    ! [B_1139,C_1140,A_1141] :
      ( k1_xboole_0 = B_1139
      | v1_funct_2(C_1140,A_1141,B_1139)
      | k1_relset_1(A_1141,B_1139,C_1140) != A_1141
      | ~ m1_subset_1(C_1140,k1_zfmisc_1(k2_zfmisc_1(A_1141,B_1139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_16674,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_14789,c_16665])).

tff(c_16697,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16140,c_16674])).

tff(c_16698,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_14788,c_16697])).

tff(c_16705,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16698])).

tff(c_16708,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_16705])).

tff(c_16711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_70,c_16274,c_16708])).

tff(c_16712,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16698])).

tff(c_16743,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16712,c_139])).

tff(c_16748,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16712,c_16712,c_12])).

tff(c_14799,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_14789,c_18])).

tff(c_14817,plain,(
    ! [B_954,A_955] :
      ( B_954 = A_955
      | ~ r1_tarski(B_954,A_955)
      | ~ r1_tarski(A_955,B_954) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14826,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14799,c_14817])).

tff(c_14926,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14826])).

tff(c_16926,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16748,c_14926])).

tff(c_16931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16743,c_16926])).

tff(c_16932,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_14826])).

tff(c_22978,plain,(
    ! [B_1548,C_1549,A_1550] :
      ( k1_xboole_0 = B_1548
      | v1_funct_2(C_1549,A_1550,B_1548)
      | k1_relset_1(A_1550,B_1548,C_1549) != A_1550
      | ~ m1_subset_1(C_1549,k1_zfmisc_1(k2_zfmisc_1(A_1550,B_1548))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_22984,plain,(
    ! [C_1549] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_1549,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_1549) != '#skF_2'
      | ~ m1_subset_1(C_1549,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16932,c_22978])).

tff(c_23170,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_22984])).

tff(c_22769,plain,(
    ! [B_1543,A_1544,C_1545] :
      ( k1_xboole_0 = B_1543
      | k1_relset_1(A_1544,B_1543,C_1545) = A_1544
      | ~ v1_funct_2(C_1545,A_1544,B_1543)
      | ~ m1_subset_1(C_1545,k1_zfmisc_1(k2_zfmisc_1(A_1544,B_1543))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_22785,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_22769])).

tff(c_22803,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22089,c_22785])).

tff(c_22807,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_22803])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( v4_relat_1(B_16,A_15)
      | ~ r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22872,plain,(
    ! [A_15] :
      ( v4_relat_1('#skF_3',A_15)
      | ~ r1_tarski('#skF_1',A_15)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22807,c_26])).

tff(c_22937,plain,(
    ! [A_1547] :
      ( v4_relat_1('#skF_3',A_1547)
      | ~ r1_tarski('#skF_1',A_1547) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_22872])).

tff(c_17572,plain,(
    ! [A_1216,B_1217,C_1218] :
      ( k2_relset_1(A_1216,B_1217,C_1218) = k2_relat_1(C_1218)
      | ~ m1_subset_1(C_1218,k1_zfmisc_1(k2_zfmisc_1(A_1216,B_1217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_17585,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_17572])).

tff(c_17599,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_17585])).

tff(c_14833,plain,(
    ! [C_956,A_957,B_958] :
      ( v4_relat_1(C_956,A_957)
      | ~ m1_subset_1(C_956,k1_zfmisc_1(k2_zfmisc_1(A_957,B_958))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14856,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_14833])).

tff(c_14871,plain,(
    ! [B_964,A_965] :
      ( r1_tarski(k1_relat_1(B_964),A_965)
      | ~ v4_relat_1(B_964,A_965)
      | ~ v1_relat_1(B_964) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_207,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(A_7)
      | ~ v1_relat_1(B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_20,c_197])).

tff(c_17250,plain,(
    ! [B_1186,A_1187] :
      ( v1_relat_1(k1_relat_1(B_1186))
      | ~ v1_relat_1(A_1187)
      | ~ v4_relat_1(B_1186,A_1187)
      | ~ v1_relat_1(B_1186) ) ),
    inference(resolution,[status(thm)],[c_14871,c_207])).

tff(c_17264,plain,
    ( v1_relat_1(k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14856,c_17250])).

tff(c_17279,plain,
    ( v1_relat_1(k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_17264])).

tff(c_17280,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_17279])).

tff(c_18299,plain,(
    ! [B_1276,C_1277,A_1278] :
      ( k1_xboole_0 = B_1276
      | v1_funct_2(C_1277,A_1278,B_1276)
      | k1_relset_1(A_1278,B_1276,C_1277) != A_1278
      | ~ m1_subset_1(C_1277,k1_zfmisc_1(k2_zfmisc_1(A_1278,B_1276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_18308,plain,(
    ! [C_1277] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_1277,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_1277) != '#skF_2'
      | ~ m1_subset_1(C_1277,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16932,c_18299])).

tff(c_18462,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18308])).

tff(c_86,plain,(
    ! [A_38] : k2_zfmisc_1(A_38,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_30])).

tff(c_18505,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18462,c_90])).

tff(c_18509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17280,c_18505])).

tff(c_18511,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18308])).

tff(c_17851,plain,(
    ! [A_1240,B_1241,C_1242] :
      ( k1_relset_1(A_1240,B_1241,C_1242) = k1_relat_1(C_1242)
      | ~ m1_subset_1(C_1242,k1_zfmisc_1(k2_zfmisc_1(A_1240,B_1241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_17990,plain,(
    ! [A_1257,B_1258,A_1259] :
      ( k1_relset_1(A_1257,B_1258,A_1259) = k1_relat_1(A_1259)
      | ~ r1_tarski(A_1259,k2_zfmisc_1(A_1257,B_1258)) ) ),
    inference(resolution,[status(thm)],[c_20,c_17851])).

tff(c_18029,plain,(
    ! [A_1257,B_1258] : k1_relset_1(A_1257,B_1258,k2_zfmisc_1(A_1257,B_1258)) = k1_relat_1(k2_zfmisc_1(A_1257,B_1258)) ),
    inference(resolution,[status(thm)],[c_6,c_17990])).

tff(c_18988,plain,(
    ! [B_1305,A_1306,A_1307] :
      ( k1_xboole_0 = B_1305
      | v1_funct_2(A_1306,A_1307,B_1305)
      | k1_relset_1(A_1307,B_1305,A_1306) != A_1307
      | ~ r1_tarski(A_1306,k2_zfmisc_1(A_1307,B_1305)) ) ),
    inference(resolution,[status(thm)],[c_20,c_18299])).

tff(c_19015,plain,(
    ! [B_1305,A_1307] :
      ( k1_xboole_0 = B_1305
      | v1_funct_2(k2_zfmisc_1(A_1307,B_1305),A_1307,B_1305)
      | k1_relset_1(A_1307,B_1305,k2_zfmisc_1(A_1307,B_1305)) != A_1307 ) ),
    inference(resolution,[status(thm)],[c_6,c_18988])).

tff(c_19027,plain,(
    ! [B_1308,A_1309] :
      ( k1_xboole_0 = B_1308
      | v1_funct_2(k2_zfmisc_1(A_1309,B_1308),A_1309,B_1308)
      | k1_relat_1(k2_zfmisc_1(A_1309,B_1308)) != A_1309 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18029,c_19015])).

tff(c_19039,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_16932,c_19027])).

tff(c_19054,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16932,c_19039])).

tff(c_19055,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_14788,c_18511,c_19054])).

tff(c_19061,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_19055])).

tff(c_19064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_70,c_17599,c_19061])).

tff(c_19065,plain,(
    v1_relat_1(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_17279])).

tff(c_14860,plain,(
    ! [C_960,A_961] :
      ( v4_relat_1(C_960,A_961)
      | ~ m1_subset_1(C_960,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_14833])).

tff(c_14867,plain,(
    ! [A_7,A_961] :
      ( v4_relat_1(A_7,A_961)
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_14860])).

tff(c_17052,plain,(
    ! [B_1163] :
      ( k1_relat_1(B_1163) = k1_xboole_0
      | ~ v4_relat_1(B_1163,k1_xboole_0)
      | ~ v1_relat_1(B_1163) ) ),
    inference(resolution,[status(thm)],[c_14871,c_8])).

tff(c_17178,plain,(
    ! [A_1172] :
      ( k1_relat_1(A_1172) = k1_xboole_0
      | ~ v1_relat_1(A_1172)
      | ~ r1_tarski(A_1172,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14867,c_17052])).

tff(c_22729,plain,(
    ! [B_1542] :
      ( k1_relat_1(k1_relat_1(B_1542)) = k1_xboole_0
      | ~ v1_relat_1(k1_relat_1(B_1542))
      | ~ v4_relat_1(B_1542,k1_xboole_0)
      | ~ v1_relat_1(B_1542) ) ),
    inference(resolution,[status(thm)],[c_28,c_17178])).

tff(c_22747,plain,
    ( k1_relat_1(k1_relat_1('#skF_3')) = k1_xboole_0
    | ~ v4_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_19065,c_22729])).

tff(c_22761,plain,
    ( k1_relat_1(k1_relat_1('#skF_3')) = k1_xboole_0
    | ~ v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_22747])).

tff(c_22764,plain,(
    ~ v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_22761])).

tff(c_22961,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22937,c_22764])).

tff(c_23178,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23170,c_22961])).

tff(c_23225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_23178])).

tff(c_23227,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22984])).

tff(c_22496,plain,(
    ! [A_1527,B_1528,A_1529] :
      ( k1_relset_1(A_1527,B_1528,A_1529) = k1_relat_1(A_1529)
      | ~ r1_tarski(A_1529,k2_zfmisc_1(A_1527,B_1528)) ) ),
    inference(resolution,[status(thm)],[c_20,c_22063])).

tff(c_22535,plain,(
    ! [A_1527,B_1528] : k1_relset_1(A_1527,B_1528,k2_zfmisc_1(A_1527,B_1528)) = k1_relat_1(k2_zfmisc_1(A_1527,B_1528)) ),
    inference(resolution,[status(thm)],[c_6,c_22496])).

tff(c_23550,plain,(
    ! [B_1575,A_1576,A_1577] :
      ( k1_xboole_0 = B_1575
      | v1_funct_2(A_1576,A_1577,B_1575)
      | k1_relset_1(A_1577,B_1575,A_1576) != A_1577
      | ~ r1_tarski(A_1576,k2_zfmisc_1(A_1577,B_1575)) ) ),
    inference(resolution,[status(thm)],[c_20,c_22978])).

tff(c_23577,plain,(
    ! [B_1575,A_1577] :
      ( k1_xboole_0 = B_1575
      | v1_funct_2(k2_zfmisc_1(A_1577,B_1575),A_1577,B_1575)
      | k1_relset_1(A_1577,B_1575,k2_zfmisc_1(A_1577,B_1575)) != A_1577 ) ),
    inference(resolution,[status(thm)],[c_6,c_23550])).

tff(c_23590,plain,(
    ! [B_1578,A_1579] :
      ( k1_xboole_0 = B_1578
      | v1_funct_2(k2_zfmisc_1(A_1579,B_1578),A_1579,B_1578)
      | k1_relat_1(k2_zfmisc_1(A_1579,B_1578)) != A_1579 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22535,c_23577])).

tff(c_23602,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_16932,c_23590])).

tff(c_23617,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16932,c_23602])).

tff(c_23618,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_14788,c_23227,c_23617])).

tff(c_23624,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_23618])).

tff(c_23627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_70,c_22203,c_23624])).

tff(c_23628,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_22803])).

tff(c_23667,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23628,c_139])).

tff(c_23672,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23628,c_23628,c_12])).

tff(c_21878,plain,(
    ! [A_1467] :
      ( m1_subset_1(A_1467,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1467),k2_relat_1(A_1467))))
      | ~ v1_funct_1(A_1467)
      | ~ v1_relat_1(A_1467) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_21908,plain,(
    ! [A_1467] :
      ( r1_tarski(A_1467,k2_zfmisc_1(k1_relat_1(A_1467),k2_relat_1(A_1467)))
      | ~ v1_funct_1(A_1467)
      | ~ v1_relat_1(A_1467) ) ),
    inference(resolution,[status(thm)],[c_21878,c_18])).

tff(c_22210,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22203,c_21908])).

tff(c_22223,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_22210])).

tff(c_22252,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_22223,c_2])).

tff(c_22350,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_22252])).

tff(c_24255,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23672,c_22350])).

tff(c_24265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23667,c_24255])).

tff(c_24267,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_22761])).

tff(c_14883,plain,(
    ! [B_964] :
      ( k1_relat_1(B_964) = k1_xboole_0
      | ~ v4_relat_1(B_964,k1_xboole_0)
      | ~ v1_relat_1(B_964) ) ),
    inference(resolution,[status(thm)],[c_14871,c_8])).

tff(c_24272,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24267,c_14883])).

tff(c_24278,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_24272])).

tff(c_24279,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,'#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24278,c_22350])).

tff(c_24291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_14,c_24279])).

tff(c_24292,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22252])).

tff(c_24967,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24963,c_24292])).

tff(c_14827,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_14817])).

tff(c_14858,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_14827])).

tff(c_25062,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24967,c_14858])).

tff(c_25067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_25062])).

tff(c_25068,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24959])).

tff(c_25107,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25068,c_139])).

tff(c_25112,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25068,c_25068,c_12])).

tff(c_25238,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25112,c_14858])).

tff(c_25243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25107,c_25238])).

tff(c_25244,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14827])).

tff(c_25248,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25244,c_72])).

tff(c_27281,plain,(
    ! [A_1817,B_1818,C_1819] :
      ( k2_relset_1(A_1817,B_1818,C_1819) = k2_relat_1(C_1819)
      | ~ m1_subset_1(C_1819,k1_zfmisc_1(k2_zfmisc_1(A_1817,B_1818))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_27334,plain,(
    ! [C_1823] :
      ( k2_relset_1('#skF_1','#skF_2',C_1823) = k2_relat_1(C_1823)
      | ~ m1_subset_1(C_1823,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25244,c_27281])).

tff(c_27337,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_25248,c_27334])).

tff(c_27347,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_27337])).

tff(c_27404,plain,(
    ! [A_1824,B_1825,C_1826] :
      ( k1_relset_1(A_1824,B_1825,C_1826) = k1_relat_1(C_1826)
      | ~ m1_subset_1(C_1826,k1_zfmisc_1(k2_zfmisc_1(A_1824,B_1825))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_27429,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14789,c_27404])).

tff(c_27970,plain,(
    ! [B_1877,C_1878,A_1879] :
      ( k1_xboole_0 = B_1877
      | v1_funct_2(C_1878,A_1879,B_1877)
      | k1_relset_1(A_1879,B_1877,C_1878) != A_1879
      | ~ m1_subset_1(C_1878,k1_zfmisc_1(k2_zfmisc_1(A_1879,B_1877))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_27982,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_14789,c_27970])).

tff(c_28002,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27429,c_27982])).

tff(c_28003,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_14788,c_28002])).

tff(c_28008,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28003])).

tff(c_28011,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_28008])).

tff(c_28014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_76,c_70,c_27347,c_28011])).

tff(c_28015,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_28003])).

tff(c_25256,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_25244,c_10])).

tff(c_25275,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_25256])).

tff(c_28049,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28015,c_25275])).

tff(c_28055,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28015,c_28015,c_14])).

tff(c_28307,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28055,c_25244])).

tff(c_28309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28049,c_28307])).

tff(c_28311,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_25256])).

tff(c_28317,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28311,c_28311,c_14])).

tff(c_28573,plain,(
    ! [A_1917,A_1918,B_1919] :
      ( v4_relat_1(A_1917,A_1918)
      | ~ r1_tarski(A_1917,k2_zfmisc_1(A_1918,B_1919)) ) ),
    inference(resolution,[status(thm)],[c_20,c_14833])).

tff(c_28595,plain,(
    ! [A_1918,B_1919] : v4_relat_1(k2_zfmisc_1(A_1918,B_1919),A_1918) ),
    inference(resolution,[status(thm)],[c_6,c_28573])).

tff(c_28505,plain,(
    ! [B_1898,A_1899] :
      ( r1_tarski(k1_relat_1(B_1898),A_1899)
      | ~ v4_relat_1(B_1898,A_1899)
      | ~ v1_relat_1(B_1898) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28316,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28311,c_28311,c_8])).

tff(c_28684,plain,(
    ! [B_1931] :
      ( k1_relat_1(B_1931) = '#skF_3'
      | ~ v4_relat_1(B_1931,'#skF_3')
      | ~ v1_relat_1(B_1931) ) ),
    inference(resolution,[status(thm)],[c_28505,c_28316])).

tff(c_28688,plain,(
    ! [B_1919] :
      ( k1_relat_1(k2_zfmisc_1('#skF_3',B_1919)) = '#skF_3'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3',B_1919)) ) ),
    inference(resolution,[status(thm)],[c_28595,c_28684])).

tff(c_28699,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28317,c_28688])).

tff(c_28320,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28311,c_16])).

tff(c_28865,plain,(
    ! [A_1943,B_1944,C_1945] :
      ( k1_relset_1(A_1943,B_1944,C_1945) = k1_relat_1(C_1945)
      | ~ m1_subset_1(C_1945,k1_zfmisc_1(k2_zfmisc_1(A_1943,B_1944))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28872,plain,(
    ! [A_1943,B_1944] : k1_relset_1(A_1943,B_1944,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28320,c_28865])).

tff(c_28885,plain,(
    ! [A_1943,B_1944] : k1_relset_1(A_1943,B_1944,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28699,c_28872])).

tff(c_54,plain,(
    ! [B_31,C_32,A_30] :
      ( k1_xboole_0 = B_31
      | v1_funct_2(C_32,A_30,B_31)
      | k1_relset_1(A_30,B_31,C_32) != A_30
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_29181,plain,(
    ! [B_1987,C_1988,A_1989] :
      ( B_1987 = '#skF_3'
      | v1_funct_2(C_1988,A_1989,B_1987)
      | k1_relset_1(A_1989,B_1987,C_1988) != A_1989
      | ~ m1_subset_1(C_1988,k1_zfmisc_1(k2_zfmisc_1(A_1989,B_1987))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28311,c_54])).

tff(c_29188,plain,(
    ! [B_1987,A_1989] :
      ( B_1987 = '#skF_3'
      | v1_funct_2('#skF_3',A_1989,B_1987)
      | k1_relset_1(A_1989,B_1987,'#skF_3') != A_1989 ) ),
    inference(resolution,[status(thm)],[c_28320,c_29181])).

tff(c_29205,plain,(
    ! [B_1990,A_1991] :
      ( B_1990 = '#skF_3'
      | v1_funct_2('#skF_3',A_1991,B_1990)
      | A_1991 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28885,c_29188])).

tff(c_28310,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_25256])).

tff(c_28337,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28311,c_28311,c_28310])).

tff(c_28338,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_28337])).

tff(c_28355,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28338,c_14789])).

tff(c_28451,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28317,c_28355])).

tff(c_28461,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_28451,c_18])).

tff(c_28470,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28461,c_28316])).

tff(c_28356,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28338,c_14788])).

tff(c_28479,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28470,c_28356])).

tff(c_29220,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_29205,c_28479])).

tff(c_28358,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28338,c_74])).

tff(c_29255,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29220,c_29220,c_28358])).

tff(c_29249,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29220,c_29220,c_28479])).

tff(c_29448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29255,c_29249])).

tff(c_29449,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_28337])).

tff(c_29450,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28337])).

tff(c_29471,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29449,c_29450])).

tff(c_48,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_30,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_78,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48])).

tff(c_28315,plain,(
    ! [A_30] :
      ( v1_funct_2('#skF_3',A_30,'#skF_3')
      | A_30 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28311,c_28311,c_28311,c_78])).

tff(c_29613,plain,(
    ! [A_30] :
      ( v1_funct_2('#skF_1',A_30,'#skF_1')
      | A_30 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29449,c_29449,c_29449,c_28315])).

tff(c_28319,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28311,c_28311,c_12])).

tff(c_29552,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29449,c_29449,c_28319])).

tff(c_29459,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29449,c_14789])).

tff(c_29615,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29552,c_29459])).

tff(c_29625,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_29615,c_18])).

tff(c_29574,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29449,c_29449,c_28316])).

tff(c_29634,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_29625,c_29574])).

tff(c_29460,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29449,c_14788])).

tff(c_29643,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29634,c_29460])).

tff(c_29669,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_29613,c_29643])).

tff(c_29673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29471,c_29669])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.02/4.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.37/4.85  
% 12.37/4.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.37/4.85  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.37/4.85  
% 12.37/4.85  %Foreground sorts:
% 12.37/4.85  
% 12.37/4.85  
% 12.37/4.85  %Background operators:
% 12.37/4.85  
% 12.37/4.85  
% 12.37/4.85  %Foreground operators:
% 12.37/4.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.37/4.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.37/4.85  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.37/4.85  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.37/4.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.37/4.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.37/4.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.37/4.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.37/4.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.37/4.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.37/4.85  tff('#skF_2', type, '#skF_2': $i).
% 12.37/4.85  tff('#skF_3', type, '#skF_3': $i).
% 12.37/4.85  tff('#skF_1', type, '#skF_1': $i).
% 12.37/4.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.37/4.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.37/4.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.37/4.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.37/4.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.37/4.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.37/4.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.37/4.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.37/4.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.37/4.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.37/4.85  
% 12.70/4.90  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.70/4.90  tff(f_145, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 12.70/4.90  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.70/4.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.70/4.90  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.70/4.90  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 12.70/4.90  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 12.70/4.90  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.70/4.90  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.70/4.90  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.70/4.90  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 12.70/4.90  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.70/4.90  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 12.70/4.90  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 12.70/4.90  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.70/4.90  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 12.70/4.90  tff(c_30, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.70/4.90  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 12.70/4.90  tff(c_197, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.70/4.90  tff(c_203, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_197])).
% 12.70/4.90  tff(c_210, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_203])).
% 12.70/4.90  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 12.70/4.90  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 12.70/4.90  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_145])).
% 12.70/4.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.70/4.90  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 12.70/4.90  tff(c_22063, plain, (![A_1484, B_1485, C_1486]: (k1_relset_1(A_1484, B_1485, C_1486)=k1_relat_1(C_1486) | ~m1_subset_1(C_1486, k1_zfmisc_1(k2_zfmisc_1(A_1484, B_1485))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.70/4.90  tff(c_22089, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_22063])).
% 12.70/4.90  tff(c_24928, plain, (![B_1626, A_1627, C_1628]: (k1_xboole_0=B_1626 | k1_relset_1(A_1627, B_1626, C_1628)=A_1627 | ~v1_funct_2(C_1628, A_1627, B_1626) | ~m1_subset_1(C_1628, k1_zfmisc_1(k2_zfmisc_1(A_1627, B_1626))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_24944, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_24928])).
% 12.70/4.90  tff(c_24959, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_22089, c_24944])).
% 12.70/4.90  tff(c_24963, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_24959])).
% 12.70/4.90  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.70/4.90  tff(c_127, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.70/4.90  tff(c_139, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_16, c_127])).
% 12.70/4.90  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.70/4.90  tff(c_22176, plain, (![A_1499, B_1500, C_1501]: (k2_relset_1(A_1499, B_1500, C_1501)=k2_relat_1(C_1501) | ~m1_subset_1(C_1501, k1_zfmisc_1(k2_zfmisc_1(A_1499, B_1500))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.70/4.90  tff(c_22189, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_22176])).
% 12.70/4.90  tff(c_22203, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_22189])).
% 12.70/4.90  tff(c_38, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.70/4.90  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.70/4.90  tff(c_32, plain, (![A_19]: (v1_funct_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.70/4.90  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 12.70/4.90  tff(c_148, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 12.70/4.90  tff(c_151, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_148])).
% 12.70/4.90  tff(c_154, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_151])).
% 12.70/4.90  tff(c_179, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.70/4.90  tff(c_185, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_179])).
% 12.70/4.90  tff(c_192, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_185])).
% 12.70/4.90  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_192])).
% 12.70/4.90  tff(c_195, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_66])).
% 12.70/4.90  tff(c_229, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_195])).
% 12.70/4.90  tff(c_233, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_229])).
% 12.70/4.90  tff(c_609, plain, (![A_116, B_117, C_118]: (k1_relset_1(A_116, B_117, C_118)=k1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.70/4.90  tff(c_628, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_609])).
% 12.70/4.90  tff(c_4835, plain, (![B_314, A_315, C_316]: (k1_xboole_0=B_314 | k1_relset_1(A_315, B_314, C_316)=A_315 | ~v1_funct_2(C_316, A_315, B_314) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_315, B_314))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_4848, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_4835])).
% 12.70/4.90  tff(c_4863, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_628, c_4848])).
% 12.70/4.90  tff(c_4867, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_4863])).
% 12.70/4.90  tff(c_1045, plain, (![B_162, A_163, C_164]: (k1_xboole_0=B_162 | k1_relset_1(A_163, B_162, C_164)=A_163 | ~v1_funct_2(C_164, A_163, B_162) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_1058, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_1045])).
% 12.70/4.90  tff(c_1076, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_628, c_1058])).
% 12.70/4.90  tff(c_1080, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1076])).
% 12.70/4.90  tff(c_36, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.70/4.90  tff(c_34, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.70/4.90  tff(c_762, plain, (![A_132, B_133, C_134]: (k2_relset_1(A_132, B_133, C_134)=k2_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.70/4.90  tff(c_772, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_762])).
% 12.70/4.90  tff(c_786, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_772])).
% 12.70/4.90  tff(c_502, plain, (![A_106]: (k1_relat_1(k2_funct_1(A_106))=k2_relat_1(A_106) | ~v2_funct_1(A_106) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.70/4.90  tff(c_258, plain, (![B_63, A_64]: (v4_relat_1(B_63, A_64) | ~r1_tarski(k1_relat_1(B_63), A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.70/4.90  tff(c_263, plain, (![B_63]: (v4_relat_1(B_63, k1_relat_1(B_63)) | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_6, c_258])).
% 12.70/4.90  tff(c_2328, plain, (![A_225]: (v4_relat_1(k2_funct_1(A_225), k2_relat_1(A_225)) | ~v1_relat_1(k2_funct_1(A_225)) | ~v2_funct_1(A_225) | ~v1_funct_1(A_225) | ~v1_relat_1(A_225))), inference(superposition, [status(thm), theory('equality')], [c_502, c_263])).
% 12.70/4.90  tff(c_2333, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_786, c_2328])).
% 12.70/4.90  tff(c_2339, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_70, c_2333])).
% 12.70/4.90  tff(c_2340, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2339])).
% 12.70/4.90  tff(c_2343, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_2340])).
% 12.70/4.90  tff(c_2347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_2343])).
% 12.70/4.90  tff(c_2349, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2339])).
% 12.70/4.90  tff(c_196, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 12.70/4.90  tff(c_2348, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_2339])).
% 12.70/4.90  tff(c_28, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.70/4.90  tff(c_3898, plain, (![A_277, A_278]: (r1_tarski(k2_relat_1(A_277), A_278) | ~v4_relat_1(k2_funct_1(A_277), A_278) | ~v1_relat_1(k2_funct_1(A_277)) | ~v2_funct_1(A_277) | ~v1_funct_1(A_277) | ~v1_relat_1(A_277))), inference(superposition, [status(thm), theory('equality')], [c_502, c_28])).
% 12.70/4.90  tff(c_3924, plain, (![A_279]: (r1_tarski(k2_relat_1(A_279), k1_relat_1(k2_funct_1(A_279))) | ~v2_funct_1(A_279) | ~v1_funct_1(A_279) | ~v1_relat_1(A_279) | ~v1_relat_1(k2_funct_1(A_279)))), inference(resolution, [status(thm)], [c_263, c_3898])).
% 12.70/4.90  tff(c_3938, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_786, c_3924])).
% 12.70/4.90  tff(c_3950, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2349, c_210, c_76, c_70, c_3938])).
% 12.70/4.90  tff(c_353, plain, (![B_83, A_84]: (r1_tarski(k1_relat_1(B_83), A_84) | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.70/4.90  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.70/4.90  tff(c_372, plain, (![B_83, A_84]: (k1_relat_1(B_83)=A_84 | ~r1_tarski(A_84, k1_relat_1(B_83)) | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_353, c_2])).
% 12.70/4.90  tff(c_3957, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3950, c_372])).
% 12.70/4.90  tff(c_3971, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2349, c_2348, c_3957])).
% 12.70/4.90  tff(c_669, plain, (![A_124]: (m1_subset_1(A_124, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_124), k2_relat_1(A_124)))) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.70/4.90  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.70/4.90  tff(c_703, plain, (![A_124]: (r1_tarski(A_124, k2_zfmisc_1(k1_relat_1(A_124), k2_relat_1(A_124))) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(resolution, [status(thm)], [c_669, c_18])).
% 12.70/4.90  tff(c_4069, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3971, c_703])).
% 12.70/4.90  tff(c_4161, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2349, c_196, c_4069])).
% 12.70/4.90  tff(c_4415, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_4161])).
% 12.70/4.90  tff(c_4432, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_70, c_1080, c_4415])).
% 12.70/4.90  tff(c_4434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_4432])).
% 12.70/4.90  tff(c_4435, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1076])).
% 12.70/4.90  tff(c_4466, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_4435, c_139])).
% 12.70/4.90  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.70/4.90  tff(c_4471, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4435, c_4435, c_12])).
% 12.70/4.90  tff(c_60, plain, (![A_33]: (m1_subset_1(A_33, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33), k2_relat_1(A_33)))) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.70/4.90  tff(c_794, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_786, c_60])).
% 12.70/4.90  tff(c_803, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_794])).
% 12.70/4.90  tff(c_844, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_803, c_18])).
% 12.70/4.90  tff(c_869, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_844, c_2])).
% 12.70/4.90  tff(c_925, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_869])).
% 12.70/4.90  tff(c_4629, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4471, c_925])).
% 12.70/4.90  tff(c_4639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4466, c_4629])).
% 12.70/4.90  tff(c_4640, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_869])).
% 12.70/4.90  tff(c_4872, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4867, c_4640])).
% 12.70/4.90  tff(c_138, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_127])).
% 12.70/4.90  tff(c_245, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.70/4.90  tff(c_252, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_138, c_245])).
% 12.70/4.90  tff(c_287, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_252])).
% 12.70/4.90  tff(c_4931, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4872, c_287])).
% 12.70/4.90  tff(c_4936, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4931])).
% 12.70/4.90  tff(c_4937, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4863])).
% 12.70/4.90  tff(c_4970, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_4937, c_139])).
% 12.70/4.90  tff(c_4975, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4937, c_4937, c_12])).
% 12.70/4.90  tff(c_5134, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4975, c_287])).
% 12.70/4.90  tff(c_5139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4970, c_5134])).
% 12.70/4.90  tff(c_5140, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_252])).
% 12.70/4.90  tff(c_5165, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5140, c_72])).
% 12.70/4.90  tff(c_5776, plain, (![A_398, B_399, C_400]: (k1_relset_1(A_398, B_399, C_400)=k1_relat_1(C_400) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.70/4.90  tff(c_5963, plain, (![C_411]: (k1_relset_1('#skF_1', '#skF_2', C_411)=k1_relat_1(C_411) | ~m1_subset_1(C_411, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5140, c_5776])).
% 12.70/4.90  tff(c_5975, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5165, c_5963])).
% 12.70/4.90  tff(c_7004, plain, (![B_481, A_482, C_483]: (k1_xboole_0=B_481 | k1_relset_1(A_482, B_481, C_483)=A_482 | ~v1_funct_2(C_483, A_482, B_481) | ~m1_subset_1(C_483, k1_zfmisc_1(k2_zfmisc_1(A_482, B_481))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_7013, plain, (![C_483]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_483)='#skF_1' | ~v1_funct_2(C_483, '#skF_1', '#skF_2') | ~m1_subset_1(C_483, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5140, c_7004])).
% 12.70/4.90  tff(c_7067, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_7013])).
% 12.70/4.90  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.70/4.90  tff(c_5176, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5140, c_10])).
% 12.70/4.90  tff(c_5195, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_5176])).
% 12.70/4.90  tff(c_7097, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7067, c_5195])).
% 12.70/4.90  tff(c_7289, plain, (![A_495]: (k2_zfmisc_1(A_495, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7067, c_7067, c_12])).
% 12.70/4.90  tff(c_6444, plain, (![B_461, C_462, A_463]: (k1_xboole_0=B_461 | v1_funct_2(C_462, A_463, B_461) | k1_relset_1(A_463, B_461, C_462)!=A_463 | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(A_463, B_461))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_6453, plain, (![C_462]: (k1_xboole_0='#skF_2' | v1_funct_2(C_462, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_462)!='#skF_1' | ~m1_subset_1(C_462, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5140, c_6444])).
% 12.70/4.90  tff(c_6532, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6453])).
% 12.70/4.90  tff(c_6571, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_6532, c_139])).
% 12.70/4.90  tff(c_6576, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6532, c_6532, c_12])).
% 12.70/4.90  tff(c_5628, plain, (![A_380, B_381, C_382]: (k2_relset_1(A_380, B_381, C_382)=k2_relat_1(C_382) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_380, B_381))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.70/4.90  tff(c_5833, plain, (![C_407]: (k2_relset_1('#skF_1', '#skF_2', C_407)=k2_relat_1(C_407) | ~m1_subset_1(C_407, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5140, c_5628])).
% 12.70/4.90  tff(c_5836, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5165, c_5833])).
% 12.70/4.90  tff(c_5846, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5836])).
% 12.70/4.90  tff(c_5501, plain, (![A_371]: (m1_subset_1(A_371, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_371), k2_relat_1(A_371)))) | ~v1_funct_1(A_371) | ~v1_relat_1(A_371))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.70/4.90  tff(c_5531, plain, (![A_371]: (r1_tarski(A_371, k2_zfmisc_1(k1_relat_1(A_371), k2_relat_1(A_371))) | ~v1_funct_1(A_371) | ~v1_relat_1(A_371))), inference(resolution, [status(thm)], [c_5501, c_18])).
% 12.70/4.90  tff(c_5853, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5846, c_5531])).
% 12.70/4.90  tff(c_5866, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_5853])).
% 12.70/4.90  tff(c_5888, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_5866, c_2])).
% 12.70/4.90  tff(c_6167, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5888])).
% 12.70/4.90  tff(c_6857, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6576, c_6167])).
% 12.70/4.90  tff(c_6863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6571, c_6857])).
% 12.70/4.90  tff(c_6865, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_6453])).
% 12.70/4.90  tff(c_6275, plain, (![B_444, A_445, C_446]: (k1_xboole_0=B_444 | k1_relset_1(A_445, B_444, C_446)=A_445 | ~v1_funct_2(C_446, A_445, B_444) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_445, B_444))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_6284, plain, (![C_446]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_446)='#skF_1' | ~v1_funct_2(C_446, '#skF_1', '#skF_2') | ~m1_subset_1(C_446, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5140, c_6275])).
% 12.70/4.90  tff(c_6903, plain, (![C_478]: (k1_relset_1('#skF_1', '#skF_2', C_478)='#skF_1' | ~v1_funct_2(C_478, '#skF_1', '#skF_2') | ~m1_subset_1(C_478, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_6865, c_6284])).
% 12.70/4.90  tff(c_6906, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5165, c_6903])).
% 12.70/4.90  tff(c_6917, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5975, c_6906])).
% 12.70/4.90  tff(c_6921, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6917, c_6167])).
% 12.70/4.90  tff(c_6932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5140, c_6921])).
% 12.70/4.90  tff(c_6933, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_5888])).
% 12.70/4.90  tff(c_7302, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7289, c_6933])).
% 12.70/4.90  tff(c_7365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7097, c_7302])).
% 12.70/4.90  tff(c_7521, plain, (![C_507]: (k1_relset_1('#skF_1', '#skF_2', C_507)='#skF_1' | ~v1_funct_2(C_507, '#skF_1', '#skF_2') | ~m1_subset_1(C_507, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_7013])).
% 12.70/4.90  tff(c_7524, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5165, c_7521])).
% 12.70/4.90  tff(c_7535, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5975, c_7524])).
% 12.70/4.90  tff(c_5142, plain, (![C_325, A_326, B_327]: (v4_relat_1(C_325, A_326) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.70/4.90  tff(c_5285, plain, (![A_346, A_347, B_348]: (v4_relat_1(A_346, A_347) | ~r1_tarski(A_346, k2_zfmisc_1(A_347, B_348)))), inference(resolution, [status(thm)], [c_20, c_5142])).
% 12.70/4.90  tff(c_5605, plain, (![B_377, A_378, B_379]: (v4_relat_1(k1_relat_1(B_377), A_378) | ~v4_relat_1(B_377, k2_zfmisc_1(A_378, B_379)) | ~v1_relat_1(B_377))), inference(resolution, [status(thm)], [c_28, c_5285])).
% 12.70/4.90  tff(c_5697, plain, (![B_389]: (v4_relat_1(k1_relat_1(B_389), '#skF_1') | ~v4_relat_1(B_389, '#skF_3') | ~v1_relat_1(B_389))), inference(superposition, [status(thm), theory('equality')], [c_5140, c_5605])).
% 12.70/4.90  tff(c_6095, plain, (![A_427]: (v4_relat_1(k2_relat_1(A_427), '#skF_1') | ~v4_relat_1(k2_funct_1(A_427), '#skF_3') | ~v1_relat_1(k2_funct_1(A_427)) | ~v2_funct_1(A_427) | ~v1_funct_1(A_427) | ~v1_relat_1(A_427))), inference(superposition, [status(thm), theory('equality')], [c_38, c_5697])).
% 12.70/4.90  tff(c_6100, plain, (v4_relat_1('#skF_2', '#skF_1') | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5846, c_6095])).
% 12.70/4.90  tff(c_6106, plain, (v4_relat_1('#skF_2', '#skF_1') | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_70, c_6100])).
% 12.70/4.90  tff(c_6128, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6106])).
% 12.70/4.90  tff(c_6131, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_6128])).
% 12.70/4.90  tff(c_6135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_6131])).
% 12.70/4.90  tff(c_6137, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6106])).
% 12.70/4.90  tff(c_5382, plain, (![A_358]: (k1_relat_1(k2_funct_1(A_358))=k2_relat_1(A_358) | ~v2_funct_1(A_358) | ~v1_funct_1(A_358) | ~v1_relat_1(A_358))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.70/4.90  tff(c_8997, plain, (![A_572]: (v4_relat_1(k2_funct_1(A_572), k2_relat_1(A_572)) | ~v1_relat_1(k2_funct_1(A_572)) | ~v2_funct_1(A_572) | ~v1_funct_1(A_572) | ~v1_relat_1(A_572))), inference(superposition, [status(thm), theory('equality')], [c_5382, c_263])).
% 12.70/4.90  tff(c_9002, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5846, c_8997])).
% 12.70/4.90  tff(c_9008, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_70, c_6137, c_9002])).
% 12.70/4.90  tff(c_9143, plain, (![A_578, A_579]: (r1_tarski(k2_relat_1(A_578), A_579) | ~v4_relat_1(k2_funct_1(A_578), A_579) | ~v1_relat_1(k2_funct_1(A_578)) | ~v2_funct_1(A_578) | ~v1_funct_1(A_578) | ~v1_relat_1(A_578))), inference(superposition, [status(thm), theory('equality')], [c_5382, c_28])).
% 12.70/4.90  tff(c_9527, plain, (![A_595]: (r1_tarski(k2_relat_1(A_595), k1_relat_1(k2_funct_1(A_595))) | ~v2_funct_1(A_595) | ~v1_funct_1(A_595) | ~v1_relat_1(A_595) | ~v1_relat_1(k2_funct_1(A_595)))), inference(resolution, [status(thm)], [c_263, c_9143])).
% 12.70/4.90  tff(c_9538, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5846, c_9527])).
% 12.70/4.90  tff(c_9549, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6137, c_210, c_76, c_70, c_9538])).
% 12.70/4.90  tff(c_5209, plain, (![B_331, A_332]: (r1_tarski(k1_relat_1(B_331), A_332) | ~v4_relat_1(B_331, A_332) | ~v1_relat_1(B_331))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.70/4.90  tff(c_5223, plain, (![B_331, A_332]: (k1_relat_1(B_331)=A_332 | ~r1_tarski(A_332, k1_relat_1(B_331)) | ~v4_relat_1(B_331, A_332) | ~v1_relat_1(B_331))), inference(resolution, [status(thm)], [c_5209, c_2])).
% 12.70/4.90  tff(c_9553, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_9549, c_5223])).
% 12.70/4.90  tff(c_9564, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6137, c_9008, c_9553])).
% 12.70/4.90  tff(c_9657, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9564, c_5531])).
% 12.70/4.90  tff(c_9739, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_6137, c_196, c_9657])).
% 12.70/4.90  tff(c_9955, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_9739])).
% 12.70/4.90  tff(c_9973, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_70, c_7535, c_9955])).
% 12.70/4.90  tff(c_9975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_9973])).
% 12.70/4.90  tff(c_9977, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5176])).
% 12.70/4.90  tff(c_9984, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9977, c_9977, c_14])).
% 12.70/4.90  tff(c_9976, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5176])).
% 12.70/4.90  tff(c_10029, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9977, c_9977, c_9976])).
% 12.70/4.90  tff(c_10030, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_10029])).
% 12.70/4.90  tff(c_10032, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10030, c_233])).
% 12.70/4.90  tff(c_10135, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9984, c_10032])).
% 12.70/4.90  tff(c_9987, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_9977, c_16])).
% 12.70/4.90  tff(c_10429, plain, (![A_651, B_652, C_653]: (k2_relset_1(A_651, B_652, C_653)=k2_relat_1(C_653) | ~m1_subset_1(C_653, k1_zfmisc_1(k2_zfmisc_1(A_651, B_652))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.70/4.90  tff(c_10450, plain, (![A_654, B_655]: (k2_relset_1(A_654, B_655, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_9987, c_10429])).
% 12.70/4.90  tff(c_10034, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10030, c_10030, c_68])).
% 12.70/4.90  tff(c_10454, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_10450, c_10034])).
% 12.70/4.90  tff(c_10202, plain, (![A_629]: (k1_relat_1(k2_funct_1(A_629))=k2_relat_1(A_629) | ~v2_funct_1(A_629) | ~v1_funct_1(A_629) | ~v1_relat_1(A_629))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.70/4.90  tff(c_12045, plain, (![A_771]: (v4_relat_1(k2_funct_1(A_771), k2_relat_1(A_771)) | ~v1_relat_1(k2_funct_1(A_771)) | ~v2_funct_1(A_771) | ~v1_funct_1(A_771) | ~v1_relat_1(A_771))), inference(superposition, [status(thm), theory('equality')], [c_10202, c_263])).
% 12.70/4.90  tff(c_12053, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10454, c_12045])).
% 12.70/4.90  tff(c_12061, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_70, c_12053])).
% 12.70/4.90  tff(c_12062, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_12061])).
% 12.70/4.90  tff(c_12065, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_12062])).
% 12.70/4.90  tff(c_12069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_12065])).
% 12.70/4.90  tff(c_12071, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_12061])).
% 12.70/4.90  tff(c_12070, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_12061])).
% 12.70/4.90  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.70/4.90  tff(c_10112, plain, (![A_610]: (A_610='#skF_3' | ~r1_tarski(A_610, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9977, c_9977, c_8])).
% 12.70/4.90  tff(c_10127, plain, (![B_16]: (k1_relat_1(B_16)='#skF_3' | ~v4_relat_1(B_16, '#skF_3') | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_28, c_10112])).
% 12.70/4.90  tff(c_12079, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_12070, c_10127])).
% 12.70/4.90  tff(c_12088, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12071, c_12079])).
% 12.70/4.90  tff(c_10287, plain, (![A_640]: (m1_subset_1(A_640, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_640), k2_relat_1(A_640)))) | ~v1_funct_1(A_640) | ~v1_relat_1(A_640))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.70/4.90  tff(c_10314, plain, (![A_640]: (r1_tarski(A_640, k2_zfmisc_1(k1_relat_1(A_640), k2_relat_1(A_640))) | ~v1_funct_1(A_640) | ~v1_relat_1(A_640))), inference(resolution, [status(thm)], [c_10287, c_18])).
% 12.70/4.90  tff(c_12162, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12088, c_10314])).
% 12.70/4.90  tff(c_12228, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12071, c_196, c_9984, c_12162])).
% 12.70/4.90  tff(c_12230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10135, c_12228])).
% 12.70/4.90  tff(c_12231, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_10029])).
% 12.70/4.90  tff(c_9986, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9977, c_9977, c_12])).
% 12.70/4.90  tff(c_12304, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12231, c_12231, c_9986])).
% 12.70/4.90  tff(c_12240, plain, (~r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12231, c_233])).
% 12.70/4.90  tff(c_12403, plain, (~r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12304, c_12240])).
% 12.70/4.90  tff(c_12242, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12231, c_210])).
% 12.70/4.90  tff(c_12247, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12231, c_76])).
% 12.70/4.90  tff(c_12246, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12231, c_70])).
% 12.70/4.90  tff(c_12287, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12231, c_12231, c_9984])).
% 12.70/4.90  tff(c_12462, plain, (![A_800, A_801, B_802]: (v4_relat_1(A_800, A_801) | ~r1_tarski(A_800, k2_zfmisc_1(A_801, B_802)))), inference(resolution, [status(thm)], [c_20, c_5142])).
% 12.70/4.90  tff(c_12484, plain, (![A_801, B_802]: (v4_relat_1(k2_zfmisc_1(A_801, B_802), A_801))), inference(resolution, [status(thm)], [c_6, c_12462])).
% 12.70/4.90  tff(c_9983, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9977, c_9977, c_8])).
% 12.70/4.90  tff(c_12363, plain, (![A_782]: (A_782='#skF_1' | ~r1_tarski(A_782, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12231, c_12231, c_9983])).
% 12.70/4.90  tff(c_12562, plain, (![B_817]: (k1_relat_1(B_817)='#skF_1' | ~v4_relat_1(B_817, '#skF_1') | ~v1_relat_1(B_817))), inference(resolution, [status(thm)], [c_28, c_12363])).
% 12.70/4.90  tff(c_12566, plain, (![B_802]: (k1_relat_1(k2_zfmisc_1('#skF_1', B_802))='#skF_1' | ~v1_relat_1(k2_zfmisc_1('#skF_1', B_802)))), inference(resolution, [status(thm)], [c_12484, c_12562])).
% 12.70/4.90  tff(c_12577, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12287, c_12566])).
% 12.70/4.90  tff(c_12334, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_12231, c_9987])).
% 12.70/4.90  tff(c_12607, plain, (![A_818, B_819, C_820]: (k2_relset_1(A_818, B_819, C_820)=k2_relat_1(C_820) | ~m1_subset_1(C_820, k1_zfmisc_1(k2_zfmisc_1(A_818, B_819))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.70/4.90  tff(c_12673, plain, (![A_824, B_825]: (k2_relset_1(A_824, B_825, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_12334, c_12607])).
% 12.70/4.90  tff(c_12244, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12231, c_68])).
% 12.70/4.90  tff(c_12677, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_12673, c_12244])).
% 12.70/4.90  tff(c_12382, plain, (![A_783]: (k1_relat_1(k2_funct_1(A_783))=k2_relat_1(A_783) | ~v2_funct_1(A_783) | ~v1_funct_1(A_783) | ~v1_relat_1(A_783))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.70/4.90  tff(c_14117, plain, (![A_935]: (v4_relat_1(k2_funct_1(A_935), k2_relat_1(A_935)) | ~v1_relat_1(k2_funct_1(A_935)) | ~v2_funct_1(A_935) | ~v1_funct_1(A_935) | ~v1_relat_1(A_935))), inference(superposition, [status(thm), theory('equality')], [c_12382, c_263])).
% 12.70/4.90  tff(c_14122, plain, (v4_relat_1(k2_funct_1('#skF_1'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12677, c_14117])).
% 12.70/4.90  tff(c_14128, plain, (v4_relat_1(k2_funct_1('#skF_1'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12242, c_12247, c_12246, c_14122])).
% 12.70/4.90  tff(c_14129, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_14128])).
% 12.70/4.90  tff(c_14132, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_14129])).
% 12.70/4.90  tff(c_14136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12242, c_12247, c_14132])).
% 12.70/4.90  tff(c_14138, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_14128])).
% 12.70/4.90  tff(c_12243, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12231, c_196])).
% 12.70/4.90  tff(c_14137, plain, (v4_relat_1(k2_funct_1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_14128])).
% 12.70/4.90  tff(c_14157, plain, (![A_936, A_937]: (r1_tarski(k2_relat_1(A_936), A_937) | ~v4_relat_1(k2_funct_1(A_936), A_937) | ~v1_relat_1(k2_funct_1(A_936)) | ~v2_funct_1(A_936) | ~v1_funct_1(A_936) | ~v1_relat_1(A_936))), inference(superposition, [status(thm), theory('equality')], [c_12382, c_28])).
% 12.70/4.90  tff(c_14387, plain, (![A_946]: (r1_tarski(k2_relat_1(A_946), k1_relat_1(k2_funct_1(A_946))) | ~v2_funct_1(A_946) | ~v1_funct_1(A_946) | ~v1_relat_1(A_946) | ~v1_relat_1(k2_funct_1(A_946)))), inference(resolution, [status(thm)], [c_263, c_14157])).
% 12.70/4.90  tff(c_14398, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_1'))) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12677, c_14387])).
% 12.70/4.90  tff(c_14409, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14138, c_12242, c_12247, c_12246, c_14398])).
% 12.70/4.90  tff(c_9993, plain, (![B_600, A_601]: (r1_tarski(k1_relat_1(B_600), A_601) | ~v4_relat_1(B_600, A_601) | ~v1_relat_1(B_600))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.70/4.90  tff(c_10003, plain, (![B_600, A_601]: (k1_relat_1(B_600)=A_601 | ~r1_tarski(A_601, k1_relat_1(B_600)) | ~v4_relat_1(B_600, A_601) | ~v1_relat_1(B_600))), inference(resolution, [status(thm)], [c_9993, c_2])).
% 12.70/4.90  tff(c_14413, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_2' | ~v4_relat_1(k2_funct_1('#skF_1'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_14409, c_10003])).
% 12.70/4.90  tff(c_14424, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14138, c_14137, c_14413])).
% 12.70/4.90  tff(c_12632, plain, (![A_823]: (m1_subset_1(A_823, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_823), k2_relat_1(A_823)))) | ~v1_funct_1(A_823) | ~v1_relat_1(A_823))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.70/4.90  tff(c_12670, plain, (![A_823]: (r1_tarski(A_823, k2_zfmisc_1(k1_relat_1(A_823), k2_relat_1(A_823))) | ~v1_funct_1(A_823) | ~v1_relat_1(A_823))), inference(resolution, [status(thm)], [c_12632, c_18])).
% 12.70/4.90  tff(c_14502, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_1')))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_14424, c_12670])).
% 12.70/4.90  tff(c_14574, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_14138, c_12243, c_14502])).
% 12.70/4.90  tff(c_14773, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_1'))) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_14574])).
% 12.70/4.90  tff(c_14785, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12242, c_12247, c_12246, c_12304, c_12577, c_14773])).
% 12.70/4.90  tff(c_14787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12403, c_14785])).
% 12.70/4.90  tff(c_14788, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_195])).
% 12.70/4.90  tff(c_16250, plain, (![A_1102, B_1103, C_1104]: (k2_relset_1(A_1102, B_1103, C_1104)=k2_relat_1(C_1104) | ~m1_subset_1(C_1104, k1_zfmisc_1(k2_zfmisc_1(A_1102, B_1103))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.70/4.90  tff(c_16260, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_16250])).
% 12.70/4.90  tff(c_16274, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16260])).
% 12.70/4.90  tff(c_14789, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_195])).
% 12.70/4.90  tff(c_16119, plain, (![A_1084, B_1085, C_1086]: (k1_relset_1(A_1084, B_1085, C_1086)=k1_relat_1(C_1086) | ~m1_subset_1(C_1086, k1_zfmisc_1(k2_zfmisc_1(A_1084, B_1085))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.70/4.90  tff(c_16140, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14789, c_16119])).
% 12.70/4.90  tff(c_16665, plain, (![B_1139, C_1140, A_1141]: (k1_xboole_0=B_1139 | v1_funct_2(C_1140, A_1141, B_1139) | k1_relset_1(A_1141, B_1139, C_1140)!=A_1141 | ~m1_subset_1(C_1140, k1_zfmisc_1(k2_zfmisc_1(A_1141, B_1139))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_16674, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_14789, c_16665])).
% 12.70/4.90  tff(c_16697, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16140, c_16674])).
% 12.70/4.90  tff(c_16698, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_14788, c_16697])).
% 12.70/4.90  tff(c_16705, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_16698])).
% 12.70/4.90  tff(c_16708, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_16705])).
% 12.70/4.90  tff(c_16711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_70, c_16274, c_16708])).
% 12.70/4.90  tff(c_16712, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_16698])).
% 12.70/4.90  tff(c_16743, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_16712, c_139])).
% 12.70/4.90  tff(c_16748, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16712, c_16712, c_12])).
% 12.70/4.90  tff(c_14799, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_14789, c_18])).
% 12.70/4.90  tff(c_14817, plain, (![B_954, A_955]: (B_954=A_955 | ~r1_tarski(B_954, A_955) | ~r1_tarski(A_955, B_954))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.70/4.90  tff(c_14826, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14799, c_14817])).
% 12.70/4.90  tff(c_14926, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_14826])).
% 12.70/4.90  tff(c_16926, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16748, c_14926])).
% 12.70/4.90  tff(c_16931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16743, c_16926])).
% 12.70/4.90  tff(c_16932, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_14826])).
% 12.70/4.90  tff(c_22978, plain, (![B_1548, C_1549, A_1550]: (k1_xboole_0=B_1548 | v1_funct_2(C_1549, A_1550, B_1548) | k1_relset_1(A_1550, B_1548, C_1549)!=A_1550 | ~m1_subset_1(C_1549, k1_zfmisc_1(k2_zfmisc_1(A_1550, B_1548))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_22984, plain, (![C_1549]: (k1_xboole_0='#skF_1' | v1_funct_2(C_1549, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_1549)!='#skF_2' | ~m1_subset_1(C_1549, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_16932, c_22978])).
% 12.70/4.90  tff(c_23170, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_22984])).
% 12.70/4.90  tff(c_22769, plain, (![B_1543, A_1544, C_1545]: (k1_xboole_0=B_1543 | k1_relset_1(A_1544, B_1543, C_1545)=A_1544 | ~v1_funct_2(C_1545, A_1544, B_1543) | ~m1_subset_1(C_1545, k1_zfmisc_1(k2_zfmisc_1(A_1544, B_1543))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_22785, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_22769])).
% 12.70/4.90  tff(c_22803, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_22089, c_22785])).
% 12.70/4.90  tff(c_22807, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_22803])).
% 12.70/4.90  tff(c_26, plain, (![B_16, A_15]: (v4_relat_1(B_16, A_15) | ~r1_tarski(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.70/4.90  tff(c_22872, plain, (![A_15]: (v4_relat_1('#skF_3', A_15) | ~r1_tarski('#skF_1', A_15) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22807, c_26])).
% 12.70/4.90  tff(c_22937, plain, (![A_1547]: (v4_relat_1('#skF_3', A_1547) | ~r1_tarski('#skF_1', A_1547))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_22872])).
% 12.70/4.90  tff(c_17572, plain, (![A_1216, B_1217, C_1218]: (k2_relset_1(A_1216, B_1217, C_1218)=k2_relat_1(C_1218) | ~m1_subset_1(C_1218, k1_zfmisc_1(k2_zfmisc_1(A_1216, B_1217))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.70/4.90  tff(c_17585, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_17572])).
% 12.70/4.90  tff(c_17599, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_17585])).
% 12.70/4.90  tff(c_14833, plain, (![C_956, A_957, B_958]: (v4_relat_1(C_956, A_957) | ~m1_subset_1(C_956, k1_zfmisc_1(k2_zfmisc_1(A_957, B_958))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.70/4.90  tff(c_14856, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_14833])).
% 12.70/4.90  tff(c_14871, plain, (![B_964, A_965]: (r1_tarski(k1_relat_1(B_964), A_965) | ~v4_relat_1(B_964, A_965) | ~v1_relat_1(B_964))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.70/4.90  tff(c_207, plain, (![A_7, B_8]: (v1_relat_1(A_7) | ~v1_relat_1(B_8) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_20, c_197])).
% 12.70/4.90  tff(c_17250, plain, (![B_1186, A_1187]: (v1_relat_1(k1_relat_1(B_1186)) | ~v1_relat_1(A_1187) | ~v4_relat_1(B_1186, A_1187) | ~v1_relat_1(B_1186))), inference(resolution, [status(thm)], [c_14871, c_207])).
% 12.70/4.90  tff(c_17264, plain, (v1_relat_1(k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14856, c_17250])).
% 12.70/4.90  tff(c_17279, plain, (v1_relat_1(k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_17264])).
% 12.70/4.90  tff(c_17280, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_17279])).
% 12.70/4.90  tff(c_18299, plain, (![B_1276, C_1277, A_1278]: (k1_xboole_0=B_1276 | v1_funct_2(C_1277, A_1278, B_1276) | k1_relset_1(A_1278, B_1276, C_1277)!=A_1278 | ~m1_subset_1(C_1277, k1_zfmisc_1(k2_zfmisc_1(A_1278, B_1276))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_18308, plain, (![C_1277]: (k1_xboole_0='#skF_1' | v1_funct_2(C_1277, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_1277)!='#skF_2' | ~m1_subset_1(C_1277, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_16932, c_18299])).
% 12.70/4.90  tff(c_18462, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_18308])).
% 12.70/4.90  tff(c_86, plain, (![A_38]: (k2_zfmisc_1(A_38, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.70/4.90  tff(c_90, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_86, c_30])).
% 12.70/4.90  tff(c_18505, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18462, c_90])).
% 12.70/4.90  tff(c_18509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17280, c_18505])).
% 12.70/4.90  tff(c_18511, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_18308])).
% 12.70/4.90  tff(c_17851, plain, (![A_1240, B_1241, C_1242]: (k1_relset_1(A_1240, B_1241, C_1242)=k1_relat_1(C_1242) | ~m1_subset_1(C_1242, k1_zfmisc_1(k2_zfmisc_1(A_1240, B_1241))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.70/4.90  tff(c_17990, plain, (![A_1257, B_1258, A_1259]: (k1_relset_1(A_1257, B_1258, A_1259)=k1_relat_1(A_1259) | ~r1_tarski(A_1259, k2_zfmisc_1(A_1257, B_1258)))), inference(resolution, [status(thm)], [c_20, c_17851])).
% 12.70/4.90  tff(c_18029, plain, (![A_1257, B_1258]: (k1_relset_1(A_1257, B_1258, k2_zfmisc_1(A_1257, B_1258))=k1_relat_1(k2_zfmisc_1(A_1257, B_1258)))), inference(resolution, [status(thm)], [c_6, c_17990])).
% 12.70/4.90  tff(c_18988, plain, (![B_1305, A_1306, A_1307]: (k1_xboole_0=B_1305 | v1_funct_2(A_1306, A_1307, B_1305) | k1_relset_1(A_1307, B_1305, A_1306)!=A_1307 | ~r1_tarski(A_1306, k2_zfmisc_1(A_1307, B_1305)))), inference(resolution, [status(thm)], [c_20, c_18299])).
% 12.70/4.90  tff(c_19015, plain, (![B_1305, A_1307]: (k1_xboole_0=B_1305 | v1_funct_2(k2_zfmisc_1(A_1307, B_1305), A_1307, B_1305) | k1_relset_1(A_1307, B_1305, k2_zfmisc_1(A_1307, B_1305))!=A_1307)), inference(resolution, [status(thm)], [c_6, c_18988])).
% 12.70/4.90  tff(c_19027, plain, (![B_1308, A_1309]: (k1_xboole_0=B_1308 | v1_funct_2(k2_zfmisc_1(A_1309, B_1308), A_1309, B_1308) | k1_relat_1(k2_zfmisc_1(A_1309, B_1308))!=A_1309)), inference(demodulation, [status(thm), theory('equality')], [c_18029, c_19015])).
% 12.70/4.90  tff(c_19039, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_16932, c_19027])).
% 12.70/4.90  tff(c_19054, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16932, c_19039])).
% 12.70/4.90  tff(c_19055, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_14788, c_18511, c_19054])).
% 12.70/4.90  tff(c_19061, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_19055])).
% 12.70/4.90  tff(c_19064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_70, c_17599, c_19061])).
% 12.70/4.90  tff(c_19065, plain, (v1_relat_1(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_17279])).
% 12.70/4.90  tff(c_14860, plain, (![C_960, A_961]: (v4_relat_1(C_960, A_961) | ~m1_subset_1(C_960, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_14833])).
% 12.70/4.90  tff(c_14867, plain, (![A_7, A_961]: (v4_relat_1(A_7, A_961) | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_14860])).
% 12.70/4.90  tff(c_17052, plain, (![B_1163]: (k1_relat_1(B_1163)=k1_xboole_0 | ~v4_relat_1(B_1163, k1_xboole_0) | ~v1_relat_1(B_1163))), inference(resolution, [status(thm)], [c_14871, c_8])).
% 12.70/4.90  tff(c_17178, plain, (![A_1172]: (k1_relat_1(A_1172)=k1_xboole_0 | ~v1_relat_1(A_1172) | ~r1_tarski(A_1172, k1_xboole_0))), inference(resolution, [status(thm)], [c_14867, c_17052])).
% 12.70/4.90  tff(c_22729, plain, (![B_1542]: (k1_relat_1(k1_relat_1(B_1542))=k1_xboole_0 | ~v1_relat_1(k1_relat_1(B_1542)) | ~v4_relat_1(B_1542, k1_xboole_0) | ~v1_relat_1(B_1542))), inference(resolution, [status(thm)], [c_28, c_17178])).
% 12.70/4.90  tff(c_22747, plain, (k1_relat_1(k1_relat_1('#skF_3'))=k1_xboole_0 | ~v4_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_19065, c_22729])).
% 12.70/4.90  tff(c_22761, plain, (k1_relat_1(k1_relat_1('#skF_3'))=k1_xboole_0 | ~v4_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_210, c_22747])).
% 12.70/4.90  tff(c_22764, plain, (~v4_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_22761])).
% 12.70/4.90  tff(c_22961, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_22937, c_22764])).
% 12.70/4.90  tff(c_23178, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23170, c_22961])).
% 12.70/4.90  tff(c_23225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_23178])).
% 12.70/4.90  tff(c_23227, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_22984])).
% 12.70/4.90  tff(c_22496, plain, (![A_1527, B_1528, A_1529]: (k1_relset_1(A_1527, B_1528, A_1529)=k1_relat_1(A_1529) | ~r1_tarski(A_1529, k2_zfmisc_1(A_1527, B_1528)))), inference(resolution, [status(thm)], [c_20, c_22063])).
% 12.70/4.90  tff(c_22535, plain, (![A_1527, B_1528]: (k1_relset_1(A_1527, B_1528, k2_zfmisc_1(A_1527, B_1528))=k1_relat_1(k2_zfmisc_1(A_1527, B_1528)))), inference(resolution, [status(thm)], [c_6, c_22496])).
% 12.70/4.90  tff(c_23550, plain, (![B_1575, A_1576, A_1577]: (k1_xboole_0=B_1575 | v1_funct_2(A_1576, A_1577, B_1575) | k1_relset_1(A_1577, B_1575, A_1576)!=A_1577 | ~r1_tarski(A_1576, k2_zfmisc_1(A_1577, B_1575)))), inference(resolution, [status(thm)], [c_20, c_22978])).
% 12.70/4.90  tff(c_23577, plain, (![B_1575, A_1577]: (k1_xboole_0=B_1575 | v1_funct_2(k2_zfmisc_1(A_1577, B_1575), A_1577, B_1575) | k1_relset_1(A_1577, B_1575, k2_zfmisc_1(A_1577, B_1575))!=A_1577)), inference(resolution, [status(thm)], [c_6, c_23550])).
% 12.70/4.90  tff(c_23590, plain, (![B_1578, A_1579]: (k1_xboole_0=B_1578 | v1_funct_2(k2_zfmisc_1(A_1579, B_1578), A_1579, B_1578) | k1_relat_1(k2_zfmisc_1(A_1579, B_1578))!=A_1579)), inference(demodulation, [status(thm), theory('equality')], [c_22535, c_23577])).
% 12.70/4.90  tff(c_23602, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_16932, c_23590])).
% 12.70/4.90  tff(c_23617, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16932, c_23602])).
% 12.70/4.90  tff(c_23618, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_14788, c_23227, c_23617])).
% 12.70/4.90  tff(c_23624, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_23618])).
% 12.70/4.90  tff(c_23627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_70, c_22203, c_23624])).
% 12.70/4.90  tff(c_23628, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_22803])).
% 12.70/4.90  tff(c_23667, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_23628, c_139])).
% 12.70/4.90  tff(c_23672, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_23628, c_23628, c_12])).
% 12.70/4.90  tff(c_21878, plain, (![A_1467]: (m1_subset_1(A_1467, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1467), k2_relat_1(A_1467)))) | ~v1_funct_1(A_1467) | ~v1_relat_1(A_1467))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.70/4.90  tff(c_21908, plain, (![A_1467]: (r1_tarski(A_1467, k2_zfmisc_1(k1_relat_1(A_1467), k2_relat_1(A_1467))) | ~v1_funct_1(A_1467) | ~v1_relat_1(A_1467))), inference(resolution, [status(thm)], [c_21878, c_18])).
% 12.70/4.90  tff(c_22210, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22203, c_21908])).
% 12.70/4.90  tff(c_22223, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_22210])).
% 12.70/4.90  tff(c_22252, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_22223, c_2])).
% 12.70/4.90  tff(c_22350, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_22252])).
% 12.70/4.90  tff(c_24255, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23672, c_22350])).
% 12.70/4.90  tff(c_24265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23667, c_24255])).
% 12.70/4.90  tff(c_24267, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_22761])).
% 12.70/4.90  tff(c_14883, plain, (![B_964]: (k1_relat_1(B_964)=k1_xboole_0 | ~v4_relat_1(B_964, k1_xboole_0) | ~v1_relat_1(B_964))), inference(resolution, [status(thm)], [c_14871, c_8])).
% 12.70/4.90  tff(c_24272, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24267, c_14883])).
% 12.70/4.90  tff(c_24278, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_210, c_24272])).
% 12.70/4.90  tff(c_24279, plain, (~r1_tarski(k2_zfmisc_1(k1_xboole_0, '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24278, c_22350])).
% 12.70/4.90  tff(c_24291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_14, c_24279])).
% 12.70/4.90  tff(c_24292, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_22252])).
% 12.70/4.90  tff(c_24967, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24963, c_24292])).
% 12.70/4.90  tff(c_14827, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_138, c_14817])).
% 12.70/4.90  tff(c_14858, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_14827])).
% 12.70/4.90  tff(c_25062, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24967, c_14858])).
% 12.70/4.90  tff(c_25067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_25062])).
% 12.70/4.90  tff(c_25068, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24959])).
% 12.70/4.90  tff(c_25107, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_25068, c_139])).
% 12.70/4.90  tff(c_25112, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25068, c_25068, c_12])).
% 12.70/4.90  tff(c_25238, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25112, c_14858])).
% 12.70/4.90  tff(c_25243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25107, c_25238])).
% 12.70/4.90  tff(c_25244, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_14827])).
% 12.70/4.90  tff(c_25248, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_25244, c_72])).
% 12.70/4.90  tff(c_27281, plain, (![A_1817, B_1818, C_1819]: (k2_relset_1(A_1817, B_1818, C_1819)=k2_relat_1(C_1819) | ~m1_subset_1(C_1819, k1_zfmisc_1(k2_zfmisc_1(A_1817, B_1818))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.70/4.90  tff(c_27334, plain, (![C_1823]: (k2_relset_1('#skF_1', '#skF_2', C_1823)=k2_relat_1(C_1823) | ~m1_subset_1(C_1823, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_25244, c_27281])).
% 12.70/4.90  tff(c_27337, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_25248, c_27334])).
% 12.70/4.90  tff(c_27347, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_27337])).
% 12.70/4.90  tff(c_27404, plain, (![A_1824, B_1825, C_1826]: (k1_relset_1(A_1824, B_1825, C_1826)=k1_relat_1(C_1826) | ~m1_subset_1(C_1826, k1_zfmisc_1(k2_zfmisc_1(A_1824, B_1825))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.70/4.90  tff(c_27429, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14789, c_27404])).
% 12.70/4.90  tff(c_27970, plain, (![B_1877, C_1878, A_1879]: (k1_xboole_0=B_1877 | v1_funct_2(C_1878, A_1879, B_1877) | k1_relset_1(A_1879, B_1877, C_1878)!=A_1879 | ~m1_subset_1(C_1878, k1_zfmisc_1(k2_zfmisc_1(A_1879, B_1877))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_27982, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_14789, c_27970])).
% 12.70/4.90  tff(c_28002, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_27429, c_27982])).
% 12.70/4.90  tff(c_28003, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_14788, c_28002])).
% 12.70/4.90  tff(c_28008, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_28003])).
% 12.70/4.90  tff(c_28011, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_28008])).
% 12.70/4.90  tff(c_28014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_76, c_70, c_27347, c_28011])).
% 12.70/4.90  tff(c_28015, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_28003])).
% 12.70/4.90  tff(c_25256, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_25244, c_10])).
% 12.70/4.90  tff(c_25275, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_25256])).
% 12.70/4.90  tff(c_28049, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28015, c_25275])).
% 12.70/4.90  tff(c_28055, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28015, c_28015, c_14])).
% 12.70/4.90  tff(c_28307, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28055, c_25244])).
% 12.70/4.90  tff(c_28309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28049, c_28307])).
% 12.70/4.90  tff(c_28311, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_25256])).
% 12.70/4.90  tff(c_28317, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28311, c_28311, c_14])).
% 12.70/4.90  tff(c_28573, plain, (![A_1917, A_1918, B_1919]: (v4_relat_1(A_1917, A_1918) | ~r1_tarski(A_1917, k2_zfmisc_1(A_1918, B_1919)))), inference(resolution, [status(thm)], [c_20, c_14833])).
% 12.70/4.90  tff(c_28595, plain, (![A_1918, B_1919]: (v4_relat_1(k2_zfmisc_1(A_1918, B_1919), A_1918))), inference(resolution, [status(thm)], [c_6, c_28573])).
% 12.70/4.90  tff(c_28505, plain, (![B_1898, A_1899]: (r1_tarski(k1_relat_1(B_1898), A_1899) | ~v4_relat_1(B_1898, A_1899) | ~v1_relat_1(B_1898))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.70/4.90  tff(c_28316, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28311, c_28311, c_8])).
% 12.70/4.90  tff(c_28684, plain, (![B_1931]: (k1_relat_1(B_1931)='#skF_3' | ~v4_relat_1(B_1931, '#skF_3') | ~v1_relat_1(B_1931))), inference(resolution, [status(thm)], [c_28505, c_28316])).
% 12.70/4.90  tff(c_28688, plain, (![B_1919]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_1919))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_3', B_1919)))), inference(resolution, [status(thm)], [c_28595, c_28684])).
% 12.70/4.90  tff(c_28699, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28317, c_28688])).
% 12.70/4.90  tff(c_28320, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_28311, c_16])).
% 12.70/4.90  tff(c_28865, plain, (![A_1943, B_1944, C_1945]: (k1_relset_1(A_1943, B_1944, C_1945)=k1_relat_1(C_1945) | ~m1_subset_1(C_1945, k1_zfmisc_1(k2_zfmisc_1(A_1943, B_1944))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.70/4.90  tff(c_28872, plain, (![A_1943, B_1944]: (k1_relset_1(A_1943, B_1944, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_28320, c_28865])).
% 12.70/4.90  tff(c_28885, plain, (![A_1943, B_1944]: (k1_relset_1(A_1943, B_1944, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28699, c_28872])).
% 12.70/4.90  tff(c_54, plain, (![B_31, C_32, A_30]: (k1_xboole_0=B_31 | v1_funct_2(C_32, A_30, B_31) | k1_relset_1(A_30, B_31, C_32)!=A_30 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_29181, plain, (![B_1987, C_1988, A_1989]: (B_1987='#skF_3' | v1_funct_2(C_1988, A_1989, B_1987) | k1_relset_1(A_1989, B_1987, C_1988)!=A_1989 | ~m1_subset_1(C_1988, k1_zfmisc_1(k2_zfmisc_1(A_1989, B_1987))))), inference(demodulation, [status(thm), theory('equality')], [c_28311, c_54])).
% 12.70/4.90  tff(c_29188, plain, (![B_1987, A_1989]: (B_1987='#skF_3' | v1_funct_2('#skF_3', A_1989, B_1987) | k1_relset_1(A_1989, B_1987, '#skF_3')!=A_1989)), inference(resolution, [status(thm)], [c_28320, c_29181])).
% 12.70/4.90  tff(c_29205, plain, (![B_1990, A_1991]: (B_1990='#skF_3' | v1_funct_2('#skF_3', A_1991, B_1990) | A_1991!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28885, c_29188])).
% 12.70/4.90  tff(c_28310, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_25256])).
% 12.70/4.90  tff(c_28337, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28311, c_28311, c_28310])).
% 12.70/4.90  tff(c_28338, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_28337])).
% 12.70/4.90  tff(c_28355, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28338, c_14789])).
% 12.70/4.90  tff(c_28451, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28317, c_28355])).
% 12.70/4.90  tff(c_28461, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_28451, c_18])).
% 12.70/4.90  tff(c_28470, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_28461, c_28316])).
% 12.70/4.90  tff(c_28356, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28338, c_14788])).
% 12.70/4.90  tff(c_28479, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28470, c_28356])).
% 12.70/4.90  tff(c_29220, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_29205, c_28479])).
% 12.70/4.90  tff(c_28358, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28338, c_74])).
% 12.70/4.90  tff(c_29255, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29220, c_29220, c_28358])).
% 12.70/4.90  tff(c_29249, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29220, c_29220, c_28479])).
% 12.70/4.90  tff(c_29448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29255, c_29249])).
% 12.70/4.90  tff(c_29449, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_28337])).
% 12.70/4.90  tff(c_29450, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_28337])).
% 12.70/4.90  tff(c_29471, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29449, c_29450])).
% 12.70/4.90  tff(c_48, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_30, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.70/4.90  tff(c_78, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_48])).
% 12.70/4.90  tff(c_28315, plain, (![A_30]: (v1_funct_2('#skF_3', A_30, '#skF_3') | A_30='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28311, c_28311, c_28311, c_78])).
% 12.70/4.90  tff(c_29613, plain, (![A_30]: (v1_funct_2('#skF_1', A_30, '#skF_1') | A_30='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29449, c_29449, c_29449, c_28315])).
% 12.70/4.90  tff(c_28319, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28311, c_28311, c_12])).
% 12.70/4.90  tff(c_29552, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29449, c_29449, c_28319])).
% 12.70/4.90  tff(c_29459, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_29449, c_14789])).
% 12.70/4.90  tff(c_29615, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_29552, c_29459])).
% 12.70/4.90  tff(c_29625, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_29615, c_18])).
% 12.70/4.90  tff(c_29574, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_29449, c_29449, c_28316])).
% 12.70/4.90  tff(c_29634, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_29625, c_29574])).
% 12.70/4.90  tff(c_29460, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29449, c_14788])).
% 12.70/4.90  tff(c_29643, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29634, c_29460])).
% 12.70/4.90  tff(c_29669, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_29613, c_29643])).
% 12.70/4.90  tff(c_29673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29471, c_29669])).
% 12.70/4.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.70/4.90  
% 12.70/4.90  Inference rules
% 12.70/4.90  ----------------------
% 12.70/4.90  #Ref     : 0
% 12.70/4.90  #Sup     : 6134
% 12.70/4.90  #Fact    : 0
% 12.70/4.90  #Define  : 0
% 12.70/4.90  #Split   : 108
% 12.70/4.90  #Chain   : 0
% 12.70/4.90  #Close   : 0
% 12.70/4.90  
% 12.70/4.90  Ordering : KBO
% 12.70/4.90  
% 12.70/4.90  Simplification rules
% 12.70/4.90  ----------------------
% 12.70/4.90  #Subsume      : 1384
% 12.70/4.90  #Demod        : 8154
% 12.70/4.90  #Tautology    : 2904
% 12.70/4.90  #SimpNegUnit  : 247
% 12.70/4.90  #BackRed      : 1196
% 12.70/4.90  
% 12.70/4.90  #Partial instantiations: 0
% 12.70/4.90  #Strategies tried      : 1
% 12.70/4.90  
% 12.70/4.90  Timing (in seconds)
% 12.70/4.90  ----------------------
% 12.70/4.90  Preprocessing        : 0.37
% 12.70/4.90  Parsing              : 0.20
% 12.70/4.90  CNF conversion       : 0.02
% 12.70/4.90  Main loop            : 3.58
% 12.70/4.90  Inferencing          : 1.09
% 12.70/4.90  Reduction            : 1.35
% 12.70/4.90  Demodulation         : 0.98
% 12.70/4.90  BG Simplification    : 0.11
% 12.70/4.90  Subsumption          : 0.77
% 12.70/4.90  Abstraction          : 0.15
% 12.70/4.90  MUC search           : 0.00
% 12.70/4.90  Cooper               : 0.00
% 12.70/4.90  Total                : 4.13
% 12.70/4.90  Index Insertion      : 0.00
% 12.70/4.90  Index Deletion       : 0.00
% 12.70/4.90  Index Matching       : 0.00
% 12.70/4.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
