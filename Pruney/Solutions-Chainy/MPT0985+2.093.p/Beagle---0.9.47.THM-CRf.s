%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:41 EST 2020

% Result     : Theorem 8.98s
% Output     : CNFRefutation 9.32s
% Verified   : 
% Statistics : Number of formulae       :  327 (3142 expanded)
%              Number of leaves         :   43 ( 985 expanded)
%              Depth                    :   15
%              Number of atoms          :  599 (8364 expanded)
%              Number of equality atoms :  195 (2788 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_124,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_10065,plain,(
    ! [C_714,A_715,B_716] :
      ( v1_relat_1(C_714)
      | ~ m1_subset_1(C_714,k1_zfmisc_1(k2_zfmisc_1(A_715,B_716))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10090,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_10065])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_82,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_80,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_10449,plain,(
    ! [A_758,B_759,C_760] :
      ( k2_relset_1(A_758,B_759,C_760) = k2_relat_1(C_760)
      | ~ m1_subset_1(C_760,k1_zfmisc_1(k2_zfmisc_1(A_758,B_759))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10465,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_10449])).

tff(c_10482,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10465])).

tff(c_40,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_177,plain,(
    ! [A_54] :
      ( v1_funct_1(k2_funct_1(A_54))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_175,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_180,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_177,c_175])).

tff(c_183,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_180])).

tff(c_260,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_270,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_260])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_270])).

tff(c_285,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_301,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_401,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_422,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_401])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_357,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_301])).

tff(c_86,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_651,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_675,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_651])).

tff(c_1404,plain,(
    ! [B_165,A_166,C_167] :
      ( k1_xboole_0 = B_165
      | k1_relset_1(A_166,B_165,C_167) = A_166
      | ~ v1_funct_2(C_167,A_166,B_165)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_166,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1423,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_1404])).

tff(c_1444,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_675,c_1423])).

tff(c_1448,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1444])).

tff(c_38,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_286,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1341,plain,(
    ! [B_162,A_163] :
      ( m1_subset_1(B_162,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_162),A_163)))
      | ~ r1_tarski(k2_relat_1(B_162),A_163)
      | ~ v1_funct_1(B_162)
      | ~ v1_relat_1(B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1915,plain,(
    ! [B_194,A_195] :
      ( r1_tarski(B_194,k2_zfmisc_1(k1_relat_1(B_194),A_195))
      | ~ r1_tarski(k2_relat_1(B_194),A_195)
      | ~ v1_funct_1(B_194)
      | ~ v1_relat_1(B_194) ) ),
    inference(resolution,[status(thm)],[c_1341,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2390,plain,(
    ! [B_238,A_239] :
      ( k2_zfmisc_1(k1_relat_1(B_238),A_239) = B_238
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(B_238),A_239),B_238)
      | ~ r1_tarski(k2_relat_1(B_238),A_239)
      | ~ v1_funct_1(B_238)
      | ~ v1_relat_1(B_238) ) ),
    inference(resolution,[status(thm)],[c_1915,c_2])).

tff(c_2403,plain,(
    ! [B_238] :
      ( k2_zfmisc_1(k1_relat_1(B_238),k1_xboole_0) = B_238
      | ~ r1_tarski(k1_xboole_0,B_238)
      | ~ r1_tarski(k2_relat_1(B_238),k1_xboole_0)
      | ~ v1_funct_1(B_238)
      | ~ v1_relat_1(B_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2390])).

tff(c_2415,plain,(
    ! [B_240] :
      ( k1_xboole_0 = B_240
      | ~ r1_tarski(k2_relat_1(B_240),k1_xboole_0)
      | ~ v1_funct_1(B_240)
      | ~ v1_relat_1(B_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_2403])).

tff(c_2435,plain,(
    ! [A_241] :
      ( k2_funct_1(A_241) = k1_xboole_0
      | ~ r1_tarski(k1_relat_1(A_241),k1_xboole_0)
      | ~ v1_funct_1(k2_funct_1(A_241))
      | ~ v1_relat_1(k2_funct_1(A_241))
      | ~ v2_funct_1(A_241)
      | ~ v1_funct_1(A_241)
      | ~ v1_relat_1(A_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2415])).

tff(c_2438,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1448,c_2435])).

tff(c_2449,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_82,c_286,c_2438])).

tff(c_2454,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2449])).

tff(c_2479,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_2454])).

tff(c_2483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_2479])).

tff(c_2485,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2449])).

tff(c_760,plain,(
    ! [A_113,B_114,C_115] :
      ( k2_relset_1(A_113,B_114,C_115) = k2_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_773,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_760])).

tff(c_789,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_773])).

tff(c_685,plain,(
    ! [A_109] :
      ( m1_subset_1(A_109,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_109),k2_relat_1(A_109))))
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1041,plain,(
    ! [A_144] :
      ( r1_tarski(A_144,k2_zfmisc_1(k1_relat_1(A_144),k2_relat_1(A_144)))
      | ~ v1_funct_1(A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_685,c_20])).

tff(c_2607,plain,(
    ! [A_247] :
      ( r1_tarski(k2_funct_1(A_247),k2_zfmisc_1(k2_relat_1(A_247),k2_relat_1(k2_funct_1(A_247))))
      | ~ v1_funct_1(k2_funct_1(A_247))
      | ~ v1_relat_1(k2_funct_1(A_247))
      | ~ v2_funct_1(A_247)
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1041])).

tff(c_2630,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_2607])).

tff(c_2653,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_82,c_2485,c_286,c_2630])).

tff(c_2680,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2653])).

tff(c_2695,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_82,c_1448,c_2680])).

tff(c_2697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_2695])).

tff(c_2698,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1444])).

tff(c_1384,plain,(
    ! [B_164] :
      ( m1_subset_1(B_164,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_164),k1_xboole_0)
      | ~ v1_funct_1(B_164)
      | ~ v1_relat_1(B_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1341])).

tff(c_1387,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_1384])).

tff(c_1398,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_1387])).

tff(c_1403,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1398])).

tff(c_2701,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2698,c_1403])).

tff(c_2736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2701])).

tff(c_2738,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1398])).

tff(c_2754,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_2738,c_2])).

tff(c_2768,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2754])).

tff(c_2847,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2768,c_8])).

tff(c_2737,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1398])).

tff(c_3042,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2768,c_2737])).

tff(c_3055,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3042,c_20])).

tff(c_3068,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_3055,c_2])).

tff(c_3074,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_3068])).

tff(c_2843,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2768,c_2768,c_14])).

tff(c_3335,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3074,c_3074,c_2843])).

tff(c_287,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_298,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_84,c_287])).

tff(c_374,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_384,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_374])).

tff(c_441,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_3097,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3074,c_441])).

tff(c_3659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3335,c_3097])).

tff(c_3660,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_3663,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3660,c_84])).

tff(c_3981,plain,(
    ! [A_306,B_307,C_308] :
      ( k2_relset_1(A_306,B_307,C_308) = k2_relat_1(C_308)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4041,plain,(
    ! [C_314] :
      ( k2_relset_1('#skF_1','#skF_2',C_314) = k2_relat_1(C_314)
      | ~ m1_subset_1(C_314,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_3981])).

tff(c_4044,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3663,c_4041])).

tff(c_4054,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4044])).

tff(c_3878,plain,(
    ! [A_297] :
      ( k1_relat_1(k2_funct_1(A_297)) = k2_relat_1(A_297)
      | ~ v2_funct_1(A_297)
      | ~ v1_funct_1(A_297)
      | ~ v1_relat_1(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_68,plain,(
    ! [A_35] :
      ( v1_funct_2(A_35,k1_relat_1(A_35),k2_relat_1(A_35))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7119,plain,(
    ! [A_509] :
      ( v1_funct_2(k2_funct_1(A_509),k2_relat_1(A_509),k2_relat_1(k2_funct_1(A_509)))
      | ~ v1_funct_1(k2_funct_1(A_509))
      | ~ v1_relat_1(k2_funct_1(A_509))
      | ~ v2_funct_1(A_509)
      | ~ v1_funct_1(A_509)
      | ~ v1_relat_1(A_509) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3878,c_68])).

tff(c_7122,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4054,c_7119])).

tff(c_7136,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_82,c_286,c_7122])).

tff(c_7141,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7136])).

tff(c_7144,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_7141])).

tff(c_7148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_7144])).

tff(c_7150,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7136])).

tff(c_4113,plain,(
    ! [A_315,B_316,C_317] :
      ( k1_relset_1(A_315,B_316,C_317) = k1_relat_1(C_317)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4171,plain,(
    ! [C_321] :
      ( k1_relset_1('#skF_1','#skF_2',C_321) = k1_relat_1(C_321)
      | ~ m1_subset_1(C_321,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_4113])).

tff(c_4183,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3663,c_4171])).

tff(c_6154,plain,(
    ! [B_449,C_450,A_451] :
      ( k1_xboole_0 = B_449
      | v1_funct_2(C_450,A_451,B_449)
      | k1_relset_1(A_451,B_449,C_450) != A_451
      | ~ m1_subset_1(C_450,k1_zfmisc_1(k2_zfmisc_1(A_451,B_449))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6166,plain,(
    ! [C_450] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_450,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_450) != '#skF_1'
      | ~ m1_subset_1(C_450,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_6154])).

tff(c_6237,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6166])).

tff(c_5881,plain,(
    ! [B_430,A_431] :
      ( m1_subset_1(B_430,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_430),A_431)))
      | ~ r1_tarski(k2_relat_1(B_430),A_431)
      | ~ v1_funct_1(B_430)
      | ~ v1_relat_1(B_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_5929,plain,(
    ! [B_432] :
      ( m1_subset_1(B_432,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_432),k1_xboole_0)
      | ~ v1_funct_1(B_432)
      | ~ v1_relat_1(B_432) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_5881])).

tff(c_5932,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4054,c_5929])).

tff(c_5943,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_5932])).

tff(c_5948,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5943])).

tff(c_6251,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6237,c_5948])).

tff(c_6286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6251])).

tff(c_6288,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6166])).

tff(c_6068,plain,(
    ! [B_438,A_439,C_440] :
      ( k1_xboole_0 = B_438
      | k1_relset_1(A_439,B_438,C_440) = A_439
      | ~ v1_funct_2(C_440,A_439,B_438)
      | ~ m1_subset_1(C_440,k1_zfmisc_1(k2_zfmisc_1(A_439,B_438))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6080,plain,(
    ! [C_440] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_440) = '#skF_1'
      | ~ v1_funct_2(C_440,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_440,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_6068])).

tff(c_6352,plain,(
    ! [C_461] :
      ( k1_relset_1('#skF_1','#skF_2',C_461) = '#skF_1'
      | ~ v1_funct_2(C_461,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_461,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6288,c_6080])).

tff(c_6355,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3663,c_6352])).

tff(c_6366,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4183,c_6355])).

tff(c_3937,plain,(
    ! [A_305] :
      ( m1_subset_1(A_305,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_305),k2_relat_1(A_305))))
      | ~ v1_funct_1(A_305)
      | ~ v1_relat_1(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7328,plain,(
    ! [A_520] :
      ( m1_subset_1(k2_funct_1(A_520),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_520)),k1_relat_1(A_520))))
      | ~ v1_funct_1(k2_funct_1(A_520))
      | ~ v1_relat_1(k2_funct_1(A_520))
      | ~ v2_funct_1(A_520)
      | ~ v1_funct_1(A_520)
      | ~ v1_relat_1(A_520) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3937])).

tff(c_7354,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6366,c_7328])).

tff(c_7378,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_82,c_7150,c_286,c_7354])).

tff(c_7408,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_7378])).

tff(c_7426,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_82,c_4054,c_7408])).

tff(c_7428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_7426])).

tff(c_7430,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5943])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7461,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7430,c_10])).

tff(c_7530,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7461,c_8])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3670,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_12])).

tff(c_3717,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3670])).

tff(c_7516,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7461,c_3717])).

tff(c_7429,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_5943])).

tff(c_7496,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7429,c_20])).

tff(c_7550,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7461,c_7496])).

tff(c_7555,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_7550,c_2])).

tff(c_7561,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_7516,c_7555])).

tff(c_7754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7530,c_7561])).

tff(c_7756,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3670])).

tff(c_18,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7786,plain,(
    ! [A_7] : m1_subset_1('#skF_3',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7756,c_18])).

tff(c_302,plain,(
    ! [A_65] : m1_subset_1(k6_partfun1(A_65),k1_zfmisc_1(k2_zfmisc_1(A_65,A_65))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_309,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_302])).

tff(c_318,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_309,c_20])).

tff(c_322,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_318,c_10])).

tff(c_7780,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7756,c_7756,c_322])).

tff(c_64,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,(
    ! [A_15] : k2_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_7807,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7780,c_89])).

tff(c_7986,plain,(
    ! [A_539] :
      ( k1_relat_1(k2_funct_1(A_539)) = k2_relat_1(A_539)
      | ~ v2_funct_1(A_539)
      | ~ v1_funct_1(A_539)
      | ~ v1_relat_1(A_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_9438,plain,(
    ! [A_679] :
      ( v1_funct_2(k2_funct_1(A_679),k2_relat_1(A_679),k2_relat_1(k2_funct_1(A_679)))
      | ~ v1_funct_1(k2_funct_1(A_679))
      | ~ v1_relat_1(k2_funct_1(A_679))
      | ~ v2_funct_1(A_679)
      | ~ v1_funct_1(A_679)
      | ~ v1_relat_1(A_679) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7986,c_68])).

tff(c_9447,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7807,c_9438])).

tff(c_9452,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_82,c_286,c_9447])).

tff(c_9455,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9452])).

tff(c_9458,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_9455])).

tff(c_9462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_9458])).

tff(c_9464,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9452])).

tff(c_7787,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7756,c_8])).

tff(c_28,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_90,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_28])).

tff(c_7804,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7780,c_90])).

tff(c_7783,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7756,c_7756,c_14])).

tff(c_8542,plain,(
    ! [B_608,A_609] :
      ( m1_subset_1(B_608,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_608),A_609)))
      | ~ r1_tarski(k2_relat_1(B_608),A_609)
      | ~ v1_funct_1(B_608)
      | ~ v1_relat_1(B_608) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_9086,plain,(
    ! [B_649,A_650] :
      ( r1_tarski(B_649,k2_zfmisc_1(k1_relat_1(B_649),A_650))
      | ~ r1_tarski(k2_relat_1(B_649),A_650)
      | ~ v1_funct_1(B_649)
      | ~ v1_relat_1(B_649) ) ),
    inference(resolution,[status(thm)],[c_8542,c_20])).

tff(c_9535,plain,(
    ! [B_685,A_686] :
      ( k2_zfmisc_1(k1_relat_1(B_685),A_686) = B_685
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(B_685),A_686),B_685)
      | ~ r1_tarski(k2_relat_1(B_685),A_686)
      | ~ v1_funct_1(B_685)
      | ~ v1_relat_1(B_685) ) ),
    inference(resolution,[status(thm)],[c_9086,c_2])).

tff(c_9542,plain,(
    ! [B_685] :
      ( k2_zfmisc_1(k1_relat_1(B_685),'#skF_3') = B_685
      | ~ r1_tarski('#skF_3',B_685)
      | ~ r1_tarski(k2_relat_1(B_685),'#skF_3')
      | ~ v1_funct_1(B_685)
      | ~ v1_relat_1(B_685) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7783,c_9535])).

tff(c_9580,plain,(
    ! [B_688] :
      ( B_688 = '#skF_3'
      | ~ r1_tarski(k2_relat_1(B_688),'#skF_3')
      | ~ v1_funct_1(B_688)
      | ~ v1_relat_1(B_688) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7787,c_7783,c_9542])).

tff(c_9595,plain,(
    ! [A_689] :
      ( k2_funct_1(A_689) = '#skF_3'
      | ~ r1_tarski(k1_relat_1(A_689),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(A_689))
      | ~ v1_relat_1(k2_funct_1(A_689))
      | ~ v2_funct_1(A_689)
      | ~ v1_funct_1(A_689)
      | ~ v1_relat_1(A_689) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_9580])).

tff(c_9601,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7804,c_9595])).

tff(c_9606,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_88,c_82,c_9464,c_286,c_7787,c_9601])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7785,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7756,c_7756,c_16])).

tff(c_7755,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3670])).

tff(c_7856,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7756,c_7756,c_7755])).

tff(c_7857,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7856])).

tff(c_7860,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7857,c_301])).

tff(c_8001,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7785,c_7860])).

tff(c_9613,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9606,c_8001])).

tff(c_9622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7786,c_9613])).

tff(c_9623,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7856])).

tff(c_9624,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7856])).

tff(c_9646,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9623,c_9624])).

tff(c_9626,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9623,c_9623,c_7807])).

tff(c_9747,plain,(
    ! [A_7] : m1_subset_1('#skF_1',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9623,c_7786])).

tff(c_9935,plain,(
    ! [A_705,B_706,C_707] :
      ( k2_relset_1(A_705,B_706,C_707) = k2_relat_1(C_707)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(k2_zfmisc_1(A_705,B_706))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_9948,plain,(
    ! [A_705,B_706] : k2_relset_1(A_705,B_706,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_9747,c_9935])).

tff(c_9958,plain,(
    ! [A_705,B_706] : k2_relset_1(A_705,B_706,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9626,c_9948])).

tff(c_9638,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9623,c_80])).

tff(c_9962,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9958,c_9638])).

tff(c_9964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9646,c_9962])).

tff(c_9965,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_9966,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_10732,plain,(
    ! [A_781,B_782,C_783] :
      ( k1_relset_1(A_781,B_782,C_783) = k1_relat_1(C_783)
      | ~ m1_subset_1(C_783,k1_zfmisc_1(k2_zfmisc_1(A_781,B_782))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10766,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9966,c_10732])).

tff(c_11276,plain,(
    ! [B_820,C_821,A_822] :
      ( k1_xboole_0 = B_820
      | v1_funct_2(C_821,A_822,B_820)
      | k1_relset_1(A_822,B_820,C_821) != A_822
      | ~ m1_subset_1(C_821,k1_zfmisc_1(k2_zfmisc_1(A_822,B_820))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_11288,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_9966,c_11276])).

tff(c_11312,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10766,c_11288])).

tff(c_11313,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_9965,c_11312])).

tff(c_11321,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_11313])).

tff(c_11324,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_11321])).

tff(c_11327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10090,c_88,c_82,c_10482,c_11324])).

tff(c_11328,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11313])).

tff(c_11362,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11328,c_8])).

tff(c_11360,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11328,c_11328,c_16])).

tff(c_9994,plain,(
    ! [B_711,A_712] :
      ( B_711 = A_712
      | ~ r1_tarski(B_711,A_712)
      | ~ r1_tarski(A_712,B_711) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10009,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_9994])).

tff(c_10041,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_10009])).

tff(c_11493,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11360,c_10041])).

tff(c_11498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11362,c_11493])).

tff(c_11499,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10009])).

tff(c_26,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11510,plain,(
    v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11499,c_26])).

tff(c_11506,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11499,c_84])).

tff(c_12223,plain,(
    ! [A_895,B_896,C_897] :
      ( k2_relset_1(A_895,B_896,C_897) = k2_relat_1(C_897)
      | ~ m1_subset_1(C_897,k1_zfmisc_1(k2_zfmisc_1(A_895,B_896))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12308,plain,(
    ! [C_904] :
      ( k2_relset_1('#skF_1','#skF_2',C_904) = k2_relat_1(C_904)
      | ~ m1_subset_1(C_904,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11499,c_12223])).

tff(c_12311,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11506,c_12308])).

tff(c_12321,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12311])).

tff(c_11930,plain,(
    ! [A_870,B_871,C_872] :
      ( k1_relset_1(A_870,B_871,C_872) = k1_relat_1(C_872)
      | ~ m1_subset_1(C_872,k1_zfmisc_1(k2_zfmisc_1(A_870,B_871))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_11956,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9966,c_11930])).

tff(c_12908,plain,(
    ! [B_941,C_942,A_943] :
      ( k1_xboole_0 = B_941
      | v1_funct_2(C_942,A_943,B_941)
      | k1_relset_1(A_943,B_941,C_942) != A_943
      | ~ m1_subset_1(C_942,k1_zfmisc_1(k2_zfmisc_1(A_943,B_941))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12926,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_9966,c_12908])).

tff(c_12950,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11956,c_12926])).

tff(c_12951,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_9965,c_12950])).

tff(c_12956,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12951])).

tff(c_12959,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_12956])).

tff(c_12962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11510,c_88,c_82,c_12321,c_12959])).

tff(c_12963,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12951])).

tff(c_11565,plain,(
    ! [B_828,A_829] :
      ( k1_xboole_0 = B_828
      | k1_xboole_0 = A_829
      | k2_zfmisc_1(A_829,B_828) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11568,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_11499,c_11565])).

tff(c_11638,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_11568])).

tff(c_12990,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12963,c_11638])).

tff(c_13002,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12963,c_12963,c_16])).

tff(c_13145,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13002,c_11499])).

tff(c_13147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12990,c_13145])).

tff(c_13149,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11568])).

tff(c_13163,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13149,c_8])).

tff(c_9973,plain,(
    ! [A_710] : m1_subset_1(k6_partfun1(A_710),k1_zfmisc_1(k2_zfmisc_1(A_710,A_710))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_9980,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_9973])).

tff(c_9989,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9980,c_20])).

tff(c_9993,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9989,c_10])).

tff(c_13156,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13149,c_13149,c_9993])).

tff(c_13183,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_13156,c_89])).

tff(c_13180,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_13156,c_90])).

tff(c_14224,plain,(
    ! [B_1022,A_1023] :
      ( v1_funct_2(B_1022,k1_relat_1(B_1022),A_1023)
      | ~ r1_tarski(k2_relat_1(B_1022),A_1023)
      | ~ v1_funct_1(B_1022)
      | ~ v1_relat_1(B_1022) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_14233,plain,(
    ! [A_1023] :
      ( v1_funct_2('#skF_3','#skF_3',A_1023)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_1023)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13180,c_14224])).

tff(c_14239,plain,(
    ! [A_1023] : v1_funct_2('#skF_3','#skF_3',A_1023) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11510,c_88,c_13163,c_13183,c_14233])).

tff(c_13161,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13149,c_13149,c_16])).

tff(c_13148,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_11568])).

tff(c_13736,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13149,c_13149,c_13148])).

tff(c_13737,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_13736])).

tff(c_13275,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13149,c_13149,c_13148])).

tff(c_13276,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_13275])).

tff(c_9970,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_9966,c_20])).

tff(c_10008,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9970,c_9994])).

tff(c_13201,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10008])).

tff(c_13398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13163,c_13161,c_13276,c_13201])).

tff(c_13399,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13275])).

tff(c_13406,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13399,c_13163])).

tff(c_13159,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13149,c_13149,c_14])).

tff(c_13496,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13399,c_13399,c_13159])).

tff(c_13701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13406,c_13496,c_13399,c_13201])).

tff(c_13702,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_10008])).

tff(c_13841,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13161,c_13737,c_13702])).

tff(c_13741,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13737,c_9965])).

tff(c_13873,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13841,c_13741])).

tff(c_14245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14239,c_13873])).

tff(c_14246,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13736])).

tff(c_14247,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13736])).

tff(c_14272,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14246,c_14247])).

tff(c_48,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_30,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_92,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_48])).

tff(c_13157,plain,(
    ! [A_30] :
      ( v1_funct_2('#skF_3',A_30,'#skF_3')
      | A_30 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13149,c_13149,c_13149,c_92])).

tff(c_14527,plain,(
    ! [A_1038] :
      ( v1_funct_2('#skF_1',A_1038,'#skF_1')
      | A_1038 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14246,c_14246,c_14246,c_13157])).

tff(c_14392,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14246,c_14246,c_13159])).

tff(c_14438,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14392,c_14246,c_13702])).

tff(c_14262,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14246,c_9965])).

tff(c_14462,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14438,c_14262])).

tff(c_14530,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14527,c_14462])).

tff(c_14534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14272,c_14530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:21:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.98/3.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.25/3.24  
% 9.25/3.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.25/3.24  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.25/3.24  
% 9.25/3.24  %Foreground sorts:
% 9.25/3.24  
% 9.25/3.24  
% 9.25/3.24  %Background operators:
% 9.25/3.24  
% 9.25/3.24  
% 9.25/3.24  %Foreground operators:
% 9.25/3.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.25/3.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.25/3.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.25/3.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.25/3.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.25/3.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.25/3.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.25/3.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.25/3.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.25/3.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.25/3.24  tff('#skF_2', type, '#skF_2': $i).
% 9.25/3.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.25/3.24  tff('#skF_3', type, '#skF_3': $i).
% 9.25/3.24  tff('#skF_1', type, '#skF_1': $i).
% 9.25/3.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.25/3.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.25/3.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.25/3.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.25/3.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.25/3.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.25/3.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.25/3.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.25/3.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.25/3.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.25/3.24  
% 9.32/3.27  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.32/3.27  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.32/3.27  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.32/3.27  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.32/3.27  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.32/3.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.32/3.27  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.32/3.27  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.32/3.27  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.32/3.27  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.32/3.27  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.32/3.27  tff(f_146, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 9.32/3.27  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 9.32/3.27  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.32/3.27  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.32/3.27  tff(f_122, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.32/3.27  tff(f_124, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.32/3.27  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.32/3.27  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.32/3.27  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.32/3.27  tff(c_10065, plain, (![C_714, A_715, B_716]: (v1_relat_1(C_714) | ~m1_subset_1(C_714, k1_zfmisc_1(k2_zfmisc_1(A_715, B_716))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.32/3.27  tff(c_10090, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_10065])).
% 9.32/3.27  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.32/3.27  tff(c_82, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.32/3.27  tff(c_80, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.32/3.27  tff(c_10449, plain, (![A_758, B_759, C_760]: (k2_relset_1(A_758, B_759, C_760)=k2_relat_1(C_760) | ~m1_subset_1(C_760, k1_zfmisc_1(k2_zfmisc_1(A_758, B_759))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.32/3.27  tff(c_10465, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_10449])).
% 9.32/3.27  tff(c_10482, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_10465])).
% 9.32/3.27  tff(c_40, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.32/3.27  tff(c_177, plain, (![A_54]: (v1_funct_1(k2_funct_1(A_54)) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.32/3.27  tff(c_78, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.32/3.27  tff(c_175, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_78])).
% 9.32/3.27  tff(c_180, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_177, c_175])).
% 9.32/3.27  tff(c_183, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_180])).
% 9.32/3.27  tff(c_260, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.32/3.27  tff(c_270, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_260])).
% 9.32/3.27  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_270])).
% 9.32/3.27  tff(c_285, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_78])).
% 9.32/3.27  tff(c_301, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_285])).
% 9.32/3.27  tff(c_401, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.32/3.27  tff(c_422, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_401])).
% 9.32/3.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.32/3.27  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.32/3.27  tff(c_22, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.32/3.27  tff(c_357, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_301])).
% 9.32/3.27  tff(c_86, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.32/3.27  tff(c_651, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.32/3.27  tff(c_675, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_651])).
% 9.32/3.27  tff(c_1404, plain, (![B_165, A_166, C_167]: (k1_xboole_0=B_165 | k1_relset_1(A_166, B_165, C_167)=A_166 | ~v1_funct_2(C_167, A_166, B_165) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_166, B_165))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.32/3.27  tff(c_1423, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_84, c_1404])).
% 9.32/3.27  tff(c_1444, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_675, c_1423])).
% 9.32/3.27  tff(c_1448, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1444])).
% 9.32/3.27  tff(c_38, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.32/3.27  tff(c_36, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.32/3.27  tff(c_286, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_78])).
% 9.32/3.27  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.32/3.27  tff(c_1341, plain, (![B_162, A_163]: (m1_subset_1(B_162, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_162), A_163))) | ~r1_tarski(k2_relat_1(B_162), A_163) | ~v1_funct_1(B_162) | ~v1_relat_1(B_162))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.32/3.27  tff(c_20, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.32/3.27  tff(c_1915, plain, (![B_194, A_195]: (r1_tarski(B_194, k2_zfmisc_1(k1_relat_1(B_194), A_195)) | ~r1_tarski(k2_relat_1(B_194), A_195) | ~v1_funct_1(B_194) | ~v1_relat_1(B_194))), inference(resolution, [status(thm)], [c_1341, c_20])).
% 9.32/3.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.32/3.27  tff(c_2390, plain, (![B_238, A_239]: (k2_zfmisc_1(k1_relat_1(B_238), A_239)=B_238 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(B_238), A_239), B_238) | ~r1_tarski(k2_relat_1(B_238), A_239) | ~v1_funct_1(B_238) | ~v1_relat_1(B_238))), inference(resolution, [status(thm)], [c_1915, c_2])).
% 9.32/3.27  tff(c_2403, plain, (![B_238]: (k2_zfmisc_1(k1_relat_1(B_238), k1_xboole_0)=B_238 | ~r1_tarski(k1_xboole_0, B_238) | ~r1_tarski(k2_relat_1(B_238), k1_xboole_0) | ~v1_funct_1(B_238) | ~v1_relat_1(B_238))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2390])).
% 9.32/3.27  tff(c_2415, plain, (![B_240]: (k1_xboole_0=B_240 | ~r1_tarski(k2_relat_1(B_240), k1_xboole_0) | ~v1_funct_1(B_240) | ~v1_relat_1(B_240))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14, c_2403])).
% 9.32/3.27  tff(c_2435, plain, (![A_241]: (k2_funct_1(A_241)=k1_xboole_0 | ~r1_tarski(k1_relat_1(A_241), k1_xboole_0) | ~v1_funct_1(k2_funct_1(A_241)) | ~v1_relat_1(k2_funct_1(A_241)) | ~v2_funct_1(A_241) | ~v1_funct_1(A_241) | ~v1_relat_1(A_241))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2415])).
% 9.32/3.27  tff(c_2438, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1448, c_2435])).
% 9.32/3.27  tff(c_2449, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_82, c_286, c_2438])).
% 9.32/3.27  tff(c_2454, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2449])).
% 9.32/3.27  tff(c_2479, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_2454])).
% 9.32/3.27  tff(c_2483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_2479])).
% 9.32/3.27  tff(c_2485, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2449])).
% 9.32/3.27  tff(c_760, plain, (![A_113, B_114, C_115]: (k2_relset_1(A_113, B_114, C_115)=k2_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.32/3.27  tff(c_773, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_760])).
% 9.32/3.27  tff(c_789, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_773])).
% 9.32/3.27  tff(c_685, plain, (![A_109]: (m1_subset_1(A_109, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_109), k2_relat_1(A_109)))) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.32/3.27  tff(c_1041, plain, (![A_144]: (r1_tarski(A_144, k2_zfmisc_1(k1_relat_1(A_144), k2_relat_1(A_144))) | ~v1_funct_1(A_144) | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_685, c_20])).
% 9.32/3.27  tff(c_2607, plain, (![A_247]: (r1_tarski(k2_funct_1(A_247), k2_zfmisc_1(k2_relat_1(A_247), k2_relat_1(k2_funct_1(A_247)))) | ~v1_funct_1(k2_funct_1(A_247)) | ~v1_relat_1(k2_funct_1(A_247)) | ~v2_funct_1(A_247) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1041])).
% 9.32/3.27  tff(c_2630, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_789, c_2607])).
% 9.32/3.27  tff(c_2653, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_82, c_2485, c_286, c_2630])).
% 9.32/3.27  tff(c_2680, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2653])).
% 9.32/3.27  tff(c_2695, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_82, c_1448, c_2680])).
% 9.32/3.27  tff(c_2697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_357, c_2695])).
% 9.32/3.27  tff(c_2698, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1444])).
% 9.32/3.27  tff(c_1384, plain, (![B_164]: (m1_subset_1(B_164, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_164), k1_xboole_0) | ~v1_funct_1(B_164) | ~v1_relat_1(B_164))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1341])).
% 9.32/3.27  tff(c_1387, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_789, c_1384])).
% 9.32/3.27  tff(c_1398, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_1387])).
% 9.32/3.27  tff(c_1403, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1398])).
% 9.32/3.27  tff(c_2701, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2698, c_1403])).
% 9.32/3.27  tff(c_2736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2701])).
% 9.32/3.27  tff(c_2738, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1398])).
% 9.32/3.27  tff(c_2754, plain, (k1_xboole_0='#skF_2' | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_2738, c_2])).
% 9.32/3.27  tff(c_2768, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2754])).
% 9.32/3.27  tff(c_2847, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2768, c_8])).
% 9.32/3.27  tff(c_2737, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1398])).
% 9.32/3.27  tff(c_3042, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2768, c_2737])).
% 9.32/3.27  tff(c_3055, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3042, c_20])).
% 9.32/3.27  tff(c_3068, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_3055, c_2])).
% 9.32/3.27  tff(c_3074, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_3068])).
% 9.32/3.27  tff(c_2843, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2768, c_2768, c_14])).
% 9.32/3.27  tff(c_3335, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3074, c_3074, c_2843])).
% 9.32/3.27  tff(c_287, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.32/3.27  tff(c_298, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_84, c_287])).
% 9.32/3.27  tff(c_374, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.32/3.27  tff(c_384, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_298, c_374])).
% 9.32/3.27  tff(c_441, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_384])).
% 9.32/3.27  tff(c_3097, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3074, c_441])).
% 9.32/3.27  tff(c_3659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3335, c_3097])).
% 9.32/3.27  tff(c_3660, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_384])).
% 9.32/3.27  tff(c_3663, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3660, c_84])).
% 9.32/3.27  tff(c_3981, plain, (![A_306, B_307, C_308]: (k2_relset_1(A_306, B_307, C_308)=k2_relat_1(C_308) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.32/3.27  tff(c_4041, plain, (![C_314]: (k2_relset_1('#skF_1', '#skF_2', C_314)=k2_relat_1(C_314) | ~m1_subset_1(C_314, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3660, c_3981])).
% 9.32/3.27  tff(c_4044, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3663, c_4041])).
% 9.32/3.27  tff(c_4054, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4044])).
% 9.32/3.27  tff(c_3878, plain, (![A_297]: (k1_relat_1(k2_funct_1(A_297))=k2_relat_1(A_297) | ~v2_funct_1(A_297) | ~v1_funct_1(A_297) | ~v1_relat_1(A_297))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.32/3.27  tff(c_68, plain, (![A_35]: (v1_funct_2(A_35, k1_relat_1(A_35), k2_relat_1(A_35)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.32/3.27  tff(c_7119, plain, (![A_509]: (v1_funct_2(k2_funct_1(A_509), k2_relat_1(A_509), k2_relat_1(k2_funct_1(A_509))) | ~v1_funct_1(k2_funct_1(A_509)) | ~v1_relat_1(k2_funct_1(A_509)) | ~v2_funct_1(A_509) | ~v1_funct_1(A_509) | ~v1_relat_1(A_509))), inference(superposition, [status(thm), theory('equality')], [c_3878, c_68])).
% 9.32/3.27  tff(c_7122, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4054, c_7119])).
% 9.32/3.27  tff(c_7136, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_82, c_286, c_7122])).
% 9.32/3.27  tff(c_7141, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_7136])).
% 9.32/3.27  tff(c_7144, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_7141])).
% 9.32/3.27  tff(c_7148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_7144])).
% 9.32/3.27  tff(c_7150, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7136])).
% 9.32/3.27  tff(c_4113, plain, (![A_315, B_316, C_317]: (k1_relset_1(A_315, B_316, C_317)=k1_relat_1(C_317) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.32/3.27  tff(c_4171, plain, (![C_321]: (k1_relset_1('#skF_1', '#skF_2', C_321)=k1_relat_1(C_321) | ~m1_subset_1(C_321, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3660, c_4113])).
% 9.32/3.27  tff(c_4183, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3663, c_4171])).
% 9.32/3.27  tff(c_6154, plain, (![B_449, C_450, A_451]: (k1_xboole_0=B_449 | v1_funct_2(C_450, A_451, B_449) | k1_relset_1(A_451, B_449, C_450)!=A_451 | ~m1_subset_1(C_450, k1_zfmisc_1(k2_zfmisc_1(A_451, B_449))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.32/3.27  tff(c_6166, plain, (![C_450]: (k1_xboole_0='#skF_2' | v1_funct_2(C_450, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_450)!='#skF_1' | ~m1_subset_1(C_450, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3660, c_6154])).
% 9.32/3.27  tff(c_6237, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6166])).
% 9.32/3.27  tff(c_5881, plain, (![B_430, A_431]: (m1_subset_1(B_430, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_430), A_431))) | ~r1_tarski(k2_relat_1(B_430), A_431) | ~v1_funct_1(B_430) | ~v1_relat_1(B_430))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.32/3.27  tff(c_5929, plain, (![B_432]: (m1_subset_1(B_432, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_432), k1_xboole_0) | ~v1_funct_1(B_432) | ~v1_relat_1(B_432))), inference(superposition, [status(thm), theory('equality')], [c_14, c_5881])).
% 9.32/3.27  tff(c_5932, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4054, c_5929])).
% 9.32/3.27  tff(c_5943, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_5932])).
% 9.32/3.27  tff(c_5948, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5943])).
% 9.32/3.27  tff(c_6251, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6237, c_5948])).
% 9.32/3.27  tff(c_6286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6251])).
% 9.32/3.27  tff(c_6288, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_6166])).
% 9.32/3.27  tff(c_6068, plain, (![B_438, A_439, C_440]: (k1_xboole_0=B_438 | k1_relset_1(A_439, B_438, C_440)=A_439 | ~v1_funct_2(C_440, A_439, B_438) | ~m1_subset_1(C_440, k1_zfmisc_1(k2_zfmisc_1(A_439, B_438))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.32/3.27  tff(c_6080, plain, (![C_440]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_440)='#skF_1' | ~v1_funct_2(C_440, '#skF_1', '#skF_2') | ~m1_subset_1(C_440, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3660, c_6068])).
% 9.32/3.27  tff(c_6352, plain, (![C_461]: (k1_relset_1('#skF_1', '#skF_2', C_461)='#skF_1' | ~v1_funct_2(C_461, '#skF_1', '#skF_2') | ~m1_subset_1(C_461, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_6288, c_6080])).
% 9.32/3.27  tff(c_6355, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3663, c_6352])).
% 9.32/3.27  tff(c_6366, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4183, c_6355])).
% 9.32/3.27  tff(c_3937, plain, (![A_305]: (m1_subset_1(A_305, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_305), k2_relat_1(A_305)))) | ~v1_funct_1(A_305) | ~v1_relat_1(A_305))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.32/3.27  tff(c_7328, plain, (![A_520]: (m1_subset_1(k2_funct_1(A_520), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_520)), k1_relat_1(A_520)))) | ~v1_funct_1(k2_funct_1(A_520)) | ~v1_relat_1(k2_funct_1(A_520)) | ~v2_funct_1(A_520) | ~v1_funct_1(A_520) | ~v1_relat_1(A_520))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3937])).
% 9.32/3.27  tff(c_7354, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6366, c_7328])).
% 9.32/3.27  tff(c_7378, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_82, c_7150, c_286, c_7354])).
% 9.32/3.27  tff(c_7408, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_7378])).
% 9.32/3.27  tff(c_7426, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_82, c_4054, c_7408])).
% 9.32/3.27  tff(c_7428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_301, c_7426])).
% 9.32/3.27  tff(c_7430, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5943])).
% 9.32/3.27  tff(c_10, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.32/3.27  tff(c_7461, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_7430, c_10])).
% 9.32/3.27  tff(c_7530, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7461, c_8])).
% 9.32/3.27  tff(c_12, plain, (![B_6, A_5]: (k1_xboole_0=B_6 | k1_xboole_0=A_5 | k2_zfmisc_1(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.32/3.27  tff(c_3670, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3660, c_12])).
% 9.32/3.27  tff(c_3717, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_3670])).
% 9.32/3.27  tff(c_7516, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7461, c_3717])).
% 9.32/3.27  tff(c_7429, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_5943])).
% 9.32/3.27  tff(c_7496, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_7429, c_20])).
% 9.32/3.27  tff(c_7550, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7461, c_7496])).
% 9.32/3.27  tff(c_7555, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_7550, c_2])).
% 9.32/3.27  tff(c_7561, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_7516, c_7555])).
% 9.32/3.27  tff(c_7754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7530, c_7561])).
% 9.32/3.27  tff(c_7756, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3670])).
% 9.32/3.27  tff(c_18, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.32/3.27  tff(c_7786, plain, (![A_7]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_7756, c_18])).
% 9.32/3.27  tff(c_302, plain, (![A_65]: (m1_subset_1(k6_partfun1(A_65), k1_zfmisc_1(k2_zfmisc_1(A_65, A_65))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.32/3.27  tff(c_309, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_302])).
% 9.32/3.27  tff(c_318, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_309, c_20])).
% 9.32/3.27  tff(c_322, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_318, c_10])).
% 9.32/3.27  tff(c_7780, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7756, c_7756, c_322])).
% 9.32/3.27  tff(c_64, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.32/3.27  tff(c_30, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.32/3.27  tff(c_89, plain, (![A_15]: (k2_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_30])).
% 9.32/3.27  tff(c_7807, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7780, c_89])).
% 9.32/3.27  tff(c_7986, plain, (![A_539]: (k1_relat_1(k2_funct_1(A_539))=k2_relat_1(A_539) | ~v2_funct_1(A_539) | ~v1_funct_1(A_539) | ~v1_relat_1(A_539))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.32/3.27  tff(c_9438, plain, (![A_679]: (v1_funct_2(k2_funct_1(A_679), k2_relat_1(A_679), k2_relat_1(k2_funct_1(A_679))) | ~v1_funct_1(k2_funct_1(A_679)) | ~v1_relat_1(k2_funct_1(A_679)) | ~v2_funct_1(A_679) | ~v1_funct_1(A_679) | ~v1_relat_1(A_679))), inference(superposition, [status(thm), theory('equality')], [c_7986, c_68])).
% 9.32/3.27  tff(c_9447, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7807, c_9438])).
% 9.32/3.27  tff(c_9452, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_82, c_286, c_9447])).
% 9.32/3.27  tff(c_9455, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_9452])).
% 9.32/3.27  tff(c_9458, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_9455])).
% 9.32/3.27  tff(c_9462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_9458])).
% 9.32/3.27  tff(c_9464, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_9452])).
% 9.32/3.27  tff(c_7787, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7756, c_8])).
% 9.32/3.27  tff(c_28, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.32/3.27  tff(c_90, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_28])).
% 9.32/3.27  tff(c_7804, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7780, c_90])).
% 9.32/3.27  tff(c_7783, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7756, c_7756, c_14])).
% 9.32/3.27  tff(c_8542, plain, (![B_608, A_609]: (m1_subset_1(B_608, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_608), A_609))) | ~r1_tarski(k2_relat_1(B_608), A_609) | ~v1_funct_1(B_608) | ~v1_relat_1(B_608))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.32/3.27  tff(c_9086, plain, (![B_649, A_650]: (r1_tarski(B_649, k2_zfmisc_1(k1_relat_1(B_649), A_650)) | ~r1_tarski(k2_relat_1(B_649), A_650) | ~v1_funct_1(B_649) | ~v1_relat_1(B_649))), inference(resolution, [status(thm)], [c_8542, c_20])).
% 9.32/3.27  tff(c_9535, plain, (![B_685, A_686]: (k2_zfmisc_1(k1_relat_1(B_685), A_686)=B_685 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(B_685), A_686), B_685) | ~r1_tarski(k2_relat_1(B_685), A_686) | ~v1_funct_1(B_685) | ~v1_relat_1(B_685))), inference(resolution, [status(thm)], [c_9086, c_2])).
% 9.32/3.27  tff(c_9542, plain, (![B_685]: (k2_zfmisc_1(k1_relat_1(B_685), '#skF_3')=B_685 | ~r1_tarski('#skF_3', B_685) | ~r1_tarski(k2_relat_1(B_685), '#skF_3') | ~v1_funct_1(B_685) | ~v1_relat_1(B_685))), inference(superposition, [status(thm), theory('equality')], [c_7783, c_9535])).
% 9.32/3.27  tff(c_9580, plain, (![B_688]: (B_688='#skF_3' | ~r1_tarski(k2_relat_1(B_688), '#skF_3') | ~v1_funct_1(B_688) | ~v1_relat_1(B_688))), inference(demodulation, [status(thm), theory('equality')], [c_7787, c_7783, c_9542])).
% 9.32/3.27  tff(c_9595, plain, (![A_689]: (k2_funct_1(A_689)='#skF_3' | ~r1_tarski(k1_relat_1(A_689), '#skF_3') | ~v1_funct_1(k2_funct_1(A_689)) | ~v1_relat_1(k2_funct_1(A_689)) | ~v2_funct_1(A_689) | ~v1_funct_1(A_689) | ~v1_relat_1(A_689))), inference(superposition, [status(thm), theory('equality')], [c_38, c_9580])).
% 9.32/3.28  tff(c_9601, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7804, c_9595])).
% 9.32/3.28  tff(c_9606, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_422, c_88, c_82, c_9464, c_286, c_7787, c_9601])).
% 9.32/3.28  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.32/3.28  tff(c_7785, plain, (![B_6]: (k2_zfmisc_1('#skF_3', B_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7756, c_7756, c_16])).
% 9.32/3.28  tff(c_7755, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_3670])).
% 9.32/3.28  tff(c_7856, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7756, c_7756, c_7755])).
% 9.32/3.28  tff(c_7857, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_7856])).
% 9.32/3.28  tff(c_7860, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_7857, c_301])).
% 9.32/3.28  tff(c_8001, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7785, c_7860])).
% 9.32/3.28  tff(c_9613, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9606, c_8001])).
% 9.32/3.28  tff(c_9622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7786, c_9613])).
% 9.32/3.28  tff(c_9623, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_7856])).
% 9.32/3.28  tff(c_9624, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_7856])).
% 9.32/3.28  tff(c_9646, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9623, c_9624])).
% 9.32/3.28  tff(c_9626, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9623, c_9623, c_7807])).
% 9.32/3.28  tff(c_9747, plain, (![A_7]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_9623, c_7786])).
% 9.32/3.28  tff(c_9935, plain, (![A_705, B_706, C_707]: (k2_relset_1(A_705, B_706, C_707)=k2_relat_1(C_707) | ~m1_subset_1(C_707, k1_zfmisc_1(k2_zfmisc_1(A_705, B_706))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.32/3.28  tff(c_9948, plain, (![A_705, B_706]: (k2_relset_1(A_705, B_706, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_9747, c_9935])).
% 9.32/3.28  tff(c_9958, plain, (![A_705, B_706]: (k2_relset_1(A_705, B_706, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9626, c_9948])).
% 9.32/3.28  tff(c_9638, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9623, c_80])).
% 9.32/3.28  tff(c_9962, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9958, c_9638])).
% 9.32/3.28  tff(c_9964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9646, c_9962])).
% 9.32/3.28  tff(c_9965, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_285])).
% 9.32/3.28  tff(c_9966, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_285])).
% 9.32/3.28  tff(c_10732, plain, (![A_781, B_782, C_783]: (k1_relset_1(A_781, B_782, C_783)=k1_relat_1(C_783) | ~m1_subset_1(C_783, k1_zfmisc_1(k2_zfmisc_1(A_781, B_782))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.32/3.28  tff(c_10766, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_9966, c_10732])).
% 9.32/3.28  tff(c_11276, plain, (![B_820, C_821, A_822]: (k1_xboole_0=B_820 | v1_funct_2(C_821, A_822, B_820) | k1_relset_1(A_822, B_820, C_821)!=A_822 | ~m1_subset_1(C_821, k1_zfmisc_1(k2_zfmisc_1(A_822, B_820))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.32/3.28  tff(c_11288, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_9966, c_11276])).
% 9.32/3.28  tff(c_11312, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10766, c_11288])).
% 9.32/3.28  tff(c_11313, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_9965, c_11312])).
% 9.32/3.28  tff(c_11321, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_11313])).
% 9.32/3.28  tff(c_11324, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_11321])).
% 9.32/3.28  tff(c_11327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10090, c_88, c_82, c_10482, c_11324])).
% 9.32/3.28  tff(c_11328, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_11313])).
% 9.32/3.28  tff(c_11362, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11328, c_8])).
% 9.32/3.28  tff(c_11360, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11328, c_11328, c_16])).
% 9.32/3.28  tff(c_9994, plain, (![B_711, A_712]: (B_711=A_712 | ~r1_tarski(B_711, A_712) | ~r1_tarski(A_712, B_711))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.32/3.28  tff(c_10009, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_298, c_9994])).
% 9.32/3.28  tff(c_10041, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_10009])).
% 9.32/3.28  tff(c_11493, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11360, c_10041])).
% 9.32/3.28  tff(c_11498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11362, c_11493])).
% 9.32/3.28  tff(c_11499, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_10009])).
% 9.32/3.28  tff(c_26, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.32/3.28  tff(c_11510, plain, (v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11499, c_26])).
% 9.32/3.28  tff(c_11506, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11499, c_84])).
% 9.32/3.28  tff(c_12223, plain, (![A_895, B_896, C_897]: (k2_relset_1(A_895, B_896, C_897)=k2_relat_1(C_897) | ~m1_subset_1(C_897, k1_zfmisc_1(k2_zfmisc_1(A_895, B_896))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.32/3.28  tff(c_12308, plain, (![C_904]: (k2_relset_1('#skF_1', '#skF_2', C_904)=k2_relat_1(C_904) | ~m1_subset_1(C_904, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_11499, c_12223])).
% 9.32/3.28  tff(c_12311, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11506, c_12308])).
% 9.32/3.28  tff(c_12321, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12311])).
% 9.32/3.28  tff(c_11930, plain, (![A_870, B_871, C_872]: (k1_relset_1(A_870, B_871, C_872)=k1_relat_1(C_872) | ~m1_subset_1(C_872, k1_zfmisc_1(k2_zfmisc_1(A_870, B_871))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.32/3.28  tff(c_11956, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_9966, c_11930])).
% 9.32/3.28  tff(c_12908, plain, (![B_941, C_942, A_943]: (k1_xboole_0=B_941 | v1_funct_2(C_942, A_943, B_941) | k1_relset_1(A_943, B_941, C_942)!=A_943 | ~m1_subset_1(C_942, k1_zfmisc_1(k2_zfmisc_1(A_943, B_941))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.32/3.28  tff(c_12926, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_9966, c_12908])).
% 9.32/3.28  tff(c_12950, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11956, c_12926])).
% 9.32/3.28  tff(c_12951, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_9965, c_12950])).
% 9.32/3.28  tff(c_12956, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_12951])).
% 9.32/3.28  tff(c_12959, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_12956])).
% 9.32/3.28  tff(c_12962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11510, c_88, c_82, c_12321, c_12959])).
% 9.32/3.28  tff(c_12963, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_12951])).
% 9.32/3.28  tff(c_11565, plain, (![B_828, A_829]: (k1_xboole_0=B_828 | k1_xboole_0=A_829 | k2_zfmisc_1(A_829, B_828)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.32/3.28  tff(c_11568, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_11499, c_11565])).
% 9.32/3.28  tff(c_11638, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_11568])).
% 9.32/3.28  tff(c_12990, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12963, c_11638])).
% 9.32/3.28  tff(c_13002, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12963, c_12963, c_16])).
% 9.32/3.28  tff(c_13145, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13002, c_11499])).
% 9.32/3.28  tff(c_13147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12990, c_13145])).
% 9.32/3.28  tff(c_13149, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_11568])).
% 9.32/3.28  tff(c_13163, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_13149, c_8])).
% 9.32/3.28  tff(c_9973, plain, (![A_710]: (m1_subset_1(k6_partfun1(A_710), k1_zfmisc_1(k2_zfmisc_1(A_710, A_710))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.32/3.28  tff(c_9980, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_9973])).
% 9.32/3.28  tff(c_9989, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_9980, c_20])).
% 9.32/3.28  tff(c_9993, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_9989, c_10])).
% 9.32/3.28  tff(c_13156, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13149, c_13149, c_9993])).
% 9.32/3.28  tff(c_13183, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_13156, c_89])).
% 9.32/3.28  tff(c_13180, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_13156, c_90])).
% 9.32/3.28  tff(c_14224, plain, (![B_1022, A_1023]: (v1_funct_2(B_1022, k1_relat_1(B_1022), A_1023) | ~r1_tarski(k2_relat_1(B_1022), A_1023) | ~v1_funct_1(B_1022) | ~v1_relat_1(B_1022))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.32/3.28  tff(c_14233, plain, (![A_1023]: (v1_funct_2('#skF_3', '#skF_3', A_1023) | ~r1_tarski(k2_relat_1('#skF_3'), A_1023) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13180, c_14224])).
% 9.32/3.28  tff(c_14239, plain, (![A_1023]: (v1_funct_2('#skF_3', '#skF_3', A_1023))), inference(demodulation, [status(thm), theory('equality')], [c_11510, c_88, c_13163, c_13183, c_14233])).
% 9.32/3.28  tff(c_13161, plain, (![B_6]: (k2_zfmisc_1('#skF_3', B_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13149, c_13149, c_16])).
% 9.32/3.28  tff(c_13148, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_11568])).
% 9.32/3.28  tff(c_13736, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13149, c_13149, c_13148])).
% 9.32/3.28  tff(c_13737, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_13736])).
% 9.32/3.28  tff(c_13275, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13149, c_13149, c_13148])).
% 9.32/3.28  tff(c_13276, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_13275])).
% 9.32/3.28  tff(c_9970, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_9966, c_20])).
% 9.32/3.28  tff(c_10008, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_9970, c_9994])).
% 9.32/3.28  tff(c_13201, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10008])).
% 9.32/3.28  tff(c_13398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13163, c_13161, c_13276, c_13201])).
% 9.32/3.28  tff(c_13399, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_13275])).
% 9.32/3.28  tff(c_13406, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_13399, c_13163])).
% 9.32/3.28  tff(c_13159, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13149, c_13149, c_14])).
% 9.32/3.28  tff(c_13496, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13399, c_13399, c_13159])).
% 9.32/3.28  tff(c_13701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13406, c_13496, c_13399, c_13201])).
% 9.32/3.28  tff(c_13702, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_10008])).
% 9.32/3.28  tff(c_13841, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13161, c_13737, c_13702])).
% 9.32/3.28  tff(c_13741, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13737, c_9965])).
% 9.32/3.28  tff(c_13873, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13841, c_13741])).
% 9.32/3.28  tff(c_14245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14239, c_13873])).
% 9.32/3.28  tff(c_14246, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_13736])).
% 9.32/3.28  tff(c_14247, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_13736])).
% 9.32/3.28  tff(c_14272, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14246, c_14247])).
% 9.32/3.28  tff(c_48, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_30, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.32/3.28  tff(c_92, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_48])).
% 9.32/3.28  tff(c_13157, plain, (![A_30]: (v1_funct_2('#skF_3', A_30, '#skF_3') | A_30='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13149, c_13149, c_13149, c_92])).
% 9.32/3.28  tff(c_14527, plain, (![A_1038]: (v1_funct_2('#skF_1', A_1038, '#skF_1') | A_1038='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14246, c_14246, c_14246, c_13157])).
% 9.32/3.28  tff(c_14392, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14246, c_14246, c_13159])).
% 9.32/3.28  tff(c_14438, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14392, c_14246, c_13702])).
% 9.32/3.28  tff(c_14262, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14246, c_9965])).
% 9.32/3.28  tff(c_14462, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14438, c_14262])).
% 9.32/3.28  tff(c_14530, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_14527, c_14462])).
% 9.32/3.28  tff(c_14534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14272, c_14530])).
% 9.32/3.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.28  
% 9.32/3.28  Inference rules
% 9.32/3.28  ----------------------
% 9.32/3.28  #Ref     : 0
% 9.32/3.28  #Sup     : 3011
% 9.32/3.28  #Fact    : 0
% 9.32/3.28  #Define  : 0
% 9.32/3.28  #Split   : 42
% 9.32/3.28  #Chain   : 0
% 9.32/3.28  #Close   : 0
% 9.32/3.28  
% 9.32/3.28  Ordering : KBO
% 9.32/3.28  
% 9.32/3.28  Simplification rules
% 9.32/3.28  ----------------------
% 9.32/3.28  #Subsume      : 437
% 9.32/3.28  #Demod        : 4952
% 9.32/3.28  #Tautology    : 1693
% 9.32/3.28  #SimpNegUnit  : 34
% 9.32/3.28  #BackRed      : 502
% 9.32/3.28  
% 9.32/3.28  #Partial instantiations: 0
% 9.32/3.28  #Strategies tried      : 1
% 9.32/3.28  
% 9.32/3.28  Timing (in seconds)
% 9.32/3.28  ----------------------
% 9.32/3.28  Preprocessing        : 0.36
% 9.32/3.28  Parsing              : 0.19
% 9.32/3.28  CNF conversion       : 0.02
% 9.32/3.28  Main loop            : 2.09
% 9.32/3.28  Inferencing          : 0.69
% 9.32/3.28  Reduction            : 0.79
% 9.32/3.28  Demodulation         : 0.58
% 9.32/3.28  BG Simplification    : 0.07
% 9.32/3.28  Subsumption          : 0.37
% 9.32/3.28  Abstraction          : 0.09
% 9.32/3.28  MUC search           : 0.00
% 9.32/3.28  Cooper               : 0.00
% 9.32/3.28  Total                : 2.55
% 9.32/3.28  Index Insertion      : 0.00
% 9.32/3.28  Index Deletion       : 0.00
% 9.32/3.28  Index Matching       : 0.00
% 9.32/3.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
