%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:30 EST 2020

% Result     : Theorem 17.56s
% Output     : CNFRefutation 18.07s
% Verified   : 
% Statistics : Number of formulae       :  421 (2938 expanded)
%              Number of leaves         :   46 ( 941 expanded)
%              Depth                    :   16
%              Number of atoms          :  821 (7531 expanded)
%              Number of equality atoms :  235 (2181 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_201,negated_conjecture,(
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

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_165,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_184,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(B,C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_155,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_102,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_36040,plain,(
    ! [C_2259,A_2260,B_2261] :
      ( v1_relat_1(C_2259)
      | ~ m1_subset_1(C_2259,k1_zfmisc_1(k2_zfmisc_1(A_2260,B_2261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36064,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_36040])).

tff(c_106,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_100,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_973,plain,(
    ! [C_147,A_148,B_149] :
      ( v4_relat_1(C_147,A_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_997,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_973])).

tff(c_657,plain,(
    ! [C_119,A_120,B_121] :
      ( v1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_679,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_657])).

tff(c_38,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_693,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_679,c_38])).

tff(c_696,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_693])).

tff(c_193,plain,(
    ! [A_75] :
      ( v1_funct_1(k2_funct_1(A_75))
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_96,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_164,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_196,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_193,c_164])).

tff(c_199,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_196])).

tff(c_209,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_216,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_209])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_216])).

tff(c_231,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_48,plain,(
    ! [A_25] :
      ( k2_relat_1(k2_funct_1(A_25)) = k1_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    ! [A_24] :
      ( v1_relat_1(k2_funct_1(A_24))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_98,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1624,plain,(
    ! [A_218,B_219,C_220] :
      ( k2_relset_1(A_218,B_219,C_220) = k2_relat_1(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1634,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_1624])).

tff(c_1648,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1634])).

tff(c_1573,plain,(
    ! [A_208] :
      ( k1_relat_1(k2_funct_1(A_208)) = k2_relat_1(A_208)
      | ~ v2_funct_1(A_208)
      | ~ v1_funct_1(A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_80,plain,(
    ! [A_49] :
      ( v1_funct_2(A_49,k1_relat_1(A_49),k2_relat_1(A_49))
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_10338,plain,(
    ! [A_731] :
      ( v1_funct_2(k2_funct_1(A_731),k2_relat_1(A_731),k2_relat_1(k2_funct_1(A_731)))
      | ~ v1_funct_1(k2_funct_1(A_731))
      | ~ v1_relat_1(k2_funct_1(A_731))
      | ~ v2_funct_1(A_731)
      | ~ v1_funct_1(A_731)
      | ~ v1_relat_1(A_731) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1573,c_80])).

tff(c_10362,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1648,c_10338])).

tff(c_10383,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_106,c_100,c_231,c_10362])).

tff(c_10386,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10383])).

tff(c_10389,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_10386])).

tff(c_10393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_106,c_10389])).

tff(c_10394,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_10383])).

tff(c_10417,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_10394])).

tff(c_10421,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_106,c_100,c_10417])).

tff(c_10395,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10383])).

tff(c_50,plain,(
    ! [A_25] :
      ( k1_relat_1(k2_funct_1(A_25)) = k2_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1711,plain,(
    ! [A_224] :
      ( m1_subset_1(A_224,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_224),k2_relat_1(A_224))))
      | ~ v1_funct_1(A_224)
      | ~ v1_relat_1(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_13216,plain,(
    ! [A_789] :
      ( m1_subset_1(k2_funct_1(A_789),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_789),k2_relat_1(k2_funct_1(A_789)))))
      | ~ v1_funct_1(k2_funct_1(A_789))
      | ~ v1_relat_1(k2_funct_1(A_789))
      | ~ v2_funct_1(A_789)
      | ~ v1_funct_1(A_789)
      | ~ v1_relat_1(A_789) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1711])).

tff(c_13280,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1648,c_13216])).

tff(c_13319,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_106,c_100,c_10395,c_231,c_13280])).

tff(c_13355,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_13319])).

tff(c_13374,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_106,c_100,c_13355])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2458,plain,(
    ! [B_282,D_283,A_284,C_285] :
      ( k1_xboole_0 = B_282
      | m1_subset_1(D_283,k1_zfmisc_1(k2_zfmisc_1(A_284,C_285)))
      | ~ r1_tarski(B_282,C_285)
      | ~ m1_subset_1(D_283,k1_zfmisc_1(k2_zfmisc_1(A_284,B_282)))
      | ~ v1_funct_2(D_283,A_284,B_282)
      | ~ v1_funct_1(D_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_13989,plain,(
    ! [B_800,D_801,A_802,A_803] :
      ( k1_relat_1(B_800) = k1_xboole_0
      | m1_subset_1(D_801,k1_zfmisc_1(k2_zfmisc_1(A_802,A_803)))
      | ~ m1_subset_1(D_801,k1_zfmisc_1(k2_zfmisc_1(A_802,k1_relat_1(B_800))))
      | ~ v1_funct_2(D_801,A_802,k1_relat_1(B_800))
      | ~ v1_funct_1(D_801)
      | ~ v4_relat_1(B_800,A_803)
      | ~ v1_relat_1(B_800) ) ),
    inference(resolution,[status(thm)],[c_28,c_2458])).

tff(c_13991,plain,(
    ! [A_803] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_803)))
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_803)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_13374,c_13989])).

tff(c_14018,plain,(
    ! [A_803] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_803)))
      | ~ v4_relat_1('#skF_4',A_803) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_231,c_10421,c_13991])).

tff(c_14181,plain,(
    ! [A_809] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_809)))
      | ~ v4_relat_1('#skF_4',A_809) ) ),
    inference(negUnitSimplification,[status(thm)],[c_696,c_14018])).

tff(c_230,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_246,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_14233,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_14181,c_246])).

tff(c_14281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_14233])).

tff(c_14282,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_693])).

tff(c_36,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_692,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_679,c_36])).

tff(c_695,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_692])).

tff(c_14303,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14282,c_695])).

tff(c_120,plain,(
    ! [A_63] : k2_zfmisc_1(A_63,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_124,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_34])).

tff(c_275,plain,(
    ! [A_84] :
      ( k2_relat_1(A_84) = k1_xboole_0
      | k1_relat_1(A_84) != k1_xboole_0
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_289,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_275])).

tff(c_292,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_293,plain,(
    ! [A_85,B_86] : m1_subset_1('#skF_1'(A_85,B_86),k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_329,plain,(
    ! [A_90] : m1_subset_1('#skF_1'(A_90,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_293])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_333,plain,(
    ! [A_90] : r1_tarski('#skF_1'(A_90,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_329,c_18])).

tff(c_424,plain,(
    ! [B_97,A_98] :
      ( B_97 = A_98
      | ~ r1_tarski(B_97,A_98)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_426,plain,(
    ! [A_90] :
      ( '#skF_1'(A_90,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,'#skF_1'(A_90,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_333,c_424])).

tff(c_451,plain,(
    ! [A_99] : '#skF_1'(A_99,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_426])).

tff(c_70,plain,(
    ! [A_46,B_47] : v4_relat_1('#skF_1'(A_46,B_47),A_46) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_468,plain,(
    ! [A_99] : v4_relat_1(k1_xboole_0,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_70])).

tff(c_592,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(k1_relat_1(B_111),A_112)
      | ~ v4_relat_1(B_111,A_112)
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_446,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_424])).

tff(c_611,plain,(
    ! [B_113] :
      ( k1_relat_1(B_113) = k1_xboole_0
      | ~ v4_relat_1(B_113,k1_xboole_0)
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_592,c_446])).

tff(c_615,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_468,c_611])).

tff(c_622,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_615])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_622])).

tff(c_625,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_14289,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14282,c_14282,c_625])).

tff(c_14310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14303,c_14289])).

tff(c_14311,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_692])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14337,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14311,c_16])).

tff(c_626,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_14329,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14311,c_14311,c_626])).

tff(c_15252,plain,(
    ! [A_903] :
      ( k2_relat_1(k2_funct_1(A_903)) = k1_relat_1(A_903)
      | ~ v2_funct_1(A_903)
      | ~ v1_funct_1(A_903)
      | ~ v1_relat_1(A_903) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22080,plain,(
    ! [A_1361] :
      ( v1_funct_2(k2_funct_1(A_1361),k1_relat_1(k2_funct_1(A_1361)),k1_relat_1(A_1361))
      | ~ v1_funct_1(k2_funct_1(A_1361))
      | ~ v1_relat_1(k2_funct_1(A_1361))
      | ~ v2_funct_1(A_1361)
      | ~ v1_funct_1(A_1361)
      | ~ v1_relat_1(A_1361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15252,c_80])).

tff(c_22092,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14329,c_22080])).

tff(c_22094,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_106,c_100,c_231,c_22092])).

tff(c_22095,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22094])).

tff(c_22098,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_22095])).

tff(c_22102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_106,c_22098])).

tff(c_22104,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_22094])).

tff(c_14332,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != '#skF_4'
      | A_22 = '#skF_4'
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14311,c_14311,c_36])).

tff(c_22118,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22104,c_14332])).

tff(c_22233,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22118])).

tff(c_22239,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_22233])).

tff(c_22245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_106,c_100,c_14329,c_22239])).

tff(c_22246,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22118])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14334,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14311,c_14311,c_14])).

tff(c_14312,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_692])).

tff(c_14344,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14311,c_14312])).

tff(c_15454,plain,(
    ! [A_926,B_927,C_928] :
      ( k2_relset_1(A_926,B_927,C_928) = k2_relat_1(C_928)
      | ~ m1_subset_1(C_928,k1_zfmisc_1(k2_zfmisc_1(A_926,B_927))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_15467,plain,(
    ! [A_926,B_927] : k2_relset_1(A_926,B_927,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14337,c_15454])).

tff(c_15477,plain,(
    ! [A_926,B_927] : k2_relset_1(A_926,B_927,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14344,c_15467])).

tff(c_15480,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15477,c_98])).

tff(c_15489,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15480,c_246])).

tff(c_15492,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14334,c_15489])).

tff(c_22251,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22246,c_15492])).

tff(c_22259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14337,c_22251])).

tff(c_22260,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_22929,plain,(
    ! [C_1429,A_1430,B_1431] :
      ( v1_relat_1(C_1429)
      | ~ m1_subset_1(C_1429,k1_zfmisc_1(k2_zfmisc_1(A_1430,B_1431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_22955,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_22929])).

tff(c_22261,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_22953,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22261,c_22929])).

tff(c_23804,plain,(
    ! [A_1520,B_1521,C_1522] :
      ( k2_relset_1(A_1520,B_1521,C_1522) = k2_relat_1(C_1522)
      | ~ m1_subset_1(C_1522,k1_zfmisc_1(k2_zfmisc_1(A_1520,B_1521))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_23817,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_23804])).

tff(c_23832,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_23817])).

tff(c_23568,plain,(
    ! [A_1493] :
      ( k1_relat_1(k2_funct_1(A_1493)) = k2_relat_1(A_1493)
      | ~ v2_funct_1(A_1493)
      | ~ v1_funct_1(A_1493)
      | ~ v1_relat_1(A_1493) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32271,plain,(
    ! [A_2015] :
      ( v1_funct_2(k2_funct_1(A_2015),k2_relat_1(A_2015),k2_relat_1(k2_funct_1(A_2015)))
      | ~ v1_funct_1(k2_funct_1(A_2015))
      | ~ v1_relat_1(k2_funct_1(A_2015))
      | ~ v2_funct_1(A_2015)
      | ~ v1_funct_1(A_2015)
      | ~ v1_relat_1(A_2015) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23568,c_80])).

tff(c_32295,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_23832,c_32271])).

tff(c_32316,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22955,c_106,c_100,c_22953,c_231,c_32295])).

tff(c_32324,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_32316])).

tff(c_32328,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22955,c_106,c_100,c_32324])).

tff(c_23904,plain,(
    ! [A_1526] :
      ( m1_subset_1(A_1526,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1526),k2_relat_1(A_1526))))
      | ~ v1_funct_1(A_1526)
      | ~ v1_relat_1(A_1526) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_33486,plain,(
    ! [A_2061] :
      ( m1_subset_1(k2_funct_1(A_2061),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_2061),k2_relat_1(k2_funct_1(A_2061)))))
      | ~ v1_funct_1(k2_funct_1(A_2061))
      | ~ v1_relat_1(k2_funct_1(A_2061))
      | ~ v2_funct_1(A_2061)
      | ~ v1_funct_1(A_2061)
      | ~ v1_relat_1(A_2061) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_23904])).

tff(c_33538,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_23832,c_33486])).

tff(c_33573,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22955,c_106,c_100,c_22953,c_231,c_33538])).

tff(c_33609,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_33573])).

tff(c_33630,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22955,c_106,c_100,c_33609])).

tff(c_22969,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22955,c_38])).

tff(c_23010,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_22969])).

tff(c_23084,plain,(
    ! [C_1440,B_1441,A_1442] :
      ( v5_relat_1(C_1440,B_1441)
      | ~ m1_subset_1(C_1440,k1_zfmisc_1(k2_zfmisc_1(A_1442,B_1441))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_23110,plain,(
    v5_relat_1(k2_funct_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22261,c_23084])).

tff(c_23748,plain,(
    ! [A_1510] :
      ( k2_relat_1(k2_funct_1(A_1510)) = k1_relat_1(A_1510)
      | ~ v2_funct_1(A_1510)
      | ~ v1_funct_1(A_1510)
      | ~ v1_relat_1(A_1510) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30558,plain,(
    ! [A_1898,A_1899] :
      ( r1_tarski(k1_relat_1(A_1898),A_1899)
      | ~ v5_relat_1(k2_funct_1(A_1898),A_1899)
      | ~ v1_relat_1(k2_funct_1(A_1898))
      | ~ v2_funct_1(A_1898)
      | ~ v1_funct_1(A_1898)
      | ~ v1_relat_1(A_1898) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23748,c_32])).

tff(c_30592,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_23110,c_30558])).

tff(c_30605,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22955,c_106,c_100,c_22953,c_30592])).

tff(c_90,plain,(
    ! [B_51,D_53,A_50,C_52] :
      ( k1_xboole_0 = B_51
      | v1_funct_2(D_53,A_50,C_52)
      | ~ r1_tarski(B_51,C_52)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_2(D_53,A_50,B_51)
      | ~ v1_funct_1(D_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_30613,plain,(
    ! [D_53,A_50] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(D_53,A_50,'#skF_2')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_50,k1_relat_1('#skF_4'))))
      | ~ v1_funct_2(D_53,A_50,k1_relat_1('#skF_4'))
      | ~ v1_funct_1(D_53) ) ),
    inference(resolution,[status(thm)],[c_30605,c_90])).

tff(c_30628,plain,(
    ! [D_53,A_50] :
      ( v1_funct_2(D_53,A_50,'#skF_2')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_50,k1_relat_1('#skF_4'))))
      | ~ v1_funct_2(D_53,A_50,k1_relat_1('#skF_4'))
      | ~ v1_funct_1(D_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_23010,c_30613])).

tff(c_34030,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_33630,c_30628])).

tff(c_34071,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_32328,c_34030])).

tff(c_34073,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22260,c_34071])).

tff(c_34074,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22969])).

tff(c_22430,plain,(
    ! [A_1379] :
      ( k1_relat_1(A_1379) = k1_xboole_0
      | k2_relat_1(A_1379) != k1_xboole_0
      | ~ v1_relat_1(A_1379) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22444,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_22430])).

tff(c_22448,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_22444])).

tff(c_22511,plain,(
    ! [A_1385] :
      ( k2_relat_1(A_1385) = k1_xboole_0
      | k1_relat_1(A_1385) != k1_xboole_0
      | ~ v1_relat_1(A_1385) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22520,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_22511])).

tff(c_22531,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22448,c_22520])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22667,plain,(
    ! [C_1398,A_1399,B_1400] :
      ( v4_relat_1(C_1398,A_1399)
      | ~ m1_subset_1(C_1398,k1_zfmisc_1(k2_zfmisc_1(A_1399,B_1400))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_22749,plain,(
    ! [A_1414,A_1415,B_1416] :
      ( v4_relat_1(A_1414,A_1415)
      | ~ r1_tarski(A_1414,k2_zfmisc_1(A_1415,B_1416)) ) ),
    inference(resolution,[status(thm)],[c_20,c_22667])).

tff(c_22784,plain,(
    ! [A_1415,B_1416] : v4_relat_1(k2_zfmisc_1(A_1415,B_1416),A_1415) ),
    inference(resolution,[status(thm)],[c_6,c_22749])).

tff(c_22729,plain,(
    ! [B_1410,A_1411] :
      ( r1_tarski(k1_relat_1(B_1410),A_1411)
      | ~ v4_relat_1(B_1410,A_1411)
      | ~ v1_relat_1(B_1410) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22312,plain,(
    ! [B_1371,A_1372] :
      ( B_1371 = A_1372
      | ~ r1_tarski(B_1371,A_1372)
      | ~ r1_tarski(A_1372,B_1371) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22332,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_22312])).

tff(c_22876,plain,(
    ! [B_1426] :
      ( k1_relat_1(B_1426) = k1_xboole_0
      | ~ v4_relat_1(B_1426,k1_xboole_0)
      | ~ v1_relat_1(B_1426) ) ),
    inference(resolution,[status(thm)],[c_22729,c_22332])).

tff(c_22880,plain,(
    ! [B_1416] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_1416)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_1416)) ) ),
    inference(resolution,[status(thm)],[c_22784,c_22876])).

tff(c_22895,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_14,c_14,c_22880])).

tff(c_22897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22531,c_22895])).

tff(c_22899,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_22444])).

tff(c_34078,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34074,c_34074,c_22899])).

tff(c_22968,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22955,c_36])).

tff(c_23009,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_22968])).

tff(c_34076,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34074,c_23009])).

tff(c_34119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34078,c_34076])).

tff(c_34120,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22968])).

tff(c_34138,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34120,c_8])).

tff(c_34134,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34120,c_34120,c_14])).

tff(c_34123,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34120,c_34120,c_22899])).

tff(c_34137,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34120,c_16])).

tff(c_35923,plain,(
    ! [A_2250,B_2251,C_2252] :
      ( k2_relset_1(A_2250,B_2251,C_2252) = k2_relat_1(C_2252)
      | ~ m1_subset_1(C_2252,k1_zfmisc_1(k2_zfmisc_1(A_2250,B_2251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_35927,plain,(
    ! [A_2250,B_2251] : k2_relset_1(A_2250,B_2251,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34137,c_35923])).

tff(c_35942,plain,(
    ! [A_2250,B_2251] : k2_relset_1(A_2250,B_2251,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34123,c_35927])).

tff(c_35945,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35942,c_98])).

tff(c_35033,plain,(
    ! [A_2156] :
      ( k1_relat_1(k2_funct_1(A_2156)) = k2_relat_1(A_2156)
      | ~ v2_funct_1(A_2156)
      | ~ v1_funct_1(A_2156)
      | ~ v1_relat_1(A_2156) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22981,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != k1_xboole_0
    | k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22953,c_38])).

tff(c_34444,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34120,c_34120,c_22981])).

tff(c_34445,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_34444])).

tff(c_35057,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_35033,c_34445])).

tff(c_35064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22955,c_106,c_100,c_34123,c_35057])).

tff(c_35065,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34444])).

tff(c_22289,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22261,c_18])).

tff(c_22326,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4')
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22289,c_22312])).

tff(c_22908,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22326])).

tff(c_35069,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35065,c_22908])).

tff(c_35953,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35945,c_35069])).

tff(c_35959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34138,c_34134,c_35953])).

tff(c_35960,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_22326])).

tff(c_35970,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35960,c_34])).

tff(c_38114,plain,(
    ! [A_2429,B_2430,C_2431] :
      ( k2_relset_1(A_2429,B_2430,C_2431) = k2_relat_1(C_2431)
      | ~ m1_subset_1(C_2431,k1_zfmisc_1(k2_zfmisc_1(A_2429,B_2430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38130,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_38114])).

tff(c_38145,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_38130])).

tff(c_37363,plain,(
    ! [A_2370] :
      ( k1_relat_1(k2_funct_1(A_2370)) = k2_relat_1(A_2370)
      | ~ v2_funct_1(A_2370)
      | ~ v1_funct_1(A_2370)
      | ~ v1_relat_1(A_2370) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_47073,plain,(
    ! [A_2905] :
      ( v1_funct_2(k2_funct_1(A_2905),k2_relat_1(A_2905),k2_relat_1(k2_funct_1(A_2905)))
      | ~ v1_funct_1(k2_funct_1(A_2905))
      | ~ v1_relat_1(k2_funct_1(A_2905))
      | ~ v2_funct_1(A_2905)
      | ~ v1_funct_1(A_2905)
      | ~ v1_relat_1(A_2905) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37363,c_80])).

tff(c_47091,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38145,c_47073])).

tff(c_47114,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36064,c_106,c_100,c_35970,c_231,c_47091])).

tff(c_47126,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_47114])).

tff(c_47130,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36064,c_106,c_100,c_47126])).

tff(c_37911,plain,(
    ! [A_2417] :
      ( m1_subset_1(A_2417,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2417),k2_relat_1(A_2417))))
      | ~ v1_funct_1(A_2417)
      | ~ v1_relat_1(A_2417) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_47797,plain,(
    ! [A_2946] :
      ( m1_subset_1(k2_funct_1(A_2946),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_2946),k2_relat_1(k2_funct_1(A_2946)))))
      | ~ v1_funct_1(k2_funct_1(A_2946))
      | ~ v1_relat_1(k2_funct_1(A_2946))
      | ~ v2_funct_1(A_2946)
      | ~ v1_funct_1(A_2946)
      | ~ v1_relat_1(A_2946) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_37911])).

tff(c_47843,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38145,c_47797])).

tff(c_47880,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36064,c_106,c_100,c_35970,c_231,c_47843])).

tff(c_47933,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_47880])).

tff(c_47953,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36064,c_106,c_100,c_47933])).

tff(c_36078,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36064,c_38])).

tff(c_36080,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36078])).

tff(c_35963,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35960,c_22261])).

tff(c_36206,plain,(
    ! [C_2270,B_2271,A_2272] :
      ( v5_relat_1(C_2270,B_2271)
      | ~ m1_subset_1(C_2270,k1_zfmisc_1(k2_zfmisc_1(A_2272,B_2271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36247,plain,(
    ! [C_2277] :
      ( v5_relat_1(C_2277,'#skF_2')
      | ~ m1_subset_1(C_2277,k1_zfmisc_1(k2_funct_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35960,c_36206])).

tff(c_36264,plain,(
    v5_relat_1(k2_funct_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_35963,c_36247])).

tff(c_37168,plain,(
    ! [A_2355] :
      ( k2_relat_1(k2_funct_1(A_2355)) = k1_relat_1(A_2355)
      | ~ v2_funct_1(A_2355)
      | ~ v1_funct_1(A_2355)
      | ~ v1_relat_1(A_2355) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44664,plain,(
    ! [A_2763,A_2764] :
      ( r1_tarski(k1_relat_1(A_2763),A_2764)
      | ~ v5_relat_1(k2_funct_1(A_2763),A_2764)
      | ~ v1_relat_1(k2_funct_1(A_2763))
      | ~ v2_funct_1(A_2763)
      | ~ v1_funct_1(A_2763)
      | ~ v1_relat_1(A_2763) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37168,c_32])).

tff(c_44695,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36264,c_44664])).

tff(c_44709,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36064,c_106,c_100,c_35970,c_44695])).

tff(c_44718,plain,(
    ! [D_53,A_50] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(D_53,A_50,'#skF_2')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_50,k1_relat_1('#skF_4'))))
      | ~ v1_funct_2(D_53,A_50,k1_relat_1('#skF_4'))
      | ~ v1_funct_1(D_53) ) ),
    inference(resolution,[status(thm)],[c_44709,c_90])).

tff(c_44733,plain,(
    ! [D_53,A_50] :
      ( v1_funct_2(D_53,A_50,'#skF_2')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_50,k1_relat_1('#skF_4'))))
      | ~ v1_funct_2(D_53,A_50,k1_relat_1('#skF_4'))
      | ~ v1_funct_1(D_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36080,c_44718])).

tff(c_48352,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_47953,c_44733])).

tff(c_48390,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_47130,c_48352])).

tff(c_48392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22260,c_48390])).

tff(c_48393,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36078])).

tff(c_48400,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48393,c_48393,c_22899])).

tff(c_36077,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36064,c_36])).

tff(c_36079,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36077])).

tff(c_48395,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48393,c_36079])).

tff(c_48460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48400,c_48395])).

tff(c_48461,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36077])).

tff(c_48535,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48461,c_48461,c_22899])).

tff(c_40,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) = k1_xboole_0
      | k2_relat_1(A_23) != k1_xboole_0
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36076,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36064,c_40])).

tff(c_48556,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48461,c_48461,c_36076])).

tff(c_48557,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48556])).

tff(c_48599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48535,c_48557])).

tff(c_48601,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48556])).

tff(c_49857,plain,(
    ! [A_3068] :
      ( k1_relat_1(k2_funct_1(A_3068)) = k2_relat_1(A_3068)
      | ~ v2_funct_1(A_3068)
      | ~ v1_funct_1(A_3068)
      | ~ v1_relat_1(A_3068) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36023,plain,(
    ! [B_2257,A_2258] :
      ( k1_xboole_0 = B_2257
      | k1_xboole_0 = A_2258
      | k2_zfmisc_1(A_2258,B_2257) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36026,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k2_funct_1('#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35960,c_36023])).

tff(c_36037,plain,(
    k2_funct_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36026])).

tff(c_35990,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != k1_xboole_0
    | k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35970,c_38])).

tff(c_36039,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36037,c_35990])).

tff(c_48531,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48461,c_36039])).

tff(c_49884,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_49857,c_48531])).

tff(c_49891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36064,c_106,c_100,c_48601,c_49884])).

tff(c_49892,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36026])).

tff(c_49917,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_49892])).

tff(c_49937,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49917,c_8])).

tff(c_49933,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49917,c_49917,c_14])).

tff(c_149,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_156,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_102,c_149])).

tff(c_22327,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_156,c_22312])).

tff(c_22364,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22327])).

tff(c_50008,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49933,c_22364])).

tff(c_50013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49937,c_50008])).

tff(c_50014,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_49892])).

tff(c_50054,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50014,c_8])).

tff(c_50052,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50014,c_50014,c_12])).

tff(c_50242,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50052,c_22364])).

tff(c_50247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50054,c_50242])).

tff(c_50248,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22327])).

tff(c_50251,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50248,c_102])).

tff(c_51067,plain,(
    ! [C_3151,A_3152,B_3153] :
      ( v4_relat_1(C_3151,A_3152)
      | ~ m1_subset_1(C_3151,k1_zfmisc_1(k2_zfmisc_1(A_3152,B_3153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_51219,plain,(
    ! [C_3172] :
      ( v4_relat_1(C_3172,'#skF_2')
      | ~ m1_subset_1(C_3172,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50248,c_51067])).

tff(c_51236,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_50251,c_51219])).

tff(c_50258,plain,(
    v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_50248,c_34])).

tff(c_50269,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50258,c_38])).

tff(c_50368,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50269])).

tff(c_50372,plain,(
    ! [C_3093,A_3094,B_3095] :
      ( v1_relat_1(C_3093)
      | ~ m1_subset_1(C_3093,k1_zfmisc_1(k2_zfmisc_1(A_3094,B_3095))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_50395,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22261,c_50372])).

tff(c_52009,plain,(
    ! [A_3249,B_3250,C_3251] :
      ( k2_relset_1(A_3249,B_3250,C_3251) = k2_relat_1(C_3251)
      | ~ m1_subset_1(C_3251,k1_zfmisc_1(k2_zfmisc_1(A_3249,B_3250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52059,plain,(
    ! [C_3256] :
      ( k2_relset_1('#skF_2','#skF_3',C_3256) = k2_relat_1(C_3256)
      | ~ m1_subset_1(C_3256,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50248,c_52009])).

tff(c_52065,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50251,c_52059])).

tff(c_52076,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_52065])).

tff(c_51613,plain,(
    ! [A_3217] :
      ( k1_relat_1(k2_funct_1(A_3217)) = k2_relat_1(A_3217)
      | ~ v2_funct_1(A_3217)
      | ~ v1_funct_1(A_3217)
      | ~ v1_relat_1(A_3217) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_59382,plain,(
    ! [A_3710] :
      ( v1_funct_2(k2_funct_1(A_3710),k2_relat_1(A_3710),k2_relat_1(k2_funct_1(A_3710)))
      | ~ v1_funct_1(k2_funct_1(A_3710))
      | ~ v1_relat_1(k2_funct_1(A_3710))
      | ~ v2_funct_1(A_3710)
      | ~ v1_funct_1(A_3710)
      | ~ v1_relat_1(A_3710) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51613,c_80])).

tff(c_59397,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_52076,c_59382])).

tff(c_59418,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50258,c_106,c_100,c_50395,c_231,c_59397])).

tff(c_59430,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_59418])).

tff(c_59434,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50258,c_106,c_100,c_59430])).

tff(c_52233,plain,(
    ! [A_3263] :
      ( m1_subset_1(A_3263,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_3263),k2_relat_1(A_3263))))
      | ~ v1_funct_1(A_3263)
      | ~ v1_relat_1(A_3263) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_61777,plain,(
    ! [A_3792] :
      ( m1_subset_1(k2_funct_1(A_3792),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_3792),k2_relat_1(k2_funct_1(A_3792)))))
      | ~ v1_funct_1(k2_funct_1(A_3792))
      | ~ v1_relat_1(k2_funct_1(A_3792))
      | ~ v2_funct_1(A_3792)
      | ~ v1_funct_1(A_3792)
      | ~ v1_relat_1(A_3792) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_52233])).

tff(c_61829,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_52076,c_61777])).

tff(c_61870,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50258,c_106,c_100,c_50395,c_231,c_61829])).

tff(c_61910,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_61870])).

tff(c_61931,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50258,c_106,c_100,c_61910])).

tff(c_52590,plain,(
    ! [B_3278,D_3279,A_3280,C_3281] :
      ( k1_xboole_0 = B_3278
      | v1_funct_2(D_3279,A_3280,C_3281)
      | ~ r1_tarski(B_3278,C_3281)
      | ~ m1_subset_1(D_3279,k1_zfmisc_1(k2_zfmisc_1(A_3280,B_3278)))
      | ~ v1_funct_2(D_3279,A_3280,B_3278)
      | ~ v1_funct_1(D_3279) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_52615,plain,(
    ! [B_17,D_3279,A_3280,A_16] :
      ( k1_relat_1(B_17) = k1_xboole_0
      | v1_funct_2(D_3279,A_3280,A_16)
      | ~ m1_subset_1(D_3279,k1_zfmisc_1(k2_zfmisc_1(A_3280,k1_relat_1(B_17))))
      | ~ v1_funct_2(D_3279,A_3280,k1_relat_1(B_17))
      | ~ v1_funct_1(D_3279)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(resolution,[status(thm)],[c_28,c_52590])).

tff(c_62628,plain,(
    ! [A_16] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_16)
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_16)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_61931,c_52615])).

tff(c_62659,plain,(
    ! [A_16] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_16)
      | ~ v4_relat_1('#skF_4',A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50258,c_231,c_59434,c_62628])).

tff(c_62681,plain,(
    ! [A_3804] :
      ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_3804)
      | ~ v4_relat_1('#skF_4',A_3804) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50368,c_62659])).

tff(c_62684,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_62681,c_22260])).

tff(c_62688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51236,c_62684])).

tff(c_62689,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50269])).

tff(c_50268,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50258,c_36])).

tff(c_50367,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50268])).

tff(c_62692,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62689,c_50367])).

tff(c_62690,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50269])).

tff(c_62712,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62689,c_62690])).

tff(c_42,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) = k1_xboole_0
      | k1_relat_1(A_23) != k1_xboole_0
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_62958,plain,(
    ! [A_3821] :
      ( k2_relat_1(A_3821) = '#skF_4'
      | k1_relat_1(A_3821) != '#skF_4'
      | ~ v1_relat_1(A_3821) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62689,c_62689,c_42])).

tff(c_62961,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_50258,c_62958])).

tff(c_62973,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62712,c_62961])).

tff(c_62975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62692,c_62973])).

tff(c_62976,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50268])).

tff(c_22290,plain,(
    ! [A_1366,B_1367] : m1_subset_1('#skF_1'(A_1366,B_1367),k1_zfmisc_1(k2_zfmisc_1(A_1366,B_1367))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_22301,plain,(
    ! [B_1368] : m1_subset_1('#skF_1'(k1_xboole_0,B_1368),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_22290])).

tff(c_22305,plain,(
    ! [B_1368] : r1_tarski('#skF_1'(k1_xboole_0,B_1368),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22301,c_18])).

tff(c_22314,plain,(
    ! [B_1368] :
      ( '#skF_1'(k1_xboole_0,B_1368) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,'#skF_1'(k1_xboole_0,B_1368)) ) ),
    inference(resolution,[status(thm)],[c_22305,c_22312])).

tff(c_22337,plain,(
    ! [B_1373] : '#skF_1'(k1_xboole_0,B_1373) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22314])).

tff(c_74,plain,(
    ! [A_46,B_47] : v1_xboole_0('#skF_1'(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_22353,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22337,c_74])).

tff(c_62983,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62976,c_22353])).

tff(c_22325,plain,(
    ! [B_1368] : '#skF_1'(k1_xboole_0,B_1368) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22314])).

tff(c_62984,plain,(
    ! [B_1368] : '#skF_1'('#skF_4',B_1368) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62976,c_62976,c_22325])).

tff(c_76,plain,(
    ! [A_46,B_47] : m1_subset_1('#skF_1'(A_46,B_47),k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_65333,plain,(
    ! [C_4038,A_4039,B_4040] :
      ( v1_partfun1(C_4038,A_4039)
      | ~ m1_subset_1(C_4038,k1_zfmisc_1(k2_zfmisc_1(A_4039,B_4040)))
      | ~ v1_xboole_0(A_4039) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_65367,plain,(
    ! [A_4044,B_4045] :
      ( v1_partfun1('#skF_1'(A_4044,B_4045),A_4044)
      | ~ v1_xboole_0(A_4044) ) ),
    inference(resolution,[status(thm)],[c_76,c_65333])).

tff(c_65373,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_62984,c_65367])).

tff(c_65375,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62983,c_65373])).

tff(c_62990,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62976,c_16])).

tff(c_65662,plain,(
    ! [C_4077,A_4078,B_4079] :
      ( v1_funct_2(C_4077,A_4078,B_4079)
      | ~ v1_partfun1(C_4077,A_4078)
      | ~ v1_funct_1(C_4077)
      | ~ m1_subset_1(C_4077,k1_zfmisc_1(k2_zfmisc_1(A_4078,B_4079))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_65675,plain,(
    ! [A_4078,B_4079] :
      ( v1_funct_2('#skF_4',A_4078,B_4079)
      | ~ v1_partfun1('#skF_4',A_4078)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62990,c_65662])).

tff(c_65689,plain,(
    ! [A_4080,B_4081] :
      ( v1_funct_2('#skF_4',A_4080,B_4081)
      | ~ v1_partfun1('#skF_4',A_4080) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_65675])).

tff(c_62987,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62976,c_62976,c_14])).

tff(c_62977,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50268])).

tff(c_62997,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62976,c_62977])).

tff(c_50338,plain,(
    ! [A_3091] :
      ( k1_relat_1(A_3091) = k1_xboole_0
      | k2_relat_1(A_3091) != k1_xboole_0
      | ~ v1_relat_1(A_3091) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50356,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_50338])).

tff(c_63626,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62976,c_62997,c_62976,c_62976,c_62976,c_50356])).

tff(c_64277,plain,(
    ! [A_3920] :
      ( v1_funct_2(A_3920,k1_relat_1(A_3920),k2_relat_1(A_3920))
      | ~ v1_funct_1(A_3920)
      | ~ v1_relat_1(A_3920) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_64280,plain,
    ( v1_funct_2('#skF_4','#skF_4',k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_63626,c_64277])).

tff(c_64285,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50258,c_106,c_62997,c_64280])).

tff(c_64490,plain,(
    ! [A_3952,B_3953,C_3954] :
      ( k2_relset_1(A_3952,B_3953,C_3954) = k2_relat_1(C_3954)
      | ~ m1_subset_1(C_3954,k1_zfmisc_1(k2_zfmisc_1(A_3952,B_3953))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_64500,plain,(
    ! [A_3952,B_3953] : k2_relset_1(A_3952,B_3953,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62990,c_64490])).

tff(c_64509,plain,(
    ! [A_3952,B_3953] : k2_relset_1(A_3952,B_3953,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62997,c_64500])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63546,plain,(
    ! [B_3850,A_3851] :
      ( B_3850 = '#skF_4'
      | A_3851 = '#skF_4'
      | k2_zfmisc_1(A_3851,B_3850) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62976,c_62976,c_62976,c_10])).

tff(c_63563,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_50248,c_63546])).

tff(c_63565,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_63563])).

tff(c_63570,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63565,c_98])).

tff(c_64512,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64509,c_63570])).

tff(c_62989,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62976,c_62976,c_12])).

tff(c_62991,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62976,c_8])).

tff(c_63179,plain,(
    ! [B_3832,A_3833] :
      ( B_3832 = '#skF_4'
      | A_3833 = '#skF_4'
      | k2_zfmisc_1(A_3833,B_3832) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62976,c_62976,c_62976,c_10])).

tff(c_63193,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_50248,c_63179])).

tff(c_63194,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_63193])).

tff(c_63002,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22326])).

tff(c_63272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62991,c_62989,c_63194,c_63002])).

tff(c_63273,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_63193])).

tff(c_63352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62991,c_62987,c_63273,c_63002])).

tff(c_63353,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_22326])).

tff(c_63567,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63565,c_63353])).

tff(c_63573,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62989,c_63567])).

tff(c_63569,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63565,c_22260])).

tff(c_63601,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63573,c_63569])).

tff(c_64520,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64512,c_63601])).

tff(c_64524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64285,c_64520])).

tff(c_64525,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_63563])).

tff(c_64528,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64525,c_63353])).

tff(c_64534,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62987,c_64528])).

tff(c_64530,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64525,c_22260])).

tff(c_64583,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64534,c_64530])).

tff(c_65692,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_65689,c_64583])).

tff(c_65696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65375,c_65692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.56/9.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.56/9.87  
% 17.56/9.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.56/9.87  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 17.56/9.87  
% 17.56/9.87  %Foreground sorts:
% 17.56/9.87  
% 17.56/9.87  
% 17.56/9.87  %Background operators:
% 17.56/9.87  
% 17.56/9.87  
% 17.56/9.87  %Foreground operators:
% 17.56/9.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 17.56/9.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.56/9.87  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 17.56/9.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 17.56/9.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.56/9.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.56/9.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.56/9.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.56/9.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.56/9.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 17.56/9.87  tff('#skF_2', type, '#skF_2': $i).
% 17.56/9.87  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 17.56/9.87  tff('#skF_3', type, '#skF_3': $i).
% 17.56/9.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 17.56/9.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.56/9.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.56/9.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.56/9.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.56/9.87  tff('#skF_4', type, '#skF_4': $i).
% 17.56/9.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.56/9.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 17.56/9.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.56/9.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.56/9.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.56/9.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.56/9.87  
% 18.07/9.92  tff(f_201, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 18.07/9.92  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 18.07/9.92  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 18.07/9.92  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 18.07/9.92  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 18.07/9.92  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 18.07/9.92  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 18.07/9.92  tff(f_165, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 18.07/9.92  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 18.07/9.92  tff(f_184, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 18.07/9.92  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 18.07/9.92  tff(f_74, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 18.07/9.92  tff(f_88, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 18.07/9.92  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 18.07/9.92  tff(f_155, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relset_1)).
% 18.07/9.92  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 18.07/9.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.07/9.92  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 18.07/9.92  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 18.07/9.92  tff(f_144, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 18.07/9.92  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 18.07/9.92  tff(c_102, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 18.07/9.92  tff(c_36040, plain, (![C_2259, A_2260, B_2261]: (v1_relat_1(C_2259) | ~m1_subset_1(C_2259, k1_zfmisc_1(k2_zfmisc_1(A_2260, B_2261))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.07/9.92  tff(c_36064, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_36040])).
% 18.07/9.92  tff(c_106, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 18.07/9.92  tff(c_100, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 18.07/9.92  tff(c_973, plain, (![C_147, A_148, B_149]: (v4_relat_1(C_147, A_148) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 18.07/9.92  tff(c_997, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_102, c_973])).
% 18.07/9.92  tff(c_657, plain, (![C_119, A_120, B_121]: (v1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.07/9.92  tff(c_679, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_657])).
% 18.07/9.92  tff(c_38, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 18.07/9.92  tff(c_693, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_679, c_38])).
% 18.07/9.92  tff(c_696, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_693])).
% 18.07/9.92  tff(c_193, plain, (![A_75]: (v1_funct_1(k2_funct_1(A_75)) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.07/9.92  tff(c_96, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 18.07/9.92  tff(c_164, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_96])).
% 18.07/9.92  tff(c_196, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_193, c_164])).
% 18.07/9.92  tff(c_199, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_196])).
% 18.07/9.92  tff(c_209, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.07/9.92  tff(c_216, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_209])).
% 18.07/9.92  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_216])).
% 18.07/9.92  tff(c_231, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_96])).
% 18.07/9.92  tff(c_48, plain, (![A_25]: (k2_relat_1(k2_funct_1(A_25))=k1_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.07/9.92  tff(c_46, plain, (![A_24]: (v1_relat_1(k2_funct_1(A_24)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.07/9.92  tff(c_98, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_201])).
% 18.07/9.92  tff(c_1624, plain, (![A_218, B_219, C_220]: (k2_relset_1(A_218, B_219, C_220)=k2_relat_1(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 18.07/9.92  tff(c_1634, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_1624])).
% 18.07/9.92  tff(c_1648, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1634])).
% 18.07/9.92  tff(c_1573, plain, (![A_208]: (k1_relat_1(k2_funct_1(A_208))=k2_relat_1(A_208) | ~v2_funct_1(A_208) | ~v1_funct_1(A_208) | ~v1_relat_1(A_208))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.07/9.92  tff(c_80, plain, (![A_49]: (v1_funct_2(A_49, k1_relat_1(A_49), k2_relat_1(A_49)) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_165])).
% 18.07/9.92  tff(c_10338, plain, (![A_731]: (v1_funct_2(k2_funct_1(A_731), k2_relat_1(A_731), k2_relat_1(k2_funct_1(A_731))) | ~v1_funct_1(k2_funct_1(A_731)) | ~v1_relat_1(k2_funct_1(A_731)) | ~v2_funct_1(A_731) | ~v1_funct_1(A_731) | ~v1_relat_1(A_731))), inference(superposition, [status(thm), theory('equality')], [c_1573, c_80])).
% 18.07/9.92  tff(c_10362, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1648, c_10338])).
% 18.07/9.92  tff(c_10383, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_679, c_106, c_100, c_231, c_10362])).
% 18.07/9.92  tff(c_10386, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_10383])).
% 18.07/9.92  tff(c_10389, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_10386])).
% 18.07/9.92  tff(c_10393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_679, c_106, c_10389])).
% 18.07/9.92  tff(c_10394, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4')))), inference(splitRight, [status(thm)], [c_10383])).
% 18.07/9.92  tff(c_10417, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_10394])).
% 18.07/9.92  tff(c_10421, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_679, c_106, c_100, c_10417])).
% 18.07/9.92  tff(c_10395, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_10383])).
% 18.07/9.92  tff(c_50, plain, (![A_25]: (k1_relat_1(k2_funct_1(A_25))=k2_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.07/9.92  tff(c_1711, plain, (![A_224]: (m1_subset_1(A_224, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_224), k2_relat_1(A_224)))) | ~v1_funct_1(A_224) | ~v1_relat_1(A_224))), inference(cnfTransformation, [status(thm)], [f_165])).
% 18.07/9.92  tff(c_13216, plain, (![A_789]: (m1_subset_1(k2_funct_1(A_789), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_789), k2_relat_1(k2_funct_1(A_789))))) | ~v1_funct_1(k2_funct_1(A_789)) | ~v1_relat_1(k2_funct_1(A_789)) | ~v2_funct_1(A_789) | ~v1_funct_1(A_789) | ~v1_relat_1(A_789))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1711])).
% 18.07/9.92  tff(c_13280, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1648, c_13216])).
% 18.07/9.92  tff(c_13319, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_679, c_106, c_100, c_10395, c_231, c_13280])).
% 18.07/9.92  tff(c_13355, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_13319])).
% 18.07/9.92  tff(c_13374, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_679, c_106, c_100, c_13355])).
% 18.07/9.92  tff(c_28, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.07/9.92  tff(c_2458, plain, (![B_282, D_283, A_284, C_285]: (k1_xboole_0=B_282 | m1_subset_1(D_283, k1_zfmisc_1(k2_zfmisc_1(A_284, C_285))) | ~r1_tarski(B_282, C_285) | ~m1_subset_1(D_283, k1_zfmisc_1(k2_zfmisc_1(A_284, B_282))) | ~v1_funct_2(D_283, A_284, B_282) | ~v1_funct_1(D_283))), inference(cnfTransformation, [status(thm)], [f_184])).
% 18.07/9.92  tff(c_13989, plain, (![B_800, D_801, A_802, A_803]: (k1_relat_1(B_800)=k1_xboole_0 | m1_subset_1(D_801, k1_zfmisc_1(k2_zfmisc_1(A_802, A_803))) | ~m1_subset_1(D_801, k1_zfmisc_1(k2_zfmisc_1(A_802, k1_relat_1(B_800)))) | ~v1_funct_2(D_801, A_802, k1_relat_1(B_800)) | ~v1_funct_1(D_801) | ~v4_relat_1(B_800, A_803) | ~v1_relat_1(B_800))), inference(resolution, [status(thm)], [c_28, c_2458])).
% 18.07/9.92  tff(c_13991, plain, (![A_803]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_803))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_803) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_13374, c_13989])).
% 18.07/9.92  tff(c_14018, plain, (![A_803]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_803))) | ~v4_relat_1('#skF_4', A_803))), inference(demodulation, [status(thm), theory('equality')], [c_679, c_231, c_10421, c_13991])).
% 18.07/9.92  tff(c_14181, plain, (![A_809]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_809))) | ~v4_relat_1('#skF_4', A_809))), inference(negUnitSimplification, [status(thm)], [c_696, c_14018])).
% 18.07/9.92  tff(c_230, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_96])).
% 18.07/9.92  tff(c_246, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_230])).
% 18.07/9.92  tff(c_14233, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_14181, c_246])).
% 18.07/9.92  tff(c_14281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_997, c_14233])).
% 18.07/9.92  tff(c_14282, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_693])).
% 18.07/9.92  tff(c_36, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 18.07/9.92  tff(c_692, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_679, c_36])).
% 18.07/9.92  tff(c_695, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_692])).
% 18.07/9.92  tff(c_14303, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14282, c_695])).
% 18.07/9.92  tff(c_120, plain, (![A_63]: (k2_zfmisc_1(A_63, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.07/9.92  tff(c_34, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 18.07/9.92  tff(c_124, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_120, c_34])).
% 18.07/9.92  tff(c_275, plain, (![A_84]: (k2_relat_1(A_84)=k1_xboole_0 | k1_relat_1(A_84)!=k1_xboole_0 | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.07/9.92  tff(c_289, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_124, c_275])).
% 18.07/9.92  tff(c_292, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_289])).
% 18.07/9.92  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.07/9.92  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.07/9.92  tff(c_293, plain, (![A_85, B_86]: (m1_subset_1('#skF_1'(A_85, B_86), k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 18.07/9.92  tff(c_329, plain, (![A_90]: (m1_subset_1('#skF_1'(A_90, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_293])).
% 18.07/9.92  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.07/9.92  tff(c_333, plain, (![A_90]: (r1_tarski('#skF_1'(A_90, k1_xboole_0), k1_xboole_0))), inference(resolution, [status(thm)], [c_329, c_18])).
% 18.07/9.92  tff(c_424, plain, (![B_97, A_98]: (B_97=A_98 | ~r1_tarski(B_97, A_98) | ~r1_tarski(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.07/9.92  tff(c_426, plain, (![A_90]: ('#skF_1'(A_90, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_1'(A_90, k1_xboole_0)))), inference(resolution, [status(thm)], [c_333, c_424])).
% 18.07/9.92  tff(c_451, plain, (![A_99]: ('#skF_1'(A_99, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_426])).
% 18.07/9.92  tff(c_70, plain, (![A_46, B_47]: (v4_relat_1('#skF_1'(A_46, B_47), A_46))), inference(cnfTransformation, [status(thm)], [f_155])).
% 18.07/9.92  tff(c_468, plain, (![A_99]: (v4_relat_1(k1_xboole_0, A_99))), inference(superposition, [status(thm), theory('equality')], [c_451, c_70])).
% 18.07/9.92  tff(c_592, plain, (![B_111, A_112]: (r1_tarski(k1_relat_1(B_111), A_112) | ~v4_relat_1(B_111, A_112) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.07/9.92  tff(c_446, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_424])).
% 18.07/9.92  tff(c_611, plain, (![B_113]: (k1_relat_1(B_113)=k1_xboole_0 | ~v4_relat_1(B_113, k1_xboole_0) | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_592, c_446])).
% 18.07/9.92  tff(c_615, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_468, c_611])).
% 18.07/9.92  tff(c_622, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_124, c_615])).
% 18.07/9.92  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_292, c_622])).
% 18.07/9.92  tff(c_625, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_289])).
% 18.07/9.92  tff(c_14289, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14282, c_14282, c_625])).
% 18.07/9.92  tff(c_14310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14303, c_14289])).
% 18.07/9.92  tff(c_14311, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_692])).
% 18.07/9.92  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.07/9.92  tff(c_14337, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_14311, c_16])).
% 18.07/9.92  tff(c_626, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_289])).
% 18.07/9.92  tff(c_14329, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14311, c_14311, c_626])).
% 18.07/9.92  tff(c_15252, plain, (![A_903]: (k2_relat_1(k2_funct_1(A_903))=k1_relat_1(A_903) | ~v2_funct_1(A_903) | ~v1_funct_1(A_903) | ~v1_relat_1(A_903))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.07/9.92  tff(c_22080, plain, (![A_1361]: (v1_funct_2(k2_funct_1(A_1361), k1_relat_1(k2_funct_1(A_1361)), k1_relat_1(A_1361)) | ~v1_funct_1(k2_funct_1(A_1361)) | ~v1_relat_1(k2_funct_1(A_1361)) | ~v2_funct_1(A_1361) | ~v1_funct_1(A_1361) | ~v1_relat_1(A_1361))), inference(superposition, [status(thm), theory('equality')], [c_15252, c_80])).
% 18.07/9.92  tff(c_22092, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14329, c_22080])).
% 18.07/9.92  tff(c_22094, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_679, c_106, c_100, c_231, c_22092])).
% 18.07/9.92  tff(c_22095, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_22094])).
% 18.07/9.92  tff(c_22098, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_22095])).
% 18.07/9.92  tff(c_22102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_679, c_106, c_22098])).
% 18.07/9.92  tff(c_22104, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_22094])).
% 18.07/9.92  tff(c_14332, plain, (![A_22]: (k2_relat_1(A_22)!='#skF_4' | A_22='#skF_4' | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_14311, c_14311, c_36])).
% 18.07/9.92  tff(c_22118, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_22104, c_14332])).
% 18.07/9.92  tff(c_22233, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_22118])).
% 18.07/9.92  tff(c_22239, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_22233])).
% 18.07/9.92  tff(c_22245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_679, c_106, c_100, c_14329, c_22239])).
% 18.07/9.92  tff(c_22246, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_22118])).
% 18.07/9.92  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.07/9.92  tff(c_14334, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14311, c_14311, c_14])).
% 18.07/9.92  tff(c_14312, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_692])).
% 18.07/9.92  tff(c_14344, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14311, c_14312])).
% 18.07/9.92  tff(c_15454, plain, (![A_926, B_927, C_928]: (k2_relset_1(A_926, B_927, C_928)=k2_relat_1(C_928) | ~m1_subset_1(C_928, k1_zfmisc_1(k2_zfmisc_1(A_926, B_927))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 18.07/9.92  tff(c_15467, plain, (![A_926, B_927]: (k2_relset_1(A_926, B_927, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14337, c_15454])).
% 18.07/9.92  tff(c_15477, plain, (![A_926, B_927]: (k2_relset_1(A_926, B_927, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14344, c_15467])).
% 18.07/9.92  tff(c_15480, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15477, c_98])).
% 18.07/9.92  tff(c_15489, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_15480, c_246])).
% 18.07/9.92  tff(c_15492, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14334, c_15489])).
% 18.07/9.92  tff(c_22251, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22246, c_15492])).
% 18.07/9.92  tff(c_22259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14337, c_22251])).
% 18.07/9.92  tff(c_22260, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_230])).
% 18.07/9.92  tff(c_22929, plain, (![C_1429, A_1430, B_1431]: (v1_relat_1(C_1429) | ~m1_subset_1(C_1429, k1_zfmisc_1(k2_zfmisc_1(A_1430, B_1431))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.07/9.92  tff(c_22955, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_22929])).
% 18.07/9.92  tff(c_22261, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_230])).
% 18.07/9.92  tff(c_22953, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22261, c_22929])).
% 18.07/9.92  tff(c_23804, plain, (![A_1520, B_1521, C_1522]: (k2_relset_1(A_1520, B_1521, C_1522)=k2_relat_1(C_1522) | ~m1_subset_1(C_1522, k1_zfmisc_1(k2_zfmisc_1(A_1520, B_1521))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 18.07/9.92  tff(c_23817, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_23804])).
% 18.07/9.92  tff(c_23832, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_23817])).
% 18.07/9.92  tff(c_23568, plain, (![A_1493]: (k1_relat_1(k2_funct_1(A_1493))=k2_relat_1(A_1493) | ~v2_funct_1(A_1493) | ~v1_funct_1(A_1493) | ~v1_relat_1(A_1493))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.07/9.92  tff(c_32271, plain, (![A_2015]: (v1_funct_2(k2_funct_1(A_2015), k2_relat_1(A_2015), k2_relat_1(k2_funct_1(A_2015))) | ~v1_funct_1(k2_funct_1(A_2015)) | ~v1_relat_1(k2_funct_1(A_2015)) | ~v2_funct_1(A_2015) | ~v1_funct_1(A_2015) | ~v1_relat_1(A_2015))), inference(superposition, [status(thm), theory('equality')], [c_23568, c_80])).
% 18.07/9.92  tff(c_32295, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_23832, c_32271])).
% 18.07/9.92  tff(c_32316, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_22955, c_106, c_100, c_22953, c_231, c_32295])).
% 18.07/9.92  tff(c_32324, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_32316])).
% 18.07/9.92  tff(c_32328, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22955, c_106, c_100, c_32324])).
% 18.07/9.92  tff(c_23904, plain, (![A_1526]: (m1_subset_1(A_1526, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1526), k2_relat_1(A_1526)))) | ~v1_funct_1(A_1526) | ~v1_relat_1(A_1526))), inference(cnfTransformation, [status(thm)], [f_165])).
% 18.07/9.92  tff(c_33486, plain, (![A_2061]: (m1_subset_1(k2_funct_1(A_2061), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_2061), k2_relat_1(k2_funct_1(A_2061))))) | ~v1_funct_1(k2_funct_1(A_2061)) | ~v1_relat_1(k2_funct_1(A_2061)) | ~v2_funct_1(A_2061) | ~v1_funct_1(A_2061) | ~v1_relat_1(A_2061))), inference(superposition, [status(thm), theory('equality')], [c_50, c_23904])).
% 18.07/9.92  tff(c_33538, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_23832, c_33486])).
% 18.07/9.92  tff(c_33573, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_22955, c_106, c_100, c_22953, c_231, c_33538])).
% 18.07/9.92  tff(c_33609, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_33573])).
% 18.07/9.92  tff(c_33630, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_22955, c_106, c_100, c_33609])).
% 18.07/9.92  tff(c_22969, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22955, c_38])).
% 18.07/9.92  tff(c_23010, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_22969])).
% 18.07/9.92  tff(c_23084, plain, (![C_1440, B_1441, A_1442]: (v5_relat_1(C_1440, B_1441) | ~m1_subset_1(C_1440, k1_zfmisc_1(k2_zfmisc_1(A_1442, B_1441))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 18.07/9.92  tff(c_23110, plain, (v5_relat_1(k2_funct_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_22261, c_23084])).
% 18.07/9.92  tff(c_23748, plain, (![A_1510]: (k2_relat_1(k2_funct_1(A_1510))=k1_relat_1(A_1510) | ~v2_funct_1(A_1510) | ~v1_funct_1(A_1510) | ~v1_relat_1(A_1510))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.07/9.92  tff(c_32, plain, (![B_19, A_18]: (r1_tarski(k2_relat_1(B_19), A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 18.07/9.92  tff(c_30558, plain, (![A_1898, A_1899]: (r1_tarski(k1_relat_1(A_1898), A_1899) | ~v5_relat_1(k2_funct_1(A_1898), A_1899) | ~v1_relat_1(k2_funct_1(A_1898)) | ~v2_funct_1(A_1898) | ~v1_funct_1(A_1898) | ~v1_relat_1(A_1898))), inference(superposition, [status(thm), theory('equality')], [c_23748, c_32])).
% 18.07/9.92  tff(c_30592, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_23110, c_30558])).
% 18.07/9.92  tff(c_30605, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22955, c_106, c_100, c_22953, c_30592])).
% 18.07/9.92  tff(c_90, plain, (![B_51, D_53, A_50, C_52]: (k1_xboole_0=B_51 | v1_funct_2(D_53, A_50, C_52) | ~r1_tarski(B_51, C_52) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_funct_2(D_53, A_50, B_51) | ~v1_funct_1(D_53))), inference(cnfTransformation, [status(thm)], [f_184])).
% 18.07/9.92  tff(c_30613, plain, (![D_53, A_50]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(D_53, A_50, '#skF_2') | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_50, k1_relat_1('#skF_4')))) | ~v1_funct_2(D_53, A_50, k1_relat_1('#skF_4')) | ~v1_funct_1(D_53))), inference(resolution, [status(thm)], [c_30605, c_90])).
% 18.07/9.92  tff(c_30628, plain, (![D_53, A_50]: (v1_funct_2(D_53, A_50, '#skF_2') | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_50, k1_relat_1('#skF_4')))) | ~v1_funct_2(D_53, A_50, k1_relat_1('#skF_4')) | ~v1_funct_1(D_53))), inference(negUnitSimplification, [status(thm)], [c_23010, c_30613])).
% 18.07/9.92  tff(c_34030, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_33630, c_30628])).
% 18.07/9.92  tff(c_34071, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_32328, c_34030])).
% 18.07/9.92  tff(c_34073, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22260, c_34071])).
% 18.07/9.92  tff(c_34074, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_22969])).
% 18.07/9.92  tff(c_22430, plain, (![A_1379]: (k1_relat_1(A_1379)=k1_xboole_0 | k2_relat_1(A_1379)!=k1_xboole_0 | ~v1_relat_1(A_1379))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.07/9.92  tff(c_22444, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_124, c_22430])).
% 18.07/9.92  tff(c_22448, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_22444])).
% 18.07/9.92  tff(c_22511, plain, (![A_1385]: (k2_relat_1(A_1385)=k1_xboole_0 | k1_relat_1(A_1385)!=k1_xboole_0 | ~v1_relat_1(A_1385))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.07/9.92  tff(c_22520, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_124, c_22511])).
% 18.07/9.92  tff(c_22531, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_22448, c_22520])).
% 18.07/9.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.07/9.92  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.07/9.92  tff(c_22667, plain, (![C_1398, A_1399, B_1400]: (v4_relat_1(C_1398, A_1399) | ~m1_subset_1(C_1398, k1_zfmisc_1(k2_zfmisc_1(A_1399, B_1400))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 18.07/9.92  tff(c_22749, plain, (![A_1414, A_1415, B_1416]: (v4_relat_1(A_1414, A_1415) | ~r1_tarski(A_1414, k2_zfmisc_1(A_1415, B_1416)))), inference(resolution, [status(thm)], [c_20, c_22667])).
% 18.07/9.92  tff(c_22784, plain, (![A_1415, B_1416]: (v4_relat_1(k2_zfmisc_1(A_1415, B_1416), A_1415))), inference(resolution, [status(thm)], [c_6, c_22749])).
% 18.07/9.92  tff(c_22729, plain, (![B_1410, A_1411]: (r1_tarski(k1_relat_1(B_1410), A_1411) | ~v4_relat_1(B_1410, A_1411) | ~v1_relat_1(B_1410))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.07/9.92  tff(c_22312, plain, (![B_1371, A_1372]: (B_1371=A_1372 | ~r1_tarski(B_1371, A_1372) | ~r1_tarski(A_1372, B_1371))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.07/9.92  tff(c_22332, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_22312])).
% 18.07/9.92  tff(c_22876, plain, (![B_1426]: (k1_relat_1(B_1426)=k1_xboole_0 | ~v4_relat_1(B_1426, k1_xboole_0) | ~v1_relat_1(B_1426))), inference(resolution, [status(thm)], [c_22729, c_22332])).
% 18.07/9.92  tff(c_22880, plain, (![B_1416]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_1416))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_1416)))), inference(resolution, [status(thm)], [c_22784, c_22876])).
% 18.07/9.92  tff(c_22895, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_124, c_14, c_14, c_22880])).
% 18.07/9.92  tff(c_22897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22531, c_22895])).
% 18.07/9.92  tff(c_22899, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_22444])).
% 18.07/9.92  tff(c_34078, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34074, c_34074, c_22899])).
% 18.07/9.92  tff(c_22968, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22955, c_36])).
% 18.07/9.92  tff(c_23009, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_22968])).
% 18.07/9.92  tff(c_34076, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34074, c_23009])).
% 18.07/9.92  tff(c_34119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34078, c_34076])).
% 18.07/9.92  tff(c_34120, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_22968])).
% 18.07/9.92  tff(c_34138, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_34120, c_8])).
% 18.07/9.92  tff(c_34134, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34120, c_34120, c_14])).
% 18.07/9.92  tff(c_34123, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34120, c_34120, c_22899])).
% 18.07/9.92  tff(c_34137, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_34120, c_16])).
% 18.07/9.92  tff(c_35923, plain, (![A_2250, B_2251, C_2252]: (k2_relset_1(A_2250, B_2251, C_2252)=k2_relat_1(C_2252) | ~m1_subset_1(C_2252, k1_zfmisc_1(k2_zfmisc_1(A_2250, B_2251))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 18.07/9.92  tff(c_35927, plain, (![A_2250, B_2251]: (k2_relset_1(A_2250, B_2251, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34137, c_35923])).
% 18.07/9.92  tff(c_35942, plain, (![A_2250, B_2251]: (k2_relset_1(A_2250, B_2251, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34123, c_35927])).
% 18.07/9.92  tff(c_35945, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35942, c_98])).
% 18.07/9.92  tff(c_35033, plain, (![A_2156]: (k1_relat_1(k2_funct_1(A_2156))=k2_relat_1(A_2156) | ~v2_funct_1(A_2156) | ~v1_funct_1(A_2156) | ~v1_relat_1(A_2156))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.07/9.92  tff(c_22981, plain, (k1_relat_1(k2_funct_1('#skF_4'))!=k1_xboole_0 | k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_22953, c_38])).
% 18.07/9.92  tff(c_34444, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34120, c_34120, c_22981])).
% 18.07/9.92  tff(c_34445, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_34444])).
% 18.07/9.92  tff(c_35057, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_35033, c_34445])).
% 18.07/9.92  tff(c_35064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22955, c_106, c_100, c_34123, c_35057])).
% 18.07/9.92  tff(c_35065, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_34444])).
% 18.07/9.92  tff(c_22289, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_22261, c_18])).
% 18.07/9.92  tff(c_22326, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4') | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22289, c_22312])).
% 18.07/9.92  tff(c_22908, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_22326])).
% 18.07/9.92  tff(c_35069, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35065, c_22908])).
% 18.07/9.92  tff(c_35953, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35945, c_35069])).
% 18.07/9.92  tff(c_35959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34138, c_34134, c_35953])).
% 18.07/9.92  tff(c_35960, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_22326])).
% 18.07/9.92  tff(c_35970, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_35960, c_34])).
% 18.07/9.92  tff(c_38114, plain, (![A_2429, B_2430, C_2431]: (k2_relset_1(A_2429, B_2430, C_2431)=k2_relat_1(C_2431) | ~m1_subset_1(C_2431, k1_zfmisc_1(k2_zfmisc_1(A_2429, B_2430))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 18.07/9.92  tff(c_38130, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_38114])).
% 18.07/9.92  tff(c_38145, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_38130])).
% 18.07/9.92  tff(c_37363, plain, (![A_2370]: (k1_relat_1(k2_funct_1(A_2370))=k2_relat_1(A_2370) | ~v2_funct_1(A_2370) | ~v1_funct_1(A_2370) | ~v1_relat_1(A_2370))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.07/9.92  tff(c_47073, plain, (![A_2905]: (v1_funct_2(k2_funct_1(A_2905), k2_relat_1(A_2905), k2_relat_1(k2_funct_1(A_2905))) | ~v1_funct_1(k2_funct_1(A_2905)) | ~v1_relat_1(k2_funct_1(A_2905)) | ~v2_funct_1(A_2905) | ~v1_funct_1(A_2905) | ~v1_relat_1(A_2905))), inference(superposition, [status(thm), theory('equality')], [c_37363, c_80])).
% 18.07/9.92  tff(c_47091, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38145, c_47073])).
% 18.07/9.92  tff(c_47114, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36064, c_106, c_100, c_35970, c_231, c_47091])).
% 18.07/9.92  tff(c_47126, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_47114])).
% 18.07/9.92  tff(c_47130, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36064, c_106, c_100, c_47126])).
% 18.07/9.92  tff(c_37911, plain, (![A_2417]: (m1_subset_1(A_2417, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2417), k2_relat_1(A_2417)))) | ~v1_funct_1(A_2417) | ~v1_relat_1(A_2417))), inference(cnfTransformation, [status(thm)], [f_165])).
% 18.07/9.92  tff(c_47797, plain, (![A_2946]: (m1_subset_1(k2_funct_1(A_2946), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_2946), k2_relat_1(k2_funct_1(A_2946))))) | ~v1_funct_1(k2_funct_1(A_2946)) | ~v1_relat_1(k2_funct_1(A_2946)) | ~v2_funct_1(A_2946) | ~v1_funct_1(A_2946) | ~v1_relat_1(A_2946))), inference(superposition, [status(thm), theory('equality')], [c_50, c_37911])).
% 18.07/9.92  tff(c_47843, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38145, c_47797])).
% 18.07/9.92  tff(c_47880, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_36064, c_106, c_100, c_35970, c_231, c_47843])).
% 18.07/9.92  tff(c_47933, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_47880])).
% 18.07/9.92  tff(c_47953, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36064, c_106, c_100, c_47933])).
% 18.07/9.92  tff(c_36078, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36064, c_38])).
% 18.07/9.92  tff(c_36080, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36078])).
% 18.07/9.92  tff(c_35963, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_35960, c_22261])).
% 18.07/9.92  tff(c_36206, plain, (![C_2270, B_2271, A_2272]: (v5_relat_1(C_2270, B_2271) | ~m1_subset_1(C_2270, k1_zfmisc_1(k2_zfmisc_1(A_2272, B_2271))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 18.07/9.92  tff(c_36247, plain, (![C_2277]: (v5_relat_1(C_2277, '#skF_2') | ~m1_subset_1(C_2277, k1_zfmisc_1(k2_funct_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_35960, c_36206])).
% 18.07/9.92  tff(c_36264, plain, (v5_relat_1(k2_funct_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_35963, c_36247])).
% 18.07/9.92  tff(c_37168, plain, (![A_2355]: (k2_relat_1(k2_funct_1(A_2355))=k1_relat_1(A_2355) | ~v2_funct_1(A_2355) | ~v1_funct_1(A_2355) | ~v1_relat_1(A_2355))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.07/9.92  tff(c_44664, plain, (![A_2763, A_2764]: (r1_tarski(k1_relat_1(A_2763), A_2764) | ~v5_relat_1(k2_funct_1(A_2763), A_2764) | ~v1_relat_1(k2_funct_1(A_2763)) | ~v2_funct_1(A_2763) | ~v1_funct_1(A_2763) | ~v1_relat_1(A_2763))), inference(superposition, [status(thm), theory('equality')], [c_37168, c_32])).
% 18.07/9.92  tff(c_44695, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36264, c_44664])).
% 18.07/9.92  tff(c_44709, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36064, c_106, c_100, c_35970, c_44695])).
% 18.07/9.92  tff(c_44718, plain, (![D_53, A_50]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(D_53, A_50, '#skF_2') | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_50, k1_relat_1('#skF_4')))) | ~v1_funct_2(D_53, A_50, k1_relat_1('#skF_4')) | ~v1_funct_1(D_53))), inference(resolution, [status(thm)], [c_44709, c_90])).
% 18.07/9.92  tff(c_44733, plain, (![D_53, A_50]: (v1_funct_2(D_53, A_50, '#skF_2') | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_50, k1_relat_1('#skF_4')))) | ~v1_funct_2(D_53, A_50, k1_relat_1('#skF_4')) | ~v1_funct_1(D_53))), inference(negUnitSimplification, [status(thm)], [c_36080, c_44718])).
% 18.07/9.92  tff(c_48352, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_47953, c_44733])).
% 18.07/9.92  tff(c_48390, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_47130, c_48352])).
% 18.07/9.92  tff(c_48392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22260, c_48390])).
% 18.07/9.92  tff(c_48393, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_36078])).
% 18.07/9.92  tff(c_48400, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48393, c_48393, c_22899])).
% 18.07/9.92  tff(c_36077, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36064, c_36])).
% 18.07/9.92  tff(c_36079, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36077])).
% 18.07/9.92  tff(c_48395, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48393, c_36079])).
% 18.07/9.92  tff(c_48460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48400, c_48395])).
% 18.07/9.92  tff(c_48461, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_36077])).
% 18.07/9.92  tff(c_48535, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48461, c_48461, c_22899])).
% 18.07/9.92  tff(c_40, plain, (![A_23]: (k1_relat_1(A_23)=k1_xboole_0 | k2_relat_1(A_23)!=k1_xboole_0 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.07/9.92  tff(c_36076, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_36064, c_40])).
% 18.07/9.92  tff(c_48556, plain, (k1_relat_1('#skF_4')='#skF_4' | k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48461, c_48461, c_36076])).
% 18.07/9.92  tff(c_48557, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_48556])).
% 18.07/9.92  tff(c_48599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48535, c_48557])).
% 18.07/9.92  tff(c_48601, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_48556])).
% 18.07/9.92  tff(c_49857, plain, (![A_3068]: (k1_relat_1(k2_funct_1(A_3068))=k2_relat_1(A_3068) | ~v2_funct_1(A_3068) | ~v1_funct_1(A_3068) | ~v1_relat_1(A_3068))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.07/9.92  tff(c_36023, plain, (![B_2257, A_2258]: (k1_xboole_0=B_2257 | k1_xboole_0=A_2258 | k2_zfmisc_1(A_2258, B_2257)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.07/9.92  tff(c_36026, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k2_funct_1('#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_35960, c_36023])).
% 18.07/9.92  tff(c_36037, plain, (k2_funct_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36026])).
% 18.07/9.92  tff(c_35990, plain, (k1_relat_1(k2_funct_1('#skF_4'))!=k1_xboole_0 | k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_35970, c_38])).
% 18.07/9.92  tff(c_36039, plain, (k1_relat_1(k2_funct_1('#skF_4'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36037, c_35990])).
% 18.07/9.92  tff(c_48531, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48461, c_36039])).
% 18.07/9.92  tff(c_49884, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_49857, c_48531])).
% 18.07/9.92  tff(c_49891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36064, c_106, c_100, c_48601, c_49884])).
% 18.07/9.92  tff(c_49892, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_36026])).
% 18.07/9.92  tff(c_49917, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_49892])).
% 18.07/9.92  tff(c_49937, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_49917, c_8])).
% 18.07/9.92  tff(c_49933, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_49917, c_49917, c_14])).
% 18.07/9.92  tff(c_149, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.07/9.92  tff(c_156, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_102, c_149])).
% 18.07/9.92  tff(c_22327, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_156, c_22312])).
% 18.07/9.92  tff(c_22364, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_22327])).
% 18.07/9.92  tff(c_50008, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49933, c_22364])).
% 18.07/9.92  tff(c_50013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49937, c_50008])).
% 18.07/9.92  tff(c_50014, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_49892])).
% 18.07/9.92  tff(c_50054, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_50014, c_8])).
% 18.07/9.92  tff(c_50052, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50014, c_50014, c_12])).
% 18.07/9.92  tff(c_50242, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50052, c_22364])).
% 18.07/9.92  tff(c_50247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50054, c_50242])).
% 18.07/9.92  tff(c_50248, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_22327])).
% 18.07/9.92  tff(c_50251, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50248, c_102])).
% 18.07/9.92  tff(c_51067, plain, (![C_3151, A_3152, B_3153]: (v4_relat_1(C_3151, A_3152) | ~m1_subset_1(C_3151, k1_zfmisc_1(k2_zfmisc_1(A_3152, B_3153))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 18.07/9.92  tff(c_51219, plain, (![C_3172]: (v4_relat_1(C_3172, '#skF_2') | ~m1_subset_1(C_3172, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_50248, c_51067])).
% 18.07/9.92  tff(c_51236, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_50251, c_51219])).
% 18.07/9.92  tff(c_50258, plain, (v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_50248, c_34])).
% 18.07/9.92  tff(c_50269, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50258, c_38])).
% 18.07/9.92  tff(c_50368, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50269])).
% 18.07/9.92  tff(c_50372, plain, (![C_3093, A_3094, B_3095]: (v1_relat_1(C_3093) | ~m1_subset_1(C_3093, k1_zfmisc_1(k2_zfmisc_1(A_3094, B_3095))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.07/9.92  tff(c_50395, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22261, c_50372])).
% 18.07/9.92  tff(c_52009, plain, (![A_3249, B_3250, C_3251]: (k2_relset_1(A_3249, B_3250, C_3251)=k2_relat_1(C_3251) | ~m1_subset_1(C_3251, k1_zfmisc_1(k2_zfmisc_1(A_3249, B_3250))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 18.07/9.92  tff(c_52059, plain, (![C_3256]: (k2_relset_1('#skF_2', '#skF_3', C_3256)=k2_relat_1(C_3256) | ~m1_subset_1(C_3256, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_50248, c_52009])).
% 18.07/9.92  tff(c_52065, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50251, c_52059])).
% 18.07/9.92  tff(c_52076, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_52065])).
% 18.07/9.92  tff(c_51613, plain, (![A_3217]: (k1_relat_1(k2_funct_1(A_3217))=k2_relat_1(A_3217) | ~v2_funct_1(A_3217) | ~v1_funct_1(A_3217) | ~v1_relat_1(A_3217))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.07/9.92  tff(c_59382, plain, (![A_3710]: (v1_funct_2(k2_funct_1(A_3710), k2_relat_1(A_3710), k2_relat_1(k2_funct_1(A_3710))) | ~v1_funct_1(k2_funct_1(A_3710)) | ~v1_relat_1(k2_funct_1(A_3710)) | ~v2_funct_1(A_3710) | ~v1_funct_1(A_3710) | ~v1_relat_1(A_3710))), inference(superposition, [status(thm), theory('equality')], [c_51613, c_80])).
% 18.07/9.92  tff(c_59397, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_52076, c_59382])).
% 18.07/9.92  tff(c_59418, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50258, c_106, c_100, c_50395, c_231, c_59397])).
% 18.07/9.92  tff(c_59430, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_59418])).
% 18.07/9.92  tff(c_59434, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50258, c_106, c_100, c_59430])).
% 18.07/9.92  tff(c_52233, plain, (![A_3263]: (m1_subset_1(A_3263, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_3263), k2_relat_1(A_3263)))) | ~v1_funct_1(A_3263) | ~v1_relat_1(A_3263))), inference(cnfTransformation, [status(thm)], [f_165])).
% 18.07/9.92  tff(c_61777, plain, (![A_3792]: (m1_subset_1(k2_funct_1(A_3792), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_3792), k2_relat_1(k2_funct_1(A_3792))))) | ~v1_funct_1(k2_funct_1(A_3792)) | ~v1_relat_1(k2_funct_1(A_3792)) | ~v2_funct_1(A_3792) | ~v1_funct_1(A_3792) | ~v1_relat_1(A_3792))), inference(superposition, [status(thm), theory('equality')], [c_50, c_52233])).
% 18.07/9.92  tff(c_61829, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_52076, c_61777])).
% 18.07/9.92  tff(c_61870, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_50258, c_106, c_100, c_50395, c_231, c_61829])).
% 18.07/9.92  tff(c_61910, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_61870])).
% 18.07/9.92  tff(c_61931, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50258, c_106, c_100, c_61910])).
% 18.07/9.92  tff(c_52590, plain, (![B_3278, D_3279, A_3280, C_3281]: (k1_xboole_0=B_3278 | v1_funct_2(D_3279, A_3280, C_3281) | ~r1_tarski(B_3278, C_3281) | ~m1_subset_1(D_3279, k1_zfmisc_1(k2_zfmisc_1(A_3280, B_3278))) | ~v1_funct_2(D_3279, A_3280, B_3278) | ~v1_funct_1(D_3279))), inference(cnfTransformation, [status(thm)], [f_184])).
% 18.07/9.92  tff(c_52615, plain, (![B_17, D_3279, A_3280, A_16]: (k1_relat_1(B_17)=k1_xboole_0 | v1_funct_2(D_3279, A_3280, A_16) | ~m1_subset_1(D_3279, k1_zfmisc_1(k2_zfmisc_1(A_3280, k1_relat_1(B_17)))) | ~v1_funct_2(D_3279, A_3280, k1_relat_1(B_17)) | ~v1_funct_1(D_3279) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(resolution, [status(thm)], [c_28, c_52590])).
% 18.07/9.92  tff(c_62628, plain, (![A_16]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_16) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_16) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_61931, c_52615])).
% 18.07/9.92  tff(c_62659, plain, (![A_16]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_16) | ~v4_relat_1('#skF_4', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_50258, c_231, c_59434, c_62628])).
% 18.07/9.92  tff(c_62681, plain, (![A_3804]: (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_3804) | ~v4_relat_1('#skF_4', A_3804))), inference(negUnitSimplification, [status(thm)], [c_50368, c_62659])).
% 18.07/9.92  tff(c_62684, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_62681, c_22260])).
% 18.07/9.92  tff(c_62688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51236, c_62684])).
% 18.07/9.92  tff(c_62689, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_50269])).
% 18.07/9.92  tff(c_50268, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50258, c_36])).
% 18.07/9.92  tff(c_50367, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50268])).
% 18.07/9.92  tff(c_62692, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62689, c_50367])).
% 18.07/9.92  tff(c_62690, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50269])).
% 18.07/9.92  tff(c_62712, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62689, c_62690])).
% 18.07/9.92  tff(c_42, plain, (![A_23]: (k2_relat_1(A_23)=k1_xboole_0 | k1_relat_1(A_23)!=k1_xboole_0 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.07/9.92  tff(c_62958, plain, (![A_3821]: (k2_relat_1(A_3821)='#skF_4' | k1_relat_1(A_3821)!='#skF_4' | ~v1_relat_1(A_3821))), inference(demodulation, [status(thm), theory('equality')], [c_62689, c_62689, c_42])).
% 18.07/9.92  tff(c_62961, plain, (k2_relat_1('#skF_4')='#skF_4' | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_50258, c_62958])).
% 18.07/9.92  tff(c_62973, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62712, c_62961])).
% 18.07/9.92  tff(c_62975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62692, c_62973])).
% 18.07/9.92  tff(c_62976, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_50268])).
% 18.07/9.92  tff(c_22290, plain, (![A_1366, B_1367]: (m1_subset_1('#skF_1'(A_1366, B_1367), k1_zfmisc_1(k2_zfmisc_1(A_1366, B_1367))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 18.07/9.92  tff(c_22301, plain, (![B_1368]: (m1_subset_1('#skF_1'(k1_xboole_0, B_1368), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_22290])).
% 18.07/9.92  tff(c_22305, plain, (![B_1368]: (r1_tarski('#skF_1'(k1_xboole_0, B_1368), k1_xboole_0))), inference(resolution, [status(thm)], [c_22301, c_18])).
% 18.07/9.92  tff(c_22314, plain, (![B_1368]: ('#skF_1'(k1_xboole_0, B_1368)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_1'(k1_xboole_0, B_1368)))), inference(resolution, [status(thm)], [c_22305, c_22312])).
% 18.07/9.92  tff(c_22337, plain, (![B_1373]: ('#skF_1'(k1_xboole_0, B_1373)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_22314])).
% 18.07/9.92  tff(c_74, plain, (![A_46, B_47]: (v1_xboole_0('#skF_1'(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_155])).
% 18.07/9.92  tff(c_22353, plain, (v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22337, c_74])).
% 18.07/9.92  tff(c_62983, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62976, c_22353])).
% 18.07/9.92  tff(c_22325, plain, (![B_1368]: ('#skF_1'(k1_xboole_0, B_1368)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_22314])).
% 18.07/9.92  tff(c_62984, plain, (![B_1368]: ('#skF_1'('#skF_4', B_1368)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62976, c_62976, c_22325])).
% 18.07/9.92  tff(c_76, plain, (![A_46, B_47]: (m1_subset_1('#skF_1'(A_46, B_47), k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 18.07/9.92  tff(c_65333, plain, (![C_4038, A_4039, B_4040]: (v1_partfun1(C_4038, A_4039) | ~m1_subset_1(C_4038, k1_zfmisc_1(k2_zfmisc_1(A_4039, B_4040))) | ~v1_xboole_0(A_4039))), inference(cnfTransformation, [status(thm)], [f_144])).
% 18.07/9.92  tff(c_65367, plain, (![A_4044, B_4045]: (v1_partfun1('#skF_1'(A_4044, B_4045), A_4044) | ~v1_xboole_0(A_4044))), inference(resolution, [status(thm)], [c_76, c_65333])).
% 18.07/9.92  tff(c_65373, plain, (v1_partfun1('#skF_4', '#skF_4') | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_62984, c_65367])).
% 18.07/9.92  tff(c_65375, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62983, c_65373])).
% 18.07/9.92  tff(c_62990, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_62976, c_16])).
% 18.07/9.92  tff(c_65662, plain, (![C_4077, A_4078, B_4079]: (v1_funct_2(C_4077, A_4078, B_4079) | ~v1_partfun1(C_4077, A_4078) | ~v1_funct_1(C_4077) | ~m1_subset_1(C_4077, k1_zfmisc_1(k2_zfmisc_1(A_4078, B_4079))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.07/9.92  tff(c_65675, plain, (![A_4078, B_4079]: (v1_funct_2('#skF_4', A_4078, B_4079) | ~v1_partfun1('#skF_4', A_4078) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62990, c_65662])).
% 18.07/9.92  tff(c_65689, plain, (![A_4080, B_4081]: (v1_funct_2('#skF_4', A_4080, B_4081) | ~v1_partfun1('#skF_4', A_4080))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_65675])).
% 18.07/9.92  tff(c_62987, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62976, c_62976, c_14])).
% 18.07/9.92  tff(c_62977, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50268])).
% 18.07/9.92  tff(c_62997, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62976, c_62977])).
% 18.07/9.92  tff(c_50338, plain, (![A_3091]: (k1_relat_1(A_3091)=k1_xboole_0 | k2_relat_1(A_3091)!=k1_xboole_0 | ~v1_relat_1(A_3091))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.07/9.92  tff(c_50356, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_124, c_50338])).
% 18.07/9.92  tff(c_63626, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62976, c_62997, c_62976, c_62976, c_62976, c_50356])).
% 18.07/9.92  tff(c_64277, plain, (![A_3920]: (v1_funct_2(A_3920, k1_relat_1(A_3920), k2_relat_1(A_3920)) | ~v1_funct_1(A_3920) | ~v1_relat_1(A_3920))), inference(cnfTransformation, [status(thm)], [f_165])).
% 18.07/9.92  tff(c_64280, plain, (v1_funct_2('#skF_4', '#skF_4', k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_63626, c_64277])).
% 18.07/9.92  tff(c_64285, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50258, c_106, c_62997, c_64280])).
% 18.07/9.92  tff(c_64490, plain, (![A_3952, B_3953, C_3954]: (k2_relset_1(A_3952, B_3953, C_3954)=k2_relat_1(C_3954) | ~m1_subset_1(C_3954, k1_zfmisc_1(k2_zfmisc_1(A_3952, B_3953))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 18.07/9.92  tff(c_64500, plain, (![A_3952, B_3953]: (k2_relset_1(A_3952, B_3953, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_62990, c_64490])).
% 18.07/9.92  tff(c_64509, plain, (![A_3952, B_3953]: (k2_relset_1(A_3952, B_3953, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62997, c_64500])).
% 18.07/9.92  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.07/9.92  tff(c_63546, plain, (![B_3850, A_3851]: (B_3850='#skF_4' | A_3851='#skF_4' | k2_zfmisc_1(A_3851, B_3850)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62976, c_62976, c_62976, c_10])).
% 18.07/9.92  tff(c_63563, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_50248, c_63546])).
% 18.07/9.92  tff(c_63565, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_63563])).
% 18.07/9.92  tff(c_63570, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63565, c_98])).
% 18.07/9.92  tff(c_64512, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64509, c_63570])).
% 18.07/9.92  tff(c_62989, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62976, c_62976, c_12])).
% 18.07/9.92  tff(c_62991, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_62976, c_8])).
% 18.07/9.92  tff(c_63179, plain, (![B_3832, A_3833]: (B_3832='#skF_4' | A_3833='#skF_4' | k2_zfmisc_1(A_3833, B_3832)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62976, c_62976, c_62976, c_10])).
% 18.07/9.92  tff(c_63193, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_50248, c_63179])).
% 18.07/9.92  tff(c_63194, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_63193])).
% 18.07/9.92  tff(c_63002, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_22326])).
% 18.07/9.92  tff(c_63272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62991, c_62989, c_63194, c_63002])).
% 18.07/9.92  tff(c_63273, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_63193])).
% 18.07/9.92  tff(c_63352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62991, c_62987, c_63273, c_63002])).
% 18.07/9.92  tff(c_63353, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_22326])).
% 18.07/9.92  tff(c_63567, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63565, c_63353])).
% 18.07/9.92  tff(c_63573, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62989, c_63567])).
% 18.07/9.92  tff(c_63569, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63565, c_22260])).
% 18.07/9.92  tff(c_63601, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63573, c_63569])).
% 18.07/9.92  tff(c_64520, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64512, c_63601])).
% 18.07/9.92  tff(c_64524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64285, c_64520])).
% 18.07/9.92  tff(c_64525, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_63563])).
% 18.07/9.92  tff(c_64528, plain, (k2_zfmisc_1('#skF_4', '#skF_2')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64525, c_63353])).
% 18.07/9.92  tff(c_64534, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62987, c_64528])).
% 18.07/9.92  tff(c_64530, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64525, c_22260])).
% 18.07/9.92  tff(c_64583, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64534, c_64530])).
% 18.07/9.92  tff(c_65692, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_65689, c_64583])).
% 18.07/9.92  tff(c_65696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65375, c_65692])).
% 18.07/9.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.07/9.92  
% 18.07/9.92  Inference rules
% 18.07/9.92  ----------------------
% 18.07/9.92  #Ref     : 0
% 18.07/9.92  #Sup     : 13484
% 18.07/9.92  #Fact    : 0
% 18.07/9.92  #Define  : 0
% 18.07/9.92  #Split   : 154
% 18.07/9.92  #Chain   : 0
% 18.07/9.92  #Close   : 0
% 18.07/9.92  
% 18.07/9.92  Ordering : KBO
% 18.07/9.92  
% 18.07/9.92  Simplification rules
% 18.07/9.92  ----------------------
% 18.07/9.92  #Subsume      : 2562
% 18.07/9.92  #Demod        : 18279
% 18.07/9.92  #Tautology    : 5050
% 18.07/9.92  #SimpNegUnit  : 522
% 18.07/9.92  #BackRed      : 655
% 18.07/9.92  
% 18.07/9.92  #Partial instantiations: 0
% 18.07/9.92  #Strategies tried      : 1
% 18.07/9.92  
% 18.07/9.92  Timing (in seconds)
% 18.07/9.92  ----------------------
% 18.07/9.92  Preprocessing        : 0.37
% 18.07/9.92  Parsing              : 0.20
% 18.07/9.92  CNF conversion       : 0.02
% 18.07/9.92  Main loop            : 8.63
% 18.07/9.92  Inferencing          : 2.15
% 18.07/9.92  Reduction            : 3.74
% 18.07/9.92  Demodulation         : 2.85
% 18.07/9.92  BG Simplification    : 0.15
% 18.07/9.92  Subsumption          : 2.06
% 18.07/9.92  Abstraction          : 0.21
% 18.07/9.92  MUC search           : 0.00
% 18.07/9.92  Cooper               : 0.00
% 18.07/9.92  Total                : 9.13
% 18.07/9.92  Index Insertion      : 0.00
% 18.07/9.92  Index Deletion       : 0.00
% 18.07/9.92  Index Matching       : 0.00
% 18.07/9.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
