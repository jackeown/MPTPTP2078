%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:30 EST 2020

% Result     : Theorem 16.08s
% Output     : CNFRefutation 16.37s
% Verified   : 
% Statistics : Number of formulae       :  343 (26098 expanded)
%              Number of leaves         :   48 (8013 expanded)
%              Depth                    :   23
%              Number of atoms          :  675 (65396 expanded)
%              Number of equality atoms :  159 (18670 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_1 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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

tff(f_219,negated_conjecture,(
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

tff(f_134,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_183,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_202,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_89,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_110,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_173,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_162,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_155,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_1589,plain,(
    ! [C_210,A_211,B_212] :
      ( v4_relat_1(C_210,A_211)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1613,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_1589])).

tff(c_1315,plain,(
    ! [C_187,A_188,B_189] :
      ( v1_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1337,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_1315])).

tff(c_38,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1354,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1337,c_38])).

tff(c_1356,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1354])).

tff(c_118,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_48,plain,(
    ! [A_26] :
      ( v1_funct_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_108,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_214,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_217,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_214])).

tff(c_220,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_217])).

tff(c_384,plain,(
    ! [C_95,A_96,B_97] :
      ( v1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_394,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_384])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_394])).

tff(c_411,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_112,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_60,plain,(
    ! [A_28] :
      ( k2_relat_1(k2_funct_1(A_28)) = k1_relat_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_50,plain,(
    ! [A_26] :
      ( v1_relat_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_110,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_2416,plain,(
    ! [A_294,B_295,C_296] :
      ( k2_relset_1(A_294,B_295,C_296) = k2_relat_1(C_296)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2429,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_2416])).

tff(c_2444,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2429])).

tff(c_2089,plain,(
    ! [A_263] :
      ( k1_relat_1(k2_funct_1(A_263)) = k2_relat_1(A_263)
      | ~ v2_funct_1(A_263)
      | ~ v1_funct_1(A_263)
      | ~ v1_relat_1(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_92,plain,(
    ! [A_52] :
      ( v1_funct_2(A_52,k1_relat_1(A_52),k2_relat_1(A_52))
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_10476,plain,(
    ! [A_778] :
      ( v1_funct_2(k2_funct_1(A_778),k2_relat_1(A_778),k2_relat_1(k2_funct_1(A_778)))
      | ~ v1_funct_1(k2_funct_1(A_778))
      | ~ v1_relat_1(k2_funct_1(A_778))
      | ~ v2_funct_1(A_778)
      | ~ v1_funct_1(A_778)
      | ~ v1_relat_1(A_778) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2089,c_92])).

tff(c_10500,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2444,c_10476])).

tff(c_10524,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_118,c_112,c_411,c_10500])).

tff(c_10529,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_10524])).

tff(c_10532,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_10529])).

tff(c_10536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_118,c_10532])).

tff(c_10537,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_10524])).

tff(c_10561,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_10537])).

tff(c_10565,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_118,c_112,c_10561])).

tff(c_10538,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_10524])).

tff(c_62,plain,(
    ! [A_28] :
      ( k1_relat_1(k2_funct_1(A_28)) = k2_relat_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2270,plain,(
    ! [A_281] :
      ( m1_subset_1(A_281,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_281),k2_relat_1(A_281))))
      | ~ v1_funct_1(A_281)
      | ~ v1_relat_1(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_11317,plain,(
    ! [A_817] :
      ( m1_subset_1(k2_funct_1(A_817),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_817),k2_relat_1(k2_funct_1(A_817)))))
      | ~ v1_funct_1(k2_funct_1(A_817))
      | ~ v1_relat_1(k2_funct_1(A_817))
      | ~ v2_funct_1(A_817)
      | ~ v1_funct_1(A_817)
      | ~ v1_relat_1(A_817) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2270])).

tff(c_11372,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2444,c_11317])).

tff(c_11413,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_118,c_112,c_10538,c_411,c_11372])).

tff(c_11454,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_11413])).

tff(c_11476,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_118,c_112,c_11454])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3059,plain,(
    ! [B_337,D_338,A_339,C_340] :
      ( k1_xboole_0 = B_337
      | m1_subset_1(D_338,k1_zfmisc_1(k2_zfmisc_1(A_339,C_340)))
      | ~ r1_tarski(B_337,C_340)
      | ~ m1_subset_1(D_338,k1_zfmisc_1(k2_zfmisc_1(A_339,B_337)))
      | ~ v1_funct_2(D_338,A_339,B_337)
      | ~ v1_funct_1(D_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_12184,plain,(
    ! [B_830,D_831,A_832,A_833] :
      ( k1_relat_1(B_830) = k1_xboole_0
      | m1_subset_1(D_831,k1_zfmisc_1(k2_zfmisc_1(A_832,A_833)))
      | ~ m1_subset_1(D_831,k1_zfmisc_1(k2_zfmisc_1(A_832,k1_relat_1(B_830))))
      | ~ v1_funct_2(D_831,A_832,k1_relat_1(B_830))
      | ~ v1_funct_1(D_831)
      | ~ v4_relat_1(B_830,A_833)
      | ~ v1_relat_1(B_830) ) ),
    inference(resolution,[status(thm)],[c_26,c_3059])).

tff(c_12186,plain,(
    ! [A_833] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_833)))
      | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v4_relat_1('#skF_5',A_833)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_11476,c_12184])).

tff(c_12207,plain,(
    ! [A_833] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_833)))
      | ~ v4_relat_1('#skF_5',A_833) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_411,c_10565,c_12186])).

tff(c_12631,plain,(
    ! [A_839] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_839)))
      | ~ v4_relat_1('#skF_5',A_839) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1356,c_12207])).

tff(c_410,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_413,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_12686,plain,(
    ~ v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_12631,c_413])).

tff(c_12737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_12686])).

tff(c_12738,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1354])).

tff(c_44,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_127,plain,(
    ! [A_58] : v1_relat_1(k6_relat_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_129,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_127])).

tff(c_454,plain,(
    ! [A_106] :
      ( k2_relat_1(A_106) = k1_xboole_0
      | k1_relat_1(A_106) != k1_xboole_0
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_472,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_129,c_454])).

tff(c_477,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_618,plain,(
    ! [A_117] :
      ( k1_relat_1(A_117) = k1_xboole_0
      | k2_relat_1(A_117) != k1_xboole_0
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_627,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_129,c_618])).

tff(c_638,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_477,c_627])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_837,plain,(
    ! [C_145,B_146,A_147] :
      ( v5_relat_1(C_145,B_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_939,plain,(
    ! [A_157,B_158,A_159] :
      ( v5_relat_1(A_157,B_158)
      | ~ r1_tarski(A_157,k2_zfmisc_1(A_159,B_158)) ) ),
    inference(resolution,[status(thm)],[c_18,c_837])).

tff(c_971,plain,(
    ! [A_159,B_158] : v5_relat_1(k2_zfmisc_1(A_159,B_158),B_158) ),
    inference(resolution,[status(thm)],[c_6,c_939])).

tff(c_981,plain,(
    ! [B_162,A_163] :
      ( r1_tarski(k2_relat_1(B_162),A_163)
      | ~ v5_relat_1(B_162,A_163)
      | ~ v1_relat_1(B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_414,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(A_98,B_99)
      | ~ m1_subset_1(A_98,k1_zfmisc_1(B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_426,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_414])).

tff(c_488,plain,(
    ! [B_110,A_111] :
      ( B_110 = A_111
      | ~ r1_tarski(B_110,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_506,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_426,c_488])).

tff(c_1099,plain,(
    ! [B_174] :
      ( k2_relat_1(B_174) = k1_xboole_0
      | ~ v5_relat_1(B_174,k1_xboole_0)
      | ~ v1_relat_1(B_174) ) ),
    inference(resolution,[status(thm)],[c_981,c_506])).

tff(c_1107,plain,(
    ! [A_159] :
      ( k2_relat_1(k2_zfmisc_1(A_159,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_159,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_971,c_1099])).

tff(c_1125,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_10,c_10,c_1107])).

tff(c_1127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_638,c_1125])).

tff(c_1128,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_12749,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12738,c_12738,c_1128])).

tff(c_12757,plain,(
    ! [A_5] : m1_subset_1('#skF_5',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12738,c_14])).

tff(c_13937,plain,(
    ! [A_946,B_947,C_948] :
      ( k2_relset_1(A_946,B_947,C_948) = k2_relat_1(C_948)
      | ~ m1_subset_1(C_948,k1_zfmisc_1(k2_zfmisc_1(A_946,B_947))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_13950,plain,(
    ! [A_946,B_947] : k2_relset_1(A_946,B_947,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12757,c_13937])).

tff(c_13963,plain,(
    ! [A_949,B_950] : k2_relset_1(A_949,B_950,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12749,c_13950])).

tff(c_13967,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_13963,c_110])).

tff(c_12756,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12738,c_12738,c_10])).

tff(c_14011,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13967,c_13967,c_12756])).

tff(c_425,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_114,c_414])).

tff(c_1134,plain,(
    ! [B_175,A_176] :
      ( B_175 = A_176
      | ~ r1_tarski(B_175,A_176)
      | ~ r1_tarski(A_176,B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1151,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_425,c_1134])).

tff(c_1303,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1151])).

tff(c_14024,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13967,c_1303])).

tff(c_14512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14011,c_14024])).

tff(c_14513,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1151])).

tff(c_14516,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14513,c_114])).

tff(c_14983,plain,(
    ! [C_1007,A_1008,B_1009] :
      ( v4_relat_1(C_1007,A_1008)
      | ~ m1_subset_1(C_1007,k1_zfmisc_1(k2_zfmisc_1(A_1008,B_1009))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_15025,plain,(
    ! [C_1014] :
      ( v4_relat_1(C_1014,'#skF_3')
      | ~ m1_subset_1(C_1014,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14513,c_14983])).

tff(c_15042,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_14516,c_15025])).

tff(c_14542,plain,(
    ! [C_975,A_976,B_977] :
      ( v1_relat_1(C_975)
      | ~ m1_subset_1(C_975,k1_zfmisc_1(k2_zfmisc_1(A_976,B_977))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_14590,plain,(
    ! [C_980] :
      ( v1_relat_1(C_980)
      | ~ m1_subset_1(C_980,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14513,c_14542])).

tff(c_14607,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14516,c_14590])).

tff(c_14625,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14607,c_38])).

tff(c_14645,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14625])).

tff(c_16691,plain,(
    ! [A_1148,B_1149,C_1150] :
      ( k2_relset_1(A_1148,B_1149,C_1150) = k2_relat_1(C_1150)
      | ~ m1_subset_1(C_1150,k1_zfmisc_1(k2_zfmisc_1(A_1148,B_1149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_16754,plain,(
    ! [C_1157] :
      ( k2_relset_1('#skF_3','#skF_4',C_1157) = k2_relat_1(C_1157)
      | ~ m1_subset_1(C_1157,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14513,c_16691])).

tff(c_16760,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14516,c_16754])).

tff(c_16772,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_16760])).

tff(c_15747,plain,(
    ! [A_1096] :
      ( k1_relat_1(k2_funct_1(A_1096)) = k2_relat_1(A_1096)
      | ~ v2_funct_1(A_1096)
      | ~ v1_funct_1(A_1096)
      | ~ v1_relat_1(A_1096) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_24064,plain,(
    ! [A_1569] :
      ( v1_funct_2(k2_funct_1(A_1569),k2_relat_1(A_1569),k2_relat_1(k2_funct_1(A_1569)))
      | ~ v1_funct_1(k2_funct_1(A_1569))
      | ~ v1_relat_1(k2_funct_1(A_1569))
      | ~ v2_funct_1(A_1569)
      | ~ v1_funct_1(A_1569)
      | ~ v1_relat_1(A_1569) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15747,c_92])).

tff(c_24091,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16772,c_24064])).

tff(c_24126,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14607,c_118,c_112,c_411,c_24091])).

tff(c_24144,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_24126])).

tff(c_24147,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_24144])).

tff(c_24151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14607,c_118,c_24147])).

tff(c_24152,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_24126])).

tff(c_24198,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_24152])).

tff(c_24202,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14607,c_118,c_112,c_24198])).

tff(c_24153,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_24126])).

tff(c_16366,plain,(
    ! [A_1137] :
      ( m1_subset_1(A_1137,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1137),k2_relat_1(A_1137))))
      | ~ v1_funct_1(A_1137)
      | ~ v1_relat_1(A_1137) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_24879,plain,(
    ! [A_1619] :
      ( m1_subset_1(k2_funct_1(A_1619),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1619),k2_relat_1(k2_funct_1(A_1619)))))
      | ~ v1_funct_1(k2_funct_1(A_1619))
      | ~ v1_relat_1(k2_funct_1(A_1619))
      | ~ v2_funct_1(A_1619)
      | ~ v1_funct_1(A_1619)
      | ~ v1_relat_1(A_1619) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_16366])).

tff(c_24937,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16772,c_24879])).

tff(c_24989,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14607,c_118,c_112,c_24153,c_411,c_24937])).

tff(c_25049,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_24989])).

tff(c_25071,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14607,c_118,c_112,c_25049])).

tff(c_17286,plain,(
    ! [B_1186,D_1187,A_1188,C_1189] :
      ( k1_xboole_0 = B_1186
      | m1_subset_1(D_1187,k1_zfmisc_1(k2_zfmisc_1(A_1188,C_1189)))
      | ~ r1_tarski(B_1186,C_1189)
      | ~ m1_subset_1(D_1187,k1_zfmisc_1(k2_zfmisc_1(A_1188,B_1186)))
      | ~ v1_funct_2(D_1187,A_1188,B_1186)
      | ~ v1_funct_1(D_1187) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_25994,plain,(
    ! [B_1641,D_1642,A_1643,A_1644] :
      ( k1_relat_1(B_1641) = k1_xboole_0
      | m1_subset_1(D_1642,k1_zfmisc_1(k2_zfmisc_1(A_1643,A_1644)))
      | ~ m1_subset_1(D_1642,k1_zfmisc_1(k2_zfmisc_1(A_1643,k1_relat_1(B_1641))))
      | ~ v1_funct_2(D_1642,A_1643,k1_relat_1(B_1641))
      | ~ v1_funct_1(D_1642)
      | ~ v4_relat_1(B_1641,A_1644)
      | ~ v1_relat_1(B_1641) ) ),
    inference(resolution,[status(thm)],[c_26,c_17286])).

tff(c_25996,plain,(
    ! [A_1644] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_1644)))
      | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v4_relat_1('#skF_5',A_1644)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_25071,c_25994])).

tff(c_26017,plain,(
    ! [A_1644] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_1644)))
      | ~ v4_relat_1('#skF_5',A_1644) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14607,c_411,c_24202,c_25996])).

tff(c_26099,plain,(
    ! [A_1646] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_1646)))
      | ~ v4_relat_1('#skF_5',A_1646) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14645,c_26017])).

tff(c_26142,plain,(
    ~ v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_26099,c_413])).

tff(c_26184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15042,c_26142])).

tff(c_26185,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_14625])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26229,plain,(
    ! [B_1647,A_1648] :
      ( B_1647 = '#skF_5'
      | A_1648 = '#skF_5'
      | k2_zfmisc_1(A_1648,B_1647) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26185,c_26185,c_26185,c_8])).

tff(c_26233,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_14513,c_26229])).

tff(c_26405,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_26233])).

tff(c_26197,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26185,c_26185,c_1128])).

tff(c_26418,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26405,c_26405,c_26197])).

tff(c_26205,plain,(
    ! [A_5] : m1_subset_1('#skF_5',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26185,c_14])).

tff(c_26406,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26405,c_26205])).

tff(c_27780,plain,(
    ! [A_1788,B_1789,C_1790] :
      ( k2_relset_1(A_1788,B_1789,C_1790) = k2_relat_1(C_1790)
      | ~ m1_subset_1(C_1790,k1_zfmisc_1(k2_zfmisc_1(A_1788,B_1789))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_27790,plain,(
    ! [A_1788,B_1789] : k2_relset_1(A_1788,B_1789,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26406,c_27780])).

tff(c_27802,plain,(
    ! [A_1791,B_1792] : k2_relset_1(A_1791,B_1792,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26418,c_27790])).

tff(c_26431,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26405,c_110])).

tff(c_27806,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_27802,c_26431])).

tff(c_27861,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27806,c_26406])).

tff(c_26423,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26405,c_14607])).

tff(c_27873,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27806,c_26423])).

tff(c_26434,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26405,c_118])).

tff(c_27876,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27806,c_26434])).

tff(c_26433,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26405,c_112])).

tff(c_27877,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27806,c_26433])).

tff(c_26186,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14625])).

tff(c_26218,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26185,c_26186])).

tff(c_26419,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26405,c_26405,c_26218])).

tff(c_27870,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27806,c_27806,c_26419])).

tff(c_26430,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26405,c_411])).

tff(c_27872,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27806,c_26430])).

tff(c_27553,plain,(
    ! [A_1759] :
      ( k2_relat_1(k2_funct_1(A_1759)) = k1_relat_1(A_1759)
      | ~ v2_funct_1(A_1759)
      | ~ v1_funct_1(A_1759)
      | ~ v1_relat_1(A_1759) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_33066,plain,(
    ! [A_2140] :
      ( v1_funct_2(k2_funct_1(A_2140),k1_relat_1(k2_funct_1(A_2140)),k1_relat_1(A_2140))
      | ~ v1_funct_1(k2_funct_1(A_2140))
      | ~ v1_relat_1(k2_funct_1(A_2140))
      | ~ v2_funct_1(A_2140)
      | ~ v1_funct_1(A_2140)
      | ~ v1_relat_1(A_2140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27553,c_92])).

tff(c_33069,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_27870,c_33066])).

tff(c_33077,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27873,c_27876,c_27877,c_27872,c_33069])).

tff(c_33078,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_33077])).

tff(c_33081,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_33078])).

tff(c_33085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27873,c_27876,c_33081])).

tff(c_33087,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_33077])).

tff(c_36,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26203,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != '#skF_5'
      | A_21 = '#skF_5'
      | ~ v1_relat_1(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26185,c_26185,c_36])).

tff(c_26953,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != '#skF_3'
      | A_21 = '#skF_3'
      | ~ v1_relat_1(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26405,c_26405,c_26203])).

tff(c_27846,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != '#skF_4'
      | A_21 = '#skF_4'
      | ~ v1_relat_1(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27806,c_27806,c_26953])).

tff(c_33103,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_33087,c_27846])).

tff(c_33109,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_33103])).

tff(c_33115,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_33109])).

tff(c_33121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27873,c_27876,c_27877,c_27870,c_33115])).

tff(c_33122,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_33103])).

tff(c_26204,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26185,c_26185,c_10])).

tff(c_26408,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26405,c_26405,c_26204])).

tff(c_26429,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26405,c_413])).

tff(c_26741,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26408,c_26429])).

tff(c_27854,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27806,c_27806,c_26741])).

tff(c_33127,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33122,c_27854])).

tff(c_33135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27861,c_33127])).

tff(c_33136,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26233])).

tff(c_33138,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33136,c_26205])).

tff(c_33155,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33136,c_14607])).

tff(c_33166,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33136,c_118])).

tff(c_33165,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33136,c_112])).

tff(c_33151,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33136,c_33136,c_26218])).

tff(c_33162,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33136,c_411])).

tff(c_34043,plain,(
    ! [A_2220] :
      ( k2_relat_1(k2_funct_1(A_2220)) = k1_relat_1(A_2220)
      | ~ v2_funct_1(A_2220)
      | ~ v1_funct_1(A_2220)
      | ~ v1_relat_1(A_2220) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_41530,plain,(
    ! [A_2704] :
      ( v1_funct_2(k2_funct_1(A_2704),k1_relat_1(k2_funct_1(A_2704)),k1_relat_1(A_2704))
      | ~ v1_funct_1(k2_funct_1(A_2704))
      | ~ v1_relat_1(k2_funct_1(A_2704))
      | ~ v2_funct_1(A_2704)
      | ~ v1_funct_1(A_2704)
      | ~ v1_relat_1(A_2704) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34043,c_92])).

tff(c_41545,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_33151,c_41530])).

tff(c_41547,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33155,c_33166,c_33165,c_33162,c_41545])).

tff(c_41572,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_41547])).

tff(c_41575,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_41572])).

tff(c_41579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33155,c_33166,c_41575])).

tff(c_41581,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_41547])).

tff(c_33660,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != '#skF_4'
      | A_21 = '#skF_4'
      | ~ v1_relat_1(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33136,c_33136,c_26203])).

tff(c_41596,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_41581,c_33660])).

tff(c_41603,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_41596])).

tff(c_41609,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_41603])).

tff(c_41615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33155,c_33166,c_33165,c_33151,c_41609])).

tff(c_41616,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_41596])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26206,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_5',B_4) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26185,c_26185,c_12])).

tff(c_33142,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33136,c_33136,c_26206])).

tff(c_33161,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33136,c_413])).

tff(c_33491,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33142,c_33161])).

tff(c_41621,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41616,c_33491])).

tff(c_41629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33138,c_41621])).

tff(c_41630,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_41694,plain,(
    ! [C_2721,A_2722,B_2723] :
      ( v1_relat_1(C_2721)
      | ~ m1_subset_1(C_2721,k1_zfmisc_1(k2_zfmisc_1(A_2722,B_2723))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_41720,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_41694])).

tff(c_41631,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_41718,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_41631,c_41694])).

tff(c_43697,plain,(
    ! [A_2895,B_2896,C_2897] :
      ( k2_relset_1(A_2895,B_2896,C_2897) = k2_relat_1(C_2897)
      | ~ m1_subset_1(C_2897,k1_zfmisc_1(k2_zfmisc_1(A_2895,B_2896))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_43713,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_43697])).

tff(c_43729,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_43713])).

tff(c_43325,plain,(
    ! [A_2862] :
      ( k1_relat_1(k2_funct_1(A_2862)) = k2_relat_1(A_2862)
      | ~ v2_funct_1(A_2862)
      | ~ v1_funct_1(A_2862)
      | ~ v1_relat_1(A_2862) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_52014,plain,(
    ! [A_3377] :
      ( v1_funct_2(k2_funct_1(A_3377),k2_relat_1(A_3377),k2_relat_1(k2_funct_1(A_3377)))
      | ~ v1_funct_1(k2_funct_1(A_3377))
      | ~ v1_relat_1(k2_funct_1(A_3377))
      | ~ v2_funct_1(A_3377)
      | ~ v1_funct_1(A_3377)
      | ~ v1_relat_1(A_3377) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43325,c_92])).

tff(c_52035,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_43729,c_52014])).

tff(c_52060,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41720,c_118,c_112,c_41718,c_411,c_52035])).

tff(c_52072,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_52060])).

tff(c_52076,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41720,c_118,c_112,c_52072])).

tff(c_43601,plain,(
    ! [A_2887] :
      ( m1_subset_1(A_2887,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2887),k2_relat_1(A_2887))))
      | ~ v1_funct_1(A_2887)
      | ~ v1_relat_1(A_2887) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_52484,plain,(
    ! [A_3391] :
      ( m1_subset_1(k2_funct_1(A_3391),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_3391),k2_relat_1(k2_funct_1(A_3391)))))
      | ~ v1_funct_1(k2_funct_1(A_3391))
      | ~ v1_relat_1(k2_funct_1(A_3391))
      | ~ v2_funct_1(A_3391)
      | ~ v1_funct_1(A_3391)
      | ~ v1_relat_1(A_3391) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_43601])).

tff(c_52542,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_43729,c_52484])).

tff(c_52588,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41720,c_118,c_112,c_41718,c_411,c_52542])).

tff(c_52637,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_52588])).

tff(c_52661,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41720,c_118,c_112,c_52637])).

tff(c_41729,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_41720,c_38])).

tff(c_41739,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_41729])).

tff(c_42908,plain,(
    ! [C_2819,B_2820,A_2821] :
      ( v5_relat_1(C_2819,B_2820)
      | ~ m1_subset_1(C_2819,k1_zfmisc_1(k2_zfmisc_1(A_2821,B_2820))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42934,plain,(
    v5_relat_1(k2_funct_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_41631,c_42908])).

tff(c_43442,plain,(
    ! [A_2869] :
      ( k2_relat_1(k2_funct_1(A_2869)) = k1_relat_1(A_2869)
      | ~ v2_funct_1(A_2869)
      | ~ v1_funct_1(A_2869)
      | ~ v1_relat_1(A_2869) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50691,plain,(
    ! [A_3286,A_3287] :
      ( r1_tarski(k1_relat_1(A_3286),A_3287)
      | ~ v5_relat_1(k2_funct_1(A_3286),A_3287)
      | ~ v1_relat_1(k2_funct_1(A_3286))
      | ~ v2_funct_1(A_3286)
      | ~ v1_funct_1(A_3286)
      | ~ v1_relat_1(A_3286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43442,c_30])).

tff(c_50724,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42934,c_50691])).

tff(c_50741,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41720,c_118,c_112,c_41718,c_50724])).

tff(c_102,plain,(
    ! [B_54,D_56,A_53,C_55] :
      ( k1_xboole_0 = B_54
      | v1_funct_2(D_56,A_53,C_55)
      | ~ r1_tarski(B_54,C_55)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(D_56,A_53,B_54)
      | ~ v1_funct_1(D_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_50750,plain,(
    ! [D_56,A_53] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | v1_funct_2(D_56,A_53,'#skF_3')
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_53,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_56,A_53,k1_relat_1('#skF_5'))
      | ~ v1_funct_1(D_56) ) ),
    inference(resolution,[status(thm)],[c_50741,c_102])).

tff(c_50768,plain,(
    ! [D_56,A_53] :
      ( v1_funct_2(D_56,A_53,'#skF_3')
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_53,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_56,A_53,k1_relat_1('#skF_5'))
      | ~ v1_funct_1(D_56) ) ),
    inference(negUnitSimplification,[status(thm)],[c_41739,c_50750])).

tff(c_53044,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52661,c_50768])).

tff(c_53082,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_52076,c_53044])).

tff(c_53084,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41630,c_53082])).

tff(c_53085,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_41729])).

tff(c_53086,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_41729])).

tff(c_53139,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53085,c_53086])).

tff(c_42,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) = k1_xboole_0
      | k1_relat_1(A_22) != k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_53114,plain,(
    ! [A_3396] :
      ( k2_relat_1(A_3396) = '#skF_5'
      | k1_relat_1(A_3396) != '#skF_5'
      | ~ v1_relat_1(A_3396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53085,c_53085,c_42])).

tff(c_53134,plain,
    ( k2_relat_1('#skF_5') = '#skF_5'
    | k1_relat_1('#skF_5') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_41720,c_53114])).

tff(c_53224,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53139,c_53134])).

tff(c_53100,plain,(
    ! [A_5] : m1_subset_1('#skF_5',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53085,c_14])).

tff(c_55340,plain,(
    ! [A_3612,B_3613,C_3614] :
      ( k2_relset_1(A_3612,B_3613,C_3614) = k2_relat_1(C_3614)
      | ~ m1_subset_1(C_3614,k1_zfmisc_1(k2_zfmisc_1(A_3612,B_3613))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_55347,plain,(
    ! [A_3612,B_3613] : k2_relset_1(A_3612,B_3613,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_53100,c_55340])).

tff(c_55366,plain,(
    ! [A_3615,B_3616] : k2_relset_1(A_3615,B_3616,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53224,c_55347])).

tff(c_55370,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_55366,c_110])).

tff(c_41632,plain,(
    ! [A_2708,B_2709] :
      ( r1_tarski(A_2708,B_2709)
      | ~ m1_subset_1(A_2708,k1_zfmisc_1(B_2709)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_41648,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_41632])).

tff(c_53094,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53085,c_41648])).

tff(c_41660,plain,(
    ! [A_2713,B_2714] : m1_subset_1('#skF_2'(A_2713,B_2714),k1_zfmisc_1(k2_zfmisc_1(A_2713,B_2714))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_41688,plain,(
    ! [B_2719] : m1_subset_1('#skF_2'(k1_xboole_0,B_2719),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_41660])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_41692,plain,(
    ! [B_2719] : r1_tarski('#skF_2'(k1_xboole_0,B_2719),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_41688,c_16])).

tff(c_53217,plain,(
    ! [B_3405] : r1_tarski('#skF_2'('#skF_5',B_3405),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53085,c_53085,c_41692])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53219,plain,(
    ! [B_3405] :
      ( '#skF_2'('#skF_5',B_3405) = '#skF_5'
      | ~ r1_tarski('#skF_5','#skF_2'('#skF_5',B_3405)) ) ),
    inference(resolution,[status(thm)],[c_53217,c_2])).

tff(c_53231,plain,(
    ! [B_3406] : '#skF_2'('#skF_5',B_3406) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53094,c_53219])).

tff(c_86,plain,(
    ! [A_49,B_50] : v1_xboole_0('#skF_2'(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_53246,plain,(
    v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_53231,c_86])).

tff(c_53222,plain,(
    ! [B_3405] : '#skF_2'('#skF_5',B_3405) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53094,c_53219])).

tff(c_88,plain,(
    ! [A_49,B_50] : m1_subset_1('#skF_2'(A_49,B_50),k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_55051,plain,(
    ! [C_3579,A_3580,B_3581] :
      ( v1_partfun1(C_3579,A_3580)
      | ~ m1_subset_1(C_3579,k1_zfmisc_1(k2_zfmisc_1(A_3580,B_3581)))
      | ~ v1_xboole_0(A_3580) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_55075,plain,(
    ! [A_3583,B_3584] :
      ( v1_partfun1('#skF_2'(A_3583,B_3584),A_3583)
      | ~ v1_xboole_0(A_3583) ) ),
    inference(resolution,[status(thm)],[c_88,c_55051])).

tff(c_55081,plain,
    ( v1_partfun1('#skF_5','#skF_5')
    | ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_53222,c_55075])).

tff(c_55083,plain,(
    v1_partfun1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53246,c_55081])).

tff(c_55386,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55370,c_55370,c_55083])).

tff(c_55438,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55370,c_118])).

tff(c_55617,plain,(
    ! [A_3626] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3626)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55370,c_53100])).

tff(c_74,plain,(
    ! [C_44,A_42,B_43] :
      ( v1_funct_2(C_44,A_42,B_43)
      | ~ v1_partfun1(C_44,A_42)
      | ~ v1_funct_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_55621,plain,(
    ! [A_42,B_43] :
      ( v1_funct_2('#skF_4',A_42,B_43)
      | ~ v1_partfun1('#skF_4',A_42)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_55617,c_74])).

tff(c_56233,plain,(
    ! [A_3674,B_3675] :
      ( v1_funct_2('#skF_4',A_3674,B_3675)
      | ~ v1_partfun1('#skF_4',A_3674) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55438,c_55621])).

tff(c_54207,plain,(
    ! [A_3497] :
      ( k2_relat_1(k2_funct_1(A_3497)) = k1_relat_1(A_3497)
      | ~ v2_funct_1(A_3497)
      | ~ v1_funct_1(A_3497)
      | ~ v1_relat_1(A_3497) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_41738,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0
    | k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41718,c_36])).

tff(c_53369,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53085,c_53085,c_41738])).

tff(c_53370,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_53369])).

tff(c_54231,plain,
    ( k1_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_54207,c_53370])).

tff(c_54238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41720,c_118,c_112,c_53139,c_54231])).

tff(c_54239,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_53369])).

tff(c_54244,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54239,c_41630])).

tff(c_55412,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55370,c_54244])).

tff(c_56236,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_56233,c_55412])).

tff(c_56240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55386,c_56236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 13:14:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.08/8.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.08/8.23  
% 16.08/8.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.08/8.23  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_1 > #skF_4 > #skF_2
% 16.08/8.23  
% 16.08/8.23  %Foreground sorts:
% 16.08/8.23  
% 16.08/8.23  
% 16.08/8.23  %Background operators:
% 16.08/8.23  
% 16.08/8.23  
% 16.08/8.23  %Foreground operators:
% 16.08/8.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 16.08/8.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.08/8.23  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 16.08/8.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 16.08/8.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.08/8.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.08/8.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.08/8.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.08/8.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.08/8.23  tff('#skF_5', type, '#skF_5': $i).
% 16.08/8.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.08/8.23  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 16.08/8.23  tff('#skF_3', type, '#skF_3': $i).
% 16.08/8.23  tff('#skF_1', type, '#skF_1': $i).
% 16.08/8.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 16.08/8.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.08/8.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.08/8.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.08/8.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.08/8.23  tff('#skF_4', type, '#skF_4': $i).
% 16.08/8.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 16.08/8.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.08/8.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.08/8.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 16.08/8.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.08/8.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.08/8.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.08/8.23  
% 16.37/8.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.37/8.27  tff(f_219, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 16.37/8.27  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 16.37/8.27  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 16.37/8.27  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 16.37/8.27  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 16.37/8.27  tff(f_124, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 16.37/8.27  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 16.37/8.27  tff(f_183, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 16.37/8.27  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 16.37/8.27  tff(f_202, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 16.37/8.27  tff(f_89, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 16.37/8.27  tff(f_110, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 16.37/8.27  tff(f_88, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 16.37/8.27  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 16.37/8.27  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 16.37/8.27  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 16.37/8.27  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 16.37/8.27  tff(f_173, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_relset_1)).
% 16.37/8.27  tff(f_162, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 16.37/8.27  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 16.37/8.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.37/8.27  tff(c_114, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.37/8.27  tff(c_1589, plain, (![C_210, A_211, B_212]: (v4_relat_1(C_210, A_211) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 16.37/8.27  tff(c_1613, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_114, c_1589])).
% 16.37/8.27  tff(c_1315, plain, (![C_187, A_188, B_189]: (v1_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 16.37/8.27  tff(c_1337, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_114, c_1315])).
% 16.37/8.27  tff(c_38, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.37/8.27  tff(c_1354, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1337, c_38])).
% 16.37/8.27  tff(c_1356, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1354])).
% 16.37/8.27  tff(c_118, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.37/8.27  tff(c_48, plain, (![A_26]: (v1_funct_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.37/8.27  tff(c_108, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.37/8.27  tff(c_214, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_108])).
% 16.37/8.27  tff(c_217, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_214])).
% 16.37/8.27  tff(c_220, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_217])).
% 16.37/8.27  tff(c_384, plain, (![C_95, A_96, B_97]: (v1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 16.37/8.27  tff(c_394, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_114, c_384])).
% 16.37/8.27  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_394])).
% 16.37/8.27  tff(c_411, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_108])).
% 16.37/8.27  tff(c_112, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.37/8.27  tff(c_60, plain, (![A_28]: (k2_relat_1(k2_funct_1(A_28))=k1_relat_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_124])).
% 16.37/8.27  tff(c_50, plain, (![A_26]: (v1_relat_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.37/8.27  tff(c_110, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.37/8.27  tff(c_2416, plain, (![A_294, B_295, C_296]: (k2_relset_1(A_294, B_295, C_296)=k2_relat_1(C_296) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 16.37/8.27  tff(c_2429, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_114, c_2416])).
% 16.37/8.27  tff(c_2444, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2429])).
% 16.37/8.27  tff(c_2089, plain, (![A_263]: (k1_relat_1(k2_funct_1(A_263))=k2_relat_1(A_263) | ~v2_funct_1(A_263) | ~v1_funct_1(A_263) | ~v1_relat_1(A_263))), inference(cnfTransformation, [status(thm)], [f_124])).
% 16.37/8.27  tff(c_92, plain, (![A_52]: (v1_funct_2(A_52, k1_relat_1(A_52), k2_relat_1(A_52)) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_183])).
% 16.37/8.27  tff(c_10476, plain, (![A_778]: (v1_funct_2(k2_funct_1(A_778), k2_relat_1(A_778), k2_relat_1(k2_funct_1(A_778))) | ~v1_funct_1(k2_funct_1(A_778)) | ~v1_relat_1(k2_funct_1(A_778)) | ~v2_funct_1(A_778) | ~v1_funct_1(A_778) | ~v1_relat_1(A_778))), inference(superposition, [status(thm), theory('equality')], [c_2089, c_92])).
% 16.37/8.27  tff(c_10500, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2444, c_10476])).
% 16.37/8.27  tff(c_10524, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_118, c_112, c_411, c_10500])).
% 16.37/8.27  tff(c_10529, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_10524])).
% 16.37/8.27  tff(c_10532, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_10529])).
% 16.37/8.27  tff(c_10536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1337, c_118, c_10532])).
% 16.37/8.27  tff(c_10537, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5')))), inference(splitRight, [status(thm)], [c_10524])).
% 16.37/8.27  tff(c_10561, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_60, c_10537])).
% 16.37/8.27  tff(c_10565, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_118, c_112, c_10561])).
% 16.37/8.27  tff(c_10538, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_10524])).
% 16.37/8.27  tff(c_62, plain, (![A_28]: (k1_relat_1(k2_funct_1(A_28))=k2_relat_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_124])).
% 16.37/8.27  tff(c_2270, plain, (![A_281]: (m1_subset_1(A_281, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_281), k2_relat_1(A_281)))) | ~v1_funct_1(A_281) | ~v1_relat_1(A_281))), inference(cnfTransformation, [status(thm)], [f_183])).
% 16.37/8.27  tff(c_11317, plain, (![A_817]: (m1_subset_1(k2_funct_1(A_817), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_817), k2_relat_1(k2_funct_1(A_817))))) | ~v1_funct_1(k2_funct_1(A_817)) | ~v1_relat_1(k2_funct_1(A_817)) | ~v2_funct_1(A_817) | ~v1_funct_1(A_817) | ~v1_relat_1(A_817))), inference(superposition, [status(thm), theory('equality')], [c_62, c_2270])).
% 16.37/8.27  tff(c_11372, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2444, c_11317])).
% 16.37/8.27  tff(c_11413, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_118, c_112, c_10538, c_411, c_11372])).
% 16.37/8.27  tff(c_11454, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_60, c_11413])).
% 16.37/8.27  tff(c_11476, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_118, c_112, c_11454])).
% 16.37/8.27  tff(c_26, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 16.37/8.27  tff(c_3059, plain, (![B_337, D_338, A_339, C_340]: (k1_xboole_0=B_337 | m1_subset_1(D_338, k1_zfmisc_1(k2_zfmisc_1(A_339, C_340))) | ~r1_tarski(B_337, C_340) | ~m1_subset_1(D_338, k1_zfmisc_1(k2_zfmisc_1(A_339, B_337))) | ~v1_funct_2(D_338, A_339, B_337) | ~v1_funct_1(D_338))), inference(cnfTransformation, [status(thm)], [f_202])).
% 16.37/8.27  tff(c_12184, plain, (![B_830, D_831, A_832, A_833]: (k1_relat_1(B_830)=k1_xboole_0 | m1_subset_1(D_831, k1_zfmisc_1(k2_zfmisc_1(A_832, A_833))) | ~m1_subset_1(D_831, k1_zfmisc_1(k2_zfmisc_1(A_832, k1_relat_1(B_830)))) | ~v1_funct_2(D_831, A_832, k1_relat_1(B_830)) | ~v1_funct_1(D_831) | ~v4_relat_1(B_830, A_833) | ~v1_relat_1(B_830))), inference(resolution, [status(thm)], [c_26, c_3059])).
% 16.37/8.27  tff(c_12186, plain, (![A_833]: (k1_relat_1('#skF_5')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_833))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v4_relat_1('#skF_5', A_833) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_11476, c_12184])).
% 16.37/8.27  tff(c_12207, plain, (![A_833]: (k1_relat_1('#skF_5')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_833))) | ~v4_relat_1('#skF_5', A_833))), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_411, c_10565, c_12186])).
% 16.37/8.27  tff(c_12631, plain, (![A_839]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_839))) | ~v4_relat_1('#skF_5', A_839))), inference(negUnitSimplification, [status(thm)], [c_1356, c_12207])).
% 16.37/8.27  tff(c_410, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_108])).
% 16.37/8.27  tff(c_413, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_410])).
% 16.37/8.27  tff(c_12686, plain, (~v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_12631, c_413])).
% 16.37/8.27  tff(c_12737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1613, c_12686])).
% 16.37/8.27  tff(c_12738, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1354])).
% 16.37/8.27  tff(c_44, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 16.37/8.27  tff(c_127, plain, (![A_58]: (v1_relat_1(k6_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.37/8.27  tff(c_129, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_127])).
% 16.37/8.27  tff(c_454, plain, (![A_106]: (k2_relat_1(A_106)=k1_xboole_0 | k1_relat_1(A_106)!=k1_xboole_0 | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.37/8.27  tff(c_472, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_129, c_454])).
% 16.37/8.27  tff(c_477, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_472])).
% 16.37/8.27  tff(c_618, plain, (![A_117]: (k1_relat_1(A_117)=k1_xboole_0 | k2_relat_1(A_117)!=k1_xboole_0 | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.37/8.27  tff(c_627, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_129, c_618])).
% 16.37/8.27  tff(c_638, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_477, c_627])).
% 16.37/8.27  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.37/8.27  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.37/8.27  tff(c_837, plain, (![C_145, B_146, A_147]: (v5_relat_1(C_145, B_146) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 16.37/8.27  tff(c_939, plain, (![A_157, B_158, A_159]: (v5_relat_1(A_157, B_158) | ~r1_tarski(A_157, k2_zfmisc_1(A_159, B_158)))), inference(resolution, [status(thm)], [c_18, c_837])).
% 16.37/8.27  tff(c_971, plain, (![A_159, B_158]: (v5_relat_1(k2_zfmisc_1(A_159, B_158), B_158))), inference(resolution, [status(thm)], [c_6, c_939])).
% 16.37/8.27  tff(c_981, plain, (![B_162, A_163]: (r1_tarski(k2_relat_1(B_162), A_163) | ~v5_relat_1(B_162, A_163) | ~v1_relat_1(B_162))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.37/8.27  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.37/8.27  tff(c_414, plain, (![A_98, B_99]: (r1_tarski(A_98, B_99) | ~m1_subset_1(A_98, k1_zfmisc_1(B_99)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.37/8.27  tff(c_426, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_414])).
% 16.37/8.27  tff(c_488, plain, (![B_110, A_111]: (B_110=A_111 | ~r1_tarski(B_110, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.37/8.27  tff(c_506, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_426, c_488])).
% 16.37/8.27  tff(c_1099, plain, (![B_174]: (k2_relat_1(B_174)=k1_xboole_0 | ~v5_relat_1(B_174, k1_xboole_0) | ~v1_relat_1(B_174))), inference(resolution, [status(thm)], [c_981, c_506])).
% 16.37/8.27  tff(c_1107, plain, (![A_159]: (k2_relat_1(k2_zfmisc_1(A_159, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_159, k1_xboole_0)))), inference(resolution, [status(thm)], [c_971, c_1099])).
% 16.37/8.27  tff(c_1125, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_129, c_10, c_10, c_1107])).
% 16.37/8.27  tff(c_1127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_638, c_1125])).
% 16.37/8.27  tff(c_1128, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_472])).
% 16.37/8.27  tff(c_12749, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12738, c_12738, c_1128])).
% 16.37/8.27  tff(c_12757, plain, (![A_5]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_12738, c_14])).
% 16.37/8.27  tff(c_13937, plain, (![A_946, B_947, C_948]: (k2_relset_1(A_946, B_947, C_948)=k2_relat_1(C_948) | ~m1_subset_1(C_948, k1_zfmisc_1(k2_zfmisc_1(A_946, B_947))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 16.37/8.27  tff(c_13950, plain, (![A_946, B_947]: (k2_relset_1(A_946, B_947, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12757, c_13937])).
% 16.37/8.27  tff(c_13963, plain, (![A_949, B_950]: (k2_relset_1(A_949, B_950, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12749, c_13950])).
% 16.37/8.27  tff(c_13967, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_13963, c_110])).
% 16.37/8.27  tff(c_12756, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12738, c_12738, c_10])).
% 16.37/8.27  tff(c_14011, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13967, c_13967, c_12756])).
% 16.37/8.27  tff(c_425, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_114, c_414])).
% 16.37/8.27  tff(c_1134, plain, (![B_175, A_176]: (B_175=A_176 | ~r1_tarski(B_175, A_176) | ~r1_tarski(A_176, B_175))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.37/8.27  tff(c_1151, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_425, c_1134])).
% 16.37/8.27  tff(c_1303, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1151])).
% 16.37/8.27  tff(c_14024, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13967, c_1303])).
% 16.37/8.27  tff(c_14512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14011, c_14024])).
% 16.37/8.27  tff(c_14513, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_1151])).
% 16.37/8.27  tff(c_14516, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_14513, c_114])).
% 16.37/8.27  tff(c_14983, plain, (![C_1007, A_1008, B_1009]: (v4_relat_1(C_1007, A_1008) | ~m1_subset_1(C_1007, k1_zfmisc_1(k2_zfmisc_1(A_1008, B_1009))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 16.37/8.27  tff(c_15025, plain, (![C_1014]: (v4_relat_1(C_1014, '#skF_3') | ~m1_subset_1(C_1014, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_14513, c_14983])).
% 16.37/8.27  tff(c_15042, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_14516, c_15025])).
% 16.37/8.27  tff(c_14542, plain, (![C_975, A_976, B_977]: (v1_relat_1(C_975) | ~m1_subset_1(C_975, k1_zfmisc_1(k2_zfmisc_1(A_976, B_977))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 16.37/8.27  tff(c_14590, plain, (![C_980]: (v1_relat_1(C_980) | ~m1_subset_1(C_980, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_14513, c_14542])).
% 16.37/8.27  tff(c_14607, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14516, c_14590])).
% 16.37/8.27  tff(c_14625, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_14607, c_38])).
% 16.37/8.27  tff(c_14645, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14625])).
% 16.37/8.27  tff(c_16691, plain, (![A_1148, B_1149, C_1150]: (k2_relset_1(A_1148, B_1149, C_1150)=k2_relat_1(C_1150) | ~m1_subset_1(C_1150, k1_zfmisc_1(k2_zfmisc_1(A_1148, B_1149))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 16.37/8.27  tff(c_16754, plain, (![C_1157]: (k2_relset_1('#skF_3', '#skF_4', C_1157)=k2_relat_1(C_1157) | ~m1_subset_1(C_1157, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_14513, c_16691])).
% 16.37/8.27  tff(c_16760, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14516, c_16754])).
% 16.37/8.27  tff(c_16772, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_16760])).
% 16.37/8.27  tff(c_15747, plain, (![A_1096]: (k1_relat_1(k2_funct_1(A_1096))=k2_relat_1(A_1096) | ~v2_funct_1(A_1096) | ~v1_funct_1(A_1096) | ~v1_relat_1(A_1096))), inference(cnfTransformation, [status(thm)], [f_124])).
% 16.37/8.27  tff(c_24064, plain, (![A_1569]: (v1_funct_2(k2_funct_1(A_1569), k2_relat_1(A_1569), k2_relat_1(k2_funct_1(A_1569))) | ~v1_funct_1(k2_funct_1(A_1569)) | ~v1_relat_1(k2_funct_1(A_1569)) | ~v2_funct_1(A_1569) | ~v1_funct_1(A_1569) | ~v1_relat_1(A_1569))), inference(superposition, [status(thm), theory('equality')], [c_15747, c_92])).
% 16.37/8.27  tff(c_24091, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16772, c_24064])).
% 16.37/8.27  tff(c_24126, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_14607, c_118, c_112, c_411, c_24091])).
% 16.37/8.27  tff(c_24144, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_24126])).
% 16.37/8.27  tff(c_24147, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_24144])).
% 16.37/8.27  tff(c_24151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14607, c_118, c_24147])).
% 16.37/8.27  tff(c_24152, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5')))), inference(splitRight, [status(thm)], [c_24126])).
% 16.37/8.27  tff(c_24198, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_60, c_24152])).
% 16.37/8.27  tff(c_24202, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_14607, c_118, c_112, c_24198])).
% 16.37/8.27  tff(c_24153, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_24126])).
% 16.37/8.27  tff(c_16366, plain, (![A_1137]: (m1_subset_1(A_1137, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1137), k2_relat_1(A_1137)))) | ~v1_funct_1(A_1137) | ~v1_relat_1(A_1137))), inference(cnfTransformation, [status(thm)], [f_183])).
% 16.37/8.27  tff(c_24879, plain, (![A_1619]: (m1_subset_1(k2_funct_1(A_1619), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1619), k2_relat_1(k2_funct_1(A_1619))))) | ~v1_funct_1(k2_funct_1(A_1619)) | ~v1_relat_1(k2_funct_1(A_1619)) | ~v2_funct_1(A_1619) | ~v1_funct_1(A_1619) | ~v1_relat_1(A_1619))), inference(superposition, [status(thm), theory('equality')], [c_62, c_16366])).
% 16.37/8.27  tff(c_24937, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16772, c_24879])).
% 16.37/8.27  tff(c_24989, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_14607, c_118, c_112, c_24153, c_411, c_24937])).
% 16.37/8.27  tff(c_25049, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_60, c_24989])).
% 16.37/8.27  tff(c_25071, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_14607, c_118, c_112, c_25049])).
% 16.37/8.27  tff(c_17286, plain, (![B_1186, D_1187, A_1188, C_1189]: (k1_xboole_0=B_1186 | m1_subset_1(D_1187, k1_zfmisc_1(k2_zfmisc_1(A_1188, C_1189))) | ~r1_tarski(B_1186, C_1189) | ~m1_subset_1(D_1187, k1_zfmisc_1(k2_zfmisc_1(A_1188, B_1186))) | ~v1_funct_2(D_1187, A_1188, B_1186) | ~v1_funct_1(D_1187))), inference(cnfTransformation, [status(thm)], [f_202])).
% 16.37/8.27  tff(c_25994, plain, (![B_1641, D_1642, A_1643, A_1644]: (k1_relat_1(B_1641)=k1_xboole_0 | m1_subset_1(D_1642, k1_zfmisc_1(k2_zfmisc_1(A_1643, A_1644))) | ~m1_subset_1(D_1642, k1_zfmisc_1(k2_zfmisc_1(A_1643, k1_relat_1(B_1641)))) | ~v1_funct_2(D_1642, A_1643, k1_relat_1(B_1641)) | ~v1_funct_1(D_1642) | ~v4_relat_1(B_1641, A_1644) | ~v1_relat_1(B_1641))), inference(resolution, [status(thm)], [c_26, c_17286])).
% 16.37/8.27  tff(c_25996, plain, (![A_1644]: (k1_relat_1('#skF_5')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_1644))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v4_relat_1('#skF_5', A_1644) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_25071, c_25994])).
% 16.37/8.27  tff(c_26017, plain, (![A_1644]: (k1_relat_1('#skF_5')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_1644))) | ~v4_relat_1('#skF_5', A_1644))), inference(demodulation, [status(thm), theory('equality')], [c_14607, c_411, c_24202, c_25996])).
% 16.37/8.27  tff(c_26099, plain, (![A_1646]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_1646))) | ~v4_relat_1('#skF_5', A_1646))), inference(negUnitSimplification, [status(thm)], [c_14645, c_26017])).
% 16.37/8.27  tff(c_26142, plain, (~v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_26099, c_413])).
% 16.37/8.27  tff(c_26184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15042, c_26142])).
% 16.37/8.27  tff(c_26185, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_14625])).
% 16.37/8.27  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.37/8.27  tff(c_26229, plain, (![B_1647, A_1648]: (B_1647='#skF_5' | A_1648='#skF_5' | k2_zfmisc_1(A_1648, B_1647)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26185, c_26185, c_26185, c_8])).
% 16.37/8.27  tff(c_26233, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_14513, c_26229])).
% 16.37/8.27  tff(c_26405, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_26233])).
% 16.37/8.27  tff(c_26197, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_26185, c_26185, c_1128])).
% 16.37/8.27  tff(c_26418, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26405, c_26405, c_26197])).
% 16.37/8.27  tff(c_26205, plain, (![A_5]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_26185, c_14])).
% 16.37/8.27  tff(c_26406, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_26405, c_26205])).
% 16.37/8.27  tff(c_27780, plain, (![A_1788, B_1789, C_1790]: (k2_relset_1(A_1788, B_1789, C_1790)=k2_relat_1(C_1790) | ~m1_subset_1(C_1790, k1_zfmisc_1(k2_zfmisc_1(A_1788, B_1789))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 16.37/8.27  tff(c_27790, plain, (![A_1788, B_1789]: (k2_relset_1(A_1788, B_1789, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_26406, c_27780])).
% 16.37/8.27  tff(c_27802, plain, (![A_1791, B_1792]: (k2_relset_1(A_1791, B_1792, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26418, c_27790])).
% 16.37/8.27  tff(c_26431, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26405, c_110])).
% 16.37/8.27  tff(c_27806, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_27802, c_26431])).
% 16.37/8.27  tff(c_27861, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_27806, c_26406])).
% 16.37/8.27  tff(c_26423, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26405, c_14607])).
% 16.37/8.27  tff(c_27873, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27806, c_26423])).
% 16.37/8.27  tff(c_26434, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26405, c_118])).
% 16.37/8.27  tff(c_27876, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27806, c_26434])).
% 16.37/8.27  tff(c_26433, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26405, c_112])).
% 16.37/8.27  tff(c_27877, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27806, c_26433])).
% 16.37/8.27  tff(c_26186, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_14625])).
% 16.37/8.27  tff(c_26218, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_26185, c_26186])).
% 16.37/8.27  tff(c_26419, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26405, c_26405, c_26218])).
% 16.37/8.27  tff(c_27870, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27806, c_27806, c_26419])).
% 16.37/8.27  tff(c_26430, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26405, c_411])).
% 16.37/8.27  tff(c_27872, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27806, c_26430])).
% 16.37/8.27  tff(c_27553, plain, (![A_1759]: (k2_relat_1(k2_funct_1(A_1759))=k1_relat_1(A_1759) | ~v2_funct_1(A_1759) | ~v1_funct_1(A_1759) | ~v1_relat_1(A_1759))), inference(cnfTransformation, [status(thm)], [f_124])).
% 16.37/8.27  tff(c_33066, plain, (![A_2140]: (v1_funct_2(k2_funct_1(A_2140), k1_relat_1(k2_funct_1(A_2140)), k1_relat_1(A_2140)) | ~v1_funct_1(k2_funct_1(A_2140)) | ~v1_relat_1(k2_funct_1(A_2140)) | ~v2_funct_1(A_2140) | ~v1_funct_1(A_2140) | ~v1_relat_1(A_2140))), inference(superposition, [status(thm), theory('equality')], [c_27553, c_92])).
% 16.37/8.27  tff(c_33069, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_27870, c_33066])).
% 16.37/8.27  tff(c_33077, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27873, c_27876, c_27877, c_27872, c_33069])).
% 16.37/8.27  tff(c_33078, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_33077])).
% 16.37/8.27  tff(c_33081, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_33078])).
% 16.37/8.27  tff(c_33085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27873, c_27876, c_33081])).
% 16.37/8.27  tff(c_33087, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_33077])).
% 16.37/8.27  tff(c_36, plain, (![A_21]: (k2_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.37/8.27  tff(c_26203, plain, (![A_21]: (k2_relat_1(A_21)!='#skF_5' | A_21='#skF_5' | ~v1_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_26185, c_26185, c_36])).
% 16.37/8.27  tff(c_26953, plain, (![A_21]: (k2_relat_1(A_21)!='#skF_3' | A_21='#skF_3' | ~v1_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_26405, c_26405, c_26203])).
% 16.37/8.27  tff(c_27846, plain, (![A_21]: (k2_relat_1(A_21)!='#skF_4' | A_21='#skF_4' | ~v1_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_27806, c_27806, c_26953])).
% 16.37/8.27  tff(c_33103, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_33087, c_27846])).
% 16.37/8.27  tff(c_33109, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_33103])).
% 16.37/8.27  tff(c_33115, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_60, c_33109])).
% 16.37/8.27  tff(c_33121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27873, c_27876, c_27877, c_27870, c_33115])).
% 16.37/8.27  tff(c_33122, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_33103])).
% 16.37/8.27  tff(c_26204, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26185, c_26185, c_10])).
% 16.37/8.27  tff(c_26408, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26405, c_26405, c_26204])).
% 16.37/8.27  tff(c_26429, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26405, c_413])).
% 16.37/8.27  tff(c_26741, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26408, c_26429])).
% 16.37/8.27  tff(c_27854, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_27806, c_27806, c_26741])).
% 16.37/8.27  tff(c_33127, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_33122, c_27854])).
% 16.37/8.27  tff(c_33135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27861, c_33127])).
% 16.37/8.27  tff(c_33136, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_26233])).
% 16.37/8.27  tff(c_33138, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_33136, c_26205])).
% 16.37/8.27  tff(c_33155, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33136, c_14607])).
% 16.37/8.27  tff(c_33166, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33136, c_118])).
% 16.37/8.27  tff(c_33165, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33136, c_112])).
% 16.37/8.27  tff(c_33151, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33136, c_33136, c_26218])).
% 16.37/8.27  tff(c_33162, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_33136, c_411])).
% 16.37/8.27  tff(c_34043, plain, (![A_2220]: (k2_relat_1(k2_funct_1(A_2220))=k1_relat_1(A_2220) | ~v2_funct_1(A_2220) | ~v1_funct_1(A_2220) | ~v1_relat_1(A_2220))), inference(cnfTransformation, [status(thm)], [f_124])).
% 16.37/8.27  tff(c_41530, plain, (![A_2704]: (v1_funct_2(k2_funct_1(A_2704), k1_relat_1(k2_funct_1(A_2704)), k1_relat_1(A_2704)) | ~v1_funct_1(k2_funct_1(A_2704)) | ~v1_relat_1(k2_funct_1(A_2704)) | ~v2_funct_1(A_2704) | ~v1_funct_1(A_2704) | ~v1_relat_1(A_2704))), inference(superposition, [status(thm), theory('equality')], [c_34043, c_92])).
% 16.37/8.27  tff(c_41545, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_33151, c_41530])).
% 16.37/8.27  tff(c_41547, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_33155, c_33166, c_33165, c_33162, c_41545])).
% 16.37/8.27  tff(c_41572, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_41547])).
% 16.37/8.27  tff(c_41575, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_41572])).
% 16.37/8.27  tff(c_41579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33155, c_33166, c_41575])).
% 16.37/8.27  tff(c_41581, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_41547])).
% 16.37/8.27  tff(c_33660, plain, (![A_21]: (k2_relat_1(A_21)!='#skF_4' | A_21='#skF_4' | ~v1_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_33136, c_33136, c_26203])).
% 16.37/8.27  tff(c_41596, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_41581, c_33660])).
% 16.37/8.27  tff(c_41603, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_41596])).
% 16.37/8.27  tff(c_41609, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_60, c_41603])).
% 16.37/8.27  tff(c_41615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33155, c_33166, c_33165, c_33151, c_41609])).
% 16.37/8.27  tff(c_41616, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_41596])).
% 16.37/8.27  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.37/8.27  tff(c_26206, plain, (![B_4]: (k2_zfmisc_1('#skF_5', B_4)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26185, c_26185, c_12])).
% 16.37/8.27  tff(c_33142, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33136, c_33136, c_26206])).
% 16.37/8.27  tff(c_33161, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_33136, c_413])).
% 16.37/8.27  tff(c_33491, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_33142, c_33161])).
% 16.37/8.27  tff(c_41621, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_41616, c_33491])).
% 16.37/8.27  tff(c_41629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33138, c_41621])).
% 16.37/8.27  tff(c_41630, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_410])).
% 16.37/8.27  tff(c_41694, plain, (![C_2721, A_2722, B_2723]: (v1_relat_1(C_2721) | ~m1_subset_1(C_2721, k1_zfmisc_1(k2_zfmisc_1(A_2722, B_2723))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 16.37/8.27  tff(c_41720, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_114, c_41694])).
% 16.37/8.27  tff(c_41631, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_410])).
% 16.37/8.27  tff(c_41718, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_41631, c_41694])).
% 16.37/8.27  tff(c_43697, plain, (![A_2895, B_2896, C_2897]: (k2_relset_1(A_2895, B_2896, C_2897)=k2_relat_1(C_2897) | ~m1_subset_1(C_2897, k1_zfmisc_1(k2_zfmisc_1(A_2895, B_2896))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 16.37/8.27  tff(c_43713, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_114, c_43697])).
% 16.37/8.27  tff(c_43729, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_43713])).
% 16.37/8.27  tff(c_43325, plain, (![A_2862]: (k1_relat_1(k2_funct_1(A_2862))=k2_relat_1(A_2862) | ~v2_funct_1(A_2862) | ~v1_funct_1(A_2862) | ~v1_relat_1(A_2862))), inference(cnfTransformation, [status(thm)], [f_124])).
% 16.37/8.27  tff(c_52014, plain, (![A_3377]: (v1_funct_2(k2_funct_1(A_3377), k2_relat_1(A_3377), k2_relat_1(k2_funct_1(A_3377))) | ~v1_funct_1(k2_funct_1(A_3377)) | ~v1_relat_1(k2_funct_1(A_3377)) | ~v2_funct_1(A_3377) | ~v1_funct_1(A_3377) | ~v1_relat_1(A_3377))), inference(superposition, [status(thm), theory('equality')], [c_43325, c_92])).
% 16.37/8.27  tff(c_52035, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_43729, c_52014])).
% 16.37/8.27  tff(c_52060, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_41720, c_118, c_112, c_41718, c_411, c_52035])).
% 16.37/8.27  tff(c_52072, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_60, c_52060])).
% 16.37/8.27  tff(c_52076, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_41720, c_118, c_112, c_52072])).
% 16.37/8.27  tff(c_43601, plain, (![A_2887]: (m1_subset_1(A_2887, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2887), k2_relat_1(A_2887)))) | ~v1_funct_1(A_2887) | ~v1_relat_1(A_2887))), inference(cnfTransformation, [status(thm)], [f_183])).
% 16.37/8.27  tff(c_52484, plain, (![A_3391]: (m1_subset_1(k2_funct_1(A_3391), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_3391), k2_relat_1(k2_funct_1(A_3391))))) | ~v1_funct_1(k2_funct_1(A_3391)) | ~v1_relat_1(k2_funct_1(A_3391)) | ~v2_funct_1(A_3391) | ~v1_funct_1(A_3391) | ~v1_relat_1(A_3391))), inference(superposition, [status(thm), theory('equality')], [c_62, c_43601])).
% 16.37/8.27  tff(c_52542, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_43729, c_52484])).
% 16.37/8.27  tff(c_52588, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_41720, c_118, c_112, c_41718, c_411, c_52542])).
% 16.37/8.27  tff(c_52637, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_60, c_52588])).
% 16.37/8.27  tff(c_52661, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_41720, c_118, c_112, c_52637])).
% 16.37/8.27  tff(c_41729, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_41720, c_38])).
% 16.37/8.27  tff(c_41739, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_41729])).
% 16.37/8.27  tff(c_42908, plain, (![C_2819, B_2820, A_2821]: (v5_relat_1(C_2819, B_2820) | ~m1_subset_1(C_2819, k1_zfmisc_1(k2_zfmisc_1(A_2821, B_2820))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 16.37/8.27  tff(c_42934, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_41631, c_42908])).
% 16.37/8.27  tff(c_43442, plain, (![A_2869]: (k2_relat_1(k2_funct_1(A_2869))=k1_relat_1(A_2869) | ~v2_funct_1(A_2869) | ~v1_funct_1(A_2869) | ~v1_relat_1(A_2869))), inference(cnfTransformation, [status(thm)], [f_124])).
% 16.37/8.27  tff(c_30, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.37/8.27  tff(c_50691, plain, (![A_3286, A_3287]: (r1_tarski(k1_relat_1(A_3286), A_3287) | ~v5_relat_1(k2_funct_1(A_3286), A_3287) | ~v1_relat_1(k2_funct_1(A_3286)) | ~v2_funct_1(A_3286) | ~v1_funct_1(A_3286) | ~v1_relat_1(A_3286))), inference(superposition, [status(thm), theory('equality')], [c_43442, c_30])).
% 16.37/8.27  tff(c_50724, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42934, c_50691])).
% 16.37/8.27  tff(c_50741, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41720, c_118, c_112, c_41718, c_50724])).
% 16.37/8.27  tff(c_102, plain, (![B_54, D_56, A_53, C_55]: (k1_xboole_0=B_54 | v1_funct_2(D_56, A_53, C_55) | ~r1_tarski(B_54, C_55) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(D_56, A_53, B_54) | ~v1_funct_1(D_56))), inference(cnfTransformation, [status(thm)], [f_202])).
% 16.37/8.27  tff(c_50750, plain, (![D_56, A_53]: (k1_relat_1('#skF_5')=k1_xboole_0 | v1_funct_2(D_56, A_53, '#skF_3') | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_53, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_56, A_53, k1_relat_1('#skF_5')) | ~v1_funct_1(D_56))), inference(resolution, [status(thm)], [c_50741, c_102])).
% 16.37/8.27  tff(c_50768, plain, (![D_56, A_53]: (v1_funct_2(D_56, A_53, '#skF_3') | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_53, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_56, A_53, k1_relat_1('#skF_5')) | ~v1_funct_1(D_56))), inference(negUnitSimplification, [status(thm)], [c_41739, c_50750])).
% 16.37/8.27  tff(c_53044, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_52661, c_50768])).
% 16.37/8.27  tff(c_53082, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_52076, c_53044])).
% 16.37/8.27  tff(c_53084, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41630, c_53082])).
% 16.37/8.27  tff(c_53085, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_41729])).
% 16.37/8.27  tff(c_53086, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_41729])).
% 16.37/8.27  tff(c_53139, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_53085, c_53086])).
% 16.37/8.27  tff(c_42, plain, (![A_22]: (k2_relat_1(A_22)=k1_xboole_0 | k1_relat_1(A_22)!=k1_xboole_0 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.37/8.27  tff(c_53114, plain, (![A_3396]: (k2_relat_1(A_3396)='#skF_5' | k1_relat_1(A_3396)!='#skF_5' | ~v1_relat_1(A_3396))), inference(demodulation, [status(thm), theory('equality')], [c_53085, c_53085, c_42])).
% 16.37/8.27  tff(c_53134, plain, (k2_relat_1('#skF_5')='#skF_5' | k1_relat_1('#skF_5')!='#skF_5'), inference(resolution, [status(thm)], [c_41720, c_53114])).
% 16.37/8.27  tff(c_53224, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_53139, c_53134])).
% 16.37/8.27  tff(c_53100, plain, (![A_5]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_53085, c_14])).
% 16.37/8.27  tff(c_55340, plain, (![A_3612, B_3613, C_3614]: (k2_relset_1(A_3612, B_3613, C_3614)=k2_relat_1(C_3614) | ~m1_subset_1(C_3614, k1_zfmisc_1(k2_zfmisc_1(A_3612, B_3613))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 16.37/8.27  tff(c_55347, plain, (![A_3612, B_3613]: (k2_relset_1(A_3612, B_3613, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_53100, c_55340])).
% 16.37/8.27  tff(c_55366, plain, (![A_3615, B_3616]: (k2_relset_1(A_3615, B_3616, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_53224, c_55347])).
% 16.37/8.27  tff(c_55370, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_55366, c_110])).
% 16.37/8.27  tff(c_41632, plain, (![A_2708, B_2709]: (r1_tarski(A_2708, B_2709) | ~m1_subset_1(A_2708, k1_zfmisc_1(B_2709)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.37/8.27  tff(c_41648, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_41632])).
% 16.37/8.27  tff(c_53094, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_53085, c_41648])).
% 16.37/8.27  tff(c_41660, plain, (![A_2713, B_2714]: (m1_subset_1('#skF_2'(A_2713, B_2714), k1_zfmisc_1(k2_zfmisc_1(A_2713, B_2714))))), inference(cnfTransformation, [status(thm)], [f_173])).
% 16.37/8.27  tff(c_41688, plain, (![B_2719]: (m1_subset_1('#skF_2'(k1_xboole_0, B_2719), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_41660])).
% 16.37/8.27  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.37/8.27  tff(c_41692, plain, (![B_2719]: (r1_tarski('#skF_2'(k1_xboole_0, B_2719), k1_xboole_0))), inference(resolution, [status(thm)], [c_41688, c_16])).
% 16.37/8.27  tff(c_53217, plain, (![B_3405]: (r1_tarski('#skF_2'('#skF_5', B_3405), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_53085, c_53085, c_41692])).
% 16.37/8.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.37/8.27  tff(c_53219, plain, (![B_3405]: ('#skF_2'('#skF_5', B_3405)='#skF_5' | ~r1_tarski('#skF_5', '#skF_2'('#skF_5', B_3405)))), inference(resolution, [status(thm)], [c_53217, c_2])).
% 16.37/8.27  tff(c_53231, plain, (![B_3406]: ('#skF_2'('#skF_5', B_3406)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_53094, c_53219])).
% 16.37/8.27  tff(c_86, plain, (![A_49, B_50]: (v1_xboole_0('#skF_2'(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_173])).
% 16.37/8.27  tff(c_53246, plain, (v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_53231, c_86])).
% 16.37/8.27  tff(c_53222, plain, (![B_3405]: ('#skF_2'('#skF_5', B_3405)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_53094, c_53219])).
% 16.37/8.27  tff(c_88, plain, (![A_49, B_50]: (m1_subset_1('#skF_2'(A_49, B_50), k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_173])).
% 16.37/8.27  tff(c_55051, plain, (![C_3579, A_3580, B_3581]: (v1_partfun1(C_3579, A_3580) | ~m1_subset_1(C_3579, k1_zfmisc_1(k2_zfmisc_1(A_3580, B_3581))) | ~v1_xboole_0(A_3580))), inference(cnfTransformation, [status(thm)], [f_162])).
% 16.37/8.27  tff(c_55075, plain, (![A_3583, B_3584]: (v1_partfun1('#skF_2'(A_3583, B_3584), A_3583) | ~v1_xboole_0(A_3583))), inference(resolution, [status(thm)], [c_88, c_55051])).
% 16.37/8.27  tff(c_55081, plain, (v1_partfun1('#skF_5', '#skF_5') | ~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_53222, c_55075])).
% 16.37/8.27  tff(c_55083, plain, (v1_partfun1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_53246, c_55081])).
% 16.37/8.27  tff(c_55386, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55370, c_55370, c_55083])).
% 16.37/8.27  tff(c_55438, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55370, c_118])).
% 16.37/8.27  tff(c_55617, plain, (![A_3626]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3626)))), inference(demodulation, [status(thm), theory('equality')], [c_55370, c_53100])).
% 16.37/8.27  tff(c_74, plain, (![C_44, A_42, B_43]: (v1_funct_2(C_44, A_42, B_43) | ~v1_partfun1(C_44, A_42) | ~v1_funct_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 16.37/8.27  tff(c_55621, plain, (![A_42, B_43]: (v1_funct_2('#skF_4', A_42, B_43) | ~v1_partfun1('#skF_4', A_42) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_55617, c_74])).
% 16.37/8.27  tff(c_56233, plain, (![A_3674, B_3675]: (v1_funct_2('#skF_4', A_3674, B_3675) | ~v1_partfun1('#skF_4', A_3674))), inference(demodulation, [status(thm), theory('equality')], [c_55438, c_55621])).
% 16.37/8.27  tff(c_54207, plain, (![A_3497]: (k2_relat_1(k2_funct_1(A_3497))=k1_relat_1(A_3497) | ~v2_funct_1(A_3497) | ~v1_funct_1(A_3497) | ~v1_relat_1(A_3497))), inference(cnfTransformation, [status(thm)], [f_124])).
% 16.37/8.27  tff(c_41738, plain, (k2_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0 | k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_41718, c_36])).
% 16.37/8.27  tff(c_53369, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_53085, c_53085, c_41738])).
% 16.37/8.27  tff(c_53370, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_53369])).
% 16.37/8.27  tff(c_54231, plain, (k1_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_54207, c_53370])).
% 16.37/8.27  tff(c_54238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41720, c_118, c_112, c_53139, c_54231])).
% 16.37/8.27  tff(c_54239, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_53369])).
% 16.37/8.27  tff(c_54244, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54239, c_41630])).
% 16.37/8.27  tff(c_55412, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55370, c_54244])).
% 16.37/8.27  tff(c_56236, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_56233, c_55412])).
% 16.37/8.27  tff(c_56240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55386, c_56236])).
% 16.37/8.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.37/8.27  
% 16.37/8.27  Inference rules
% 16.37/8.27  ----------------------
% 16.37/8.27  #Ref     : 0
% 16.37/8.27  #Sup     : 11673
% 16.37/8.27  #Fact    : 0
% 16.37/8.27  #Define  : 0
% 16.37/8.27  #Split   : 97
% 16.37/8.27  #Chain   : 0
% 16.37/8.27  #Close   : 0
% 16.37/8.27  
% 16.37/8.27  Ordering : KBO
% 16.37/8.27  
% 16.37/8.27  Simplification rules
% 16.37/8.27  ----------------------
% 16.37/8.27  #Subsume      : 1815
% 16.37/8.27  #Demod        : 16177
% 16.37/8.27  #Tautology    : 4701
% 16.37/8.27  #SimpNegUnit  : 261
% 16.37/8.27  #BackRed      : 562
% 16.37/8.27  
% 16.37/8.27  #Partial instantiations: 0
% 16.37/8.27  #Strategies tried      : 1
% 16.37/8.27  
% 16.37/8.27  Timing (in seconds)
% 16.37/8.27  ----------------------
% 16.52/8.27  Preprocessing        : 0.38
% 16.52/8.27  Parsing              : 0.20
% 16.52/8.27  CNF conversion       : 0.03
% 16.52/8.27  Main loop            : 6.97
% 16.52/8.27  Inferencing          : 1.80
% 16.52/8.27  Reduction            : 2.90
% 16.52/8.27  Demodulation         : 2.23
% 16.52/8.27  BG Simplification    : 0.14
% 16.52/8.27  Subsumption          : 1.65
% 16.52/8.27  Abstraction          : 0.18
% 16.52/8.27  MUC search           : 0.00
% 16.52/8.27  Cooper               : 0.00
% 16.52/8.27  Total                : 7.45
% 16.52/8.27  Index Insertion      : 0.00
% 16.52/8.28  Index Deletion       : 0.00
% 16.52/8.28  Index Matching       : 0.00
% 16.52/8.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
