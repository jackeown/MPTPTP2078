%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:49 EST 2020

% Result     : Theorem 9.58s
% Output     : CNFRefutation 9.73s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 649 expanded)
%              Number of leaves         :   39 ( 204 expanded)
%              Depth                    :   19
%              Number of atoms          :  272 (1964 expanded)
%              Number of equality atoms :   66 ( 476 expanded)
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

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_160,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_133,axiom,(
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

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_143,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2754,plain,(
    ! [B_254,A_255] :
      ( v1_relat_1(B_254)
      | ~ m1_subset_1(B_254,k1_zfmisc_1(A_255))
      | ~ v1_relat_1(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2763,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_2754])).

tff(c_2773,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2763])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_8353,plain,(
    ! [A_591,B_592,C_593] :
      ( k2_relset_1(A_591,B_592,C_593) = k2_relat_1(C_593)
      | ~ m1_subset_1(C_593,k1_zfmisc_1(k2_zfmisc_1(A_591,B_592))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8363,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_8353])).

tff(c_8371,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8363])).

tff(c_36,plain,(
    ! [A_24] :
      ( k1_relat_1(k2_funct_1(A_24)) = k2_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_181,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_187,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_181])).

tff(c_194,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_187])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1128,plain,(
    ! [A_174,B_175,C_176] :
      ( k2_relset_1(A_174,B_175,C_176) = k2_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1138,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1128])).

tff(c_1146,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1138])).

tff(c_338,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_351,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_338])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    ! [A_24] :
      ( k2_relat_1(k2_funct_1(A_24)) = k1_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2365,plain,(
    ! [C_241,A_242,B_243] :
      ( m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ r1_tarski(k2_relat_1(C_241),B_243)
      | ~ r1_tarski(k1_relat_1(C_241),A_242)
      | ~ v1_relat_1(C_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_100,plain,(
    ! [A_49] :
      ( v1_funct_1(k2_funct_1(A_49))
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_88,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_103,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_88])).

tff(c_106,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_103])).

tff(c_140,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_146,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_140])).

tff(c_153,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_146])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_153])).

tff(c_156,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_175,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_2418,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2365,c_175])).

tff(c_2466,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2418])).

tff(c_2469,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_2466])).

tff(c_2473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_76,c_2469])).

tff(c_2474,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_2418])).

tff(c_2476,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2474])).

tff(c_2479,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2476])).

tff(c_2481,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_76,c_70,c_2479])).

tff(c_2487,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2481])).

tff(c_2494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_351,c_2487])).

tff(c_2495,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2474])).

tff(c_2737,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2495])).

tff(c_2746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_76,c_70,c_6,c_1146,c_2737])).

tff(c_2747,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_2748,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_8516,plain,(
    ! [A_606,B_607,C_608] :
      ( k1_relset_1(A_606,B_607,C_608) = k1_relat_1(C_608)
      | ~ m1_subset_1(C_608,k1_zfmisc_1(k2_zfmisc_1(A_606,B_607))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8531,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2748,c_8516])).

tff(c_12256,plain,(
    ! [B_744,C_745,A_746] :
      ( k1_xboole_0 = B_744
      | v1_funct_2(C_745,A_746,B_744)
      | k1_relset_1(A_746,B_744,C_745) != A_746
      | ~ m1_subset_1(C_745,k1_zfmisc_1(k2_zfmisc_1(A_746,B_744))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12268,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2748,c_12256])).

tff(c_12286,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8531,c_12268])).

tff(c_12287,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2747,c_12286])).

tff(c_12294,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12287])).

tff(c_12297,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_12294])).

tff(c_12300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2773,c_76,c_70,c_8371,c_12297])).

tff(c_12301,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12287])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2774,plain,(
    ! [A_7] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_2754])).

tff(c_2775,plain,(
    ! [A_7] : ~ v1_relat_1(A_7) ),
    inference(splitLeft,[status(thm)],[c_2774])).

tff(c_2757,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2748,c_2754])).

tff(c_2769,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2757])).

tff(c_2797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2775,c_2769])).

tff(c_2798,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2774])).

tff(c_2857,plain,(
    ! [C_266,A_267,B_268] :
      ( v4_relat_1(C_266,A_267)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2875,plain,(
    ! [A_267] : v4_relat_1(k1_xboole_0,A_267) ),
    inference(resolution,[status(thm)],[c_12,c_2857])).

tff(c_2901,plain,(
    ! [B_275,A_276] :
      ( r1_tarski(k1_relat_1(B_275),A_276)
      | ~ v4_relat_1(B_275,A_276)
      | ~ v1_relat_1(B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2821,plain,(
    ! [B_260,A_261] :
      ( B_260 = A_261
      | ~ r1_tarski(B_260,A_261)
      | ~ r1_tarski(A_261,B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2836,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_2821])).

tff(c_2923,plain,(
    ! [B_277] :
      ( k1_relat_1(B_277) = k1_xboole_0
      | ~ v4_relat_1(B_277,k1_xboole_0)
      | ~ v1_relat_1(B_277) ) ),
    inference(resolution,[status(thm)],[c_2901,c_2836])).

tff(c_2931,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2875,c_2923])).

tff(c_2937,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2798,c_2931])).

tff(c_12326,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12301,c_12301,c_2937])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_8533,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_8516])).

tff(c_58,plain,(
    ! [B_38,A_37,C_39] :
      ( k1_xboole_0 = B_38
      | k1_relset_1(A_37,B_38,C_39) = A_37
      | ~ v1_funct_2(C_39,A_37,B_38)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12379,plain,(
    ! [B_749,A_750,C_751] :
      ( B_749 = '#skF_1'
      | k1_relset_1(A_750,B_749,C_751) = A_750
      | ~ v1_funct_2(C_751,A_750,B_749)
      | ~ m1_subset_1(C_751,k1_zfmisc_1(k2_zfmisc_1(A_750,B_749))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12301,c_58])).

tff(c_12398,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_12379])).

tff(c_12409,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_8533,c_12398])).

tff(c_12606,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12409])).

tff(c_157,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_12302,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12287])).

tff(c_62,plain,(
    ! [A_40] :
      ( v1_funct_2(A_40,k1_relat_1(A_40),k2_relat_1(A_40))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_12818,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12302,c_62])).

tff(c_12865,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2769,c_157,c_12818])).

tff(c_13263,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_12865])).

tff(c_13265,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2773,c_76,c_70,c_12606,c_13263])).

tff(c_13267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2747,c_13265])).

tff(c_13269,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12409])).

tff(c_13268,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12409])).

tff(c_8378,plain,
    ( v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8371,c_62])).

tff(c_8382,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2773,c_76,c_8378])).

tff(c_13295,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13268,c_8382])).

tff(c_13296,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13268,c_8371])).

tff(c_8650,plain,(
    ! [A_620] :
      ( m1_subset_1(A_620,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_620),k2_relat_1(A_620))))
      | ~ v1_funct_1(A_620)
      | ~ v1_relat_1(A_620) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8700,plain,(
    ! [A_620] :
      ( r1_tarski(A_620,k2_zfmisc_1(k1_relat_1(A_620),k2_relat_1(A_620)))
      | ~ v1_funct_1(A_620)
      | ~ v1_relat_1(A_620) ) ),
    inference(resolution,[status(thm)],[c_8650,c_14])).

tff(c_13336,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13296,c_8700])).

tff(c_13353,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2773,c_76,c_13336])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8831,plain,(
    ! [C_624,A_625] :
      ( k1_xboole_0 = C_624
      | ~ v1_funct_2(C_624,A_625,k1_xboole_0)
      | k1_xboole_0 = A_625
      | ~ m1_subset_1(C_624,k1_zfmisc_1(k2_zfmisc_1(A_625,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_8840,plain,(
    ! [A_8,A_625] :
      ( k1_xboole_0 = A_8
      | ~ v1_funct_2(A_8,A_625,k1_xboole_0)
      | k1_xboole_0 = A_625
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_625,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_8831])).

tff(c_13945,plain,(
    ! [A_798,A_799] :
      ( A_798 = '#skF_1'
      | ~ v1_funct_2(A_798,A_799,'#skF_1')
      | A_799 = '#skF_1'
      | ~ r1_tarski(A_798,k2_zfmisc_1(A_799,'#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12301,c_12301,c_12301,c_12301,c_8840])).

tff(c_13948,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_1')
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_13353,c_13945])).

tff(c_13969,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13295,c_13948])).

tff(c_13970,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_13269,c_13969])).

tff(c_13999,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13970,c_13269])).

tff(c_14037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12326,c_13999])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:31:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.58/3.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/3.24  
% 9.58/3.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/3.24  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.58/3.24  
% 9.58/3.24  %Foreground sorts:
% 9.58/3.24  
% 9.58/3.24  
% 9.58/3.24  %Background operators:
% 9.58/3.24  
% 9.58/3.24  
% 9.58/3.24  %Foreground operators:
% 9.58/3.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.58/3.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.58/3.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.58/3.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.58/3.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.58/3.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.58/3.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.58/3.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.58/3.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.58/3.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.58/3.24  tff('#skF_2', type, '#skF_2': $i).
% 9.58/3.24  tff('#skF_3', type, '#skF_3': $i).
% 9.58/3.24  tff('#skF_1', type, '#skF_1': $i).
% 9.58/3.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.58/3.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.58/3.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.58/3.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.58/3.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.58/3.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.58/3.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.58/3.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.58/3.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.58/3.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.58/3.24  
% 9.73/3.26  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.73/3.26  tff(f_160, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.73/3.26  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.73/3.26  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.73/3.26  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.73/3.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.73/3.26  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.73/3.26  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.73/3.26  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.73/3.26  tff(f_115, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 9.73/3.26  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.73/3.26  tff(f_133, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.73/3.26  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.73/3.26  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.73/3.26  tff(f_143, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 9.73/3.26  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.73/3.26  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.73/3.26  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.73/3.26  tff(c_2754, plain, (![B_254, A_255]: (v1_relat_1(B_254) | ~m1_subset_1(B_254, k1_zfmisc_1(A_255)) | ~v1_relat_1(A_255))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.73/3.26  tff(c_2763, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_2754])).
% 9.73/3.26  tff(c_2773, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2763])).
% 9.73/3.26  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.73/3.26  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.73/3.26  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.73/3.26  tff(c_8353, plain, (![A_591, B_592, C_593]: (k2_relset_1(A_591, B_592, C_593)=k2_relat_1(C_593) | ~m1_subset_1(C_593, k1_zfmisc_1(k2_zfmisc_1(A_591, B_592))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.73/3.26  tff(c_8363, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_8353])).
% 9.73/3.26  tff(c_8371, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8363])).
% 9.73/3.26  tff(c_36, plain, (![A_24]: (k1_relat_1(k2_funct_1(A_24))=k2_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.73/3.26  tff(c_181, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.73/3.26  tff(c_187, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_181])).
% 9.73/3.26  tff(c_194, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_187])).
% 9.73/3.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.73/3.26  tff(c_1128, plain, (![A_174, B_175, C_176]: (k2_relset_1(A_174, B_175, C_176)=k2_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.73/3.26  tff(c_1138, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1128])).
% 9.73/3.26  tff(c_1146, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1138])).
% 9.73/3.26  tff(c_338, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.73/3.26  tff(c_351, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_338])).
% 9.73/3.26  tff(c_24, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.73/3.26  tff(c_34, plain, (![A_24]: (k2_relat_1(k2_funct_1(A_24))=k1_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.73/3.26  tff(c_32, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.73/3.26  tff(c_2365, plain, (![C_241, A_242, B_243]: (m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))) | ~r1_tarski(k2_relat_1(C_241), B_243) | ~r1_tarski(k1_relat_1(C_241), A_242) | ~v1_relat_1(C_241))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.73/3.26  tff(c_100, plain, (![A_49]: (v1_funct_1(k2_funct_1(A_49)) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.73/3.26  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.73/3.26  tff(c_88, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 9.73/3.26  tff(c_103, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_88])).
% 9.73/3.26  tff(c_106, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_103])).
% 9.73/3.26  tff(c_140, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.73/3.26  tff(c_146, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_140])).
% 9.73/3.26  tff(c_153, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_146])).
% 9.73/3.26  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_153])).
% 9.73/3.26  tff(c_156, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_66])).
% 9.73/3.26  tff(c_175, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_156])).
% 9.73/3.26  tff(c_2418, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2365, c_175])).
% 9.73/3.26  tff(c_2466, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2418])).
% 9.73/3.26  tff(c_2469, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_2466])).
% 9.73/3.26  tff(c_2473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_76, c_2469])).
% 9.73/3.26  tff(c_2474, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(splitRight, [status(thm)], [c_2418])).
% 9.73/3.26  tff(c_2476, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(splitLeft, [status(thm)], [c_2474])).
% 9.73/3.26  tff(c_2479, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_2476])).
% 9.73/3.26  tff(c_2481, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_76, c_70, c_2479])).
% 9.73/3.26  tff(c_2487, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_2481])).
% 9.73/3.26  tff(c_2494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_351, c_2487])).
% 9.73/3.26  tff(c_2495, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_2474])).
% 9.73/3.26  tff(c_2737, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_2495])).
% 9.73/3.26  tff(c_2746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_76, c_70, c_6, c_1146, c_2737])).
% 9.73/3.26  tff(c_2747, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_156])).
% 9.73/3.26  tff(c_2748, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_156])).
% 9.73/3.26  tff(c_8516, plain, (![A_606, B_607, C_608]: (k1_relset_1(A_606, B_607, C_608)=k1_relat_1(C_608) | ~m1_subset_1(C_608, k1_zfmisc_1(k2_zfmisc_1(A_606, B_607))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.73/3.26  tff(c_8531, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2748, c_8516])).
% 9.73/3.26  tff(c_12256, plain, (![B_744, C_745, A_746]: (k1_xboole_0=B_744 | v1_funct_2(C_745, A_746, B_744) | k1_relset_1(A_746, B_744, C_745)!=A_746 | ~m1_subset_1(C_745, k1_zfmisc_1(k2_zfmisc_1(A_746, B_744))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.73/3.26  tff(c_12268, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_2748, c_12256])).
% 9.73/3.26  tff(c_12286, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8531, c_12268])).
% 9.73/3.26  tff(c_12287, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2747, c_12286])).
% 9.73/3.26  tff(c_12294, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_12287])).
% 9.73/3.26  tff(c_12297, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_12294])).
% 9.73/3.26  tff(c_12300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2773, c_76, c_70, c_8371, c_12297])).
% 9.73/3.26  tff(c_12301, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_12287])).
% 9.73/3.26  tff(c_12, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.73/3.26  tff(c_2774, plain, (![A_7]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_12, c_2754])).
% 9.73/3.26  tff(c_2775, plain, (![A_7]: (~v1_relat_1(A_7))), inference(splitLeft, [status(thm)], [c_2774])).
% 9.73/3.26  tff(c_2757, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_2748, c_2754])).
% 9.73/3.26  tff(c_2769, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2757])).
% 9.73/3.26  tff(c_2797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2775, c_2769])).
% 9.73/3.26  tff(c_2798, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_2774])).
% 9.73/3.26  tff(c_2857, plain, (![C_266, A_267, B_268]: (v4_relat_1(C_266, A_267) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.73/3.26  tff(c_2875, plain, (![A_267]: (v4_relat_1(k1_xboole_0, A_267))), inference(resolution, [status(thm)], [c_12, c_2857])).
% 9.73/3.26  tff(c_2901, plain, (![B_275, A_276]: (r1_tarski(k1_relat_1(B_275), A_276) | ~v4_relat_1(B_275, A_276) | ~v1_relat_1(B_275))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.73/3.26  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.73/3.26  tff(c_2821, plain, (![B_260, A_261]: (B_260=A_261 | ~r1_tarski(B_260, A_261) | ~r1_tarski(A_261, B_260))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.73/3.26  tff(c_2836, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_2821])).
% 9.73/3.26  tff(c_2923, plain, (![B_277]: (k1_relat_1(B_277)=k1_xboole_0 | ~v4_relat_1(B_277, k1_xboole_0) | ~v1_relat_1(B_277))), inference(resolution, [status(thm)], [c_2901, c_2836])).
% 9.73/3.26  tff(c_2931, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2875, c_2923])).
% 9.73/3.26  tff(c_2937, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2798, c_2931])).
% 9.73/3.26  tff(c_12326, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12301, c_12301, c_2937])).
% 9.73/3.26  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.73/3.26  tff(c_8533, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_8516])).
% 9.73/3.26  tff(c_58, plain, (![B_38, A_37, C_39]: (k1_xboole_0=B_38 | k1_relset_1(A_37, B_38, C_39)=A_37 | ~v1_funct_2(C_39, A_37, B_38) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.73/3.26  tff(c_12379, plain, (![B_749, A_750, C_751]: (B_749='#skF_1' | k1_relset_1(A_750, B_749, C_751)=A_750 | ~v1_funct_2(C_751, A_750, B_749) | ~m1_subset_1(C_751, k1_zfmisc_1(k2_zfmisc_1(A_750, B_749))))), inference(demodulation, [status(thm), theory('equality')], [c_12301, c_58])).
% 9.73/3.26  tff(c_12398, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_12379])).
% 9.73/3.26  tff(c_12409, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_8533, c_12398])).
% 9.73/3.26  tff(c_12606, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_12409])).
% 9.73/3.26  tff(c_157, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 9.73/3.26  tff(c_12302, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_12287])).
% 9.73/3.26  tff(c_62, plain, (![A_40]: (v1_funct_2(A_40, k1_relat_1(A_40), k2_relat_1(A_40)) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.73/3.26  tff(c_12818, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12302, c_62])).
% 9.73/3.26  tff(c_12865, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2769, c_157, c_12818])).
% 9.73/3.26  tff(c_13263, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_12865])).
% 9.73/3.26  tff(c_13265, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2773, c_76, c_70, c_12606, c_13263])).
% 9.73/3.26  tff(c_13267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2747, c_13265])).
% 9.73/3.26  tff(c_13269, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_12409])).
% 9.73/3.26  tff(c_13268, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_12409])).
% 9.73/3.26  tff(c_8378, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8371, c_62])).
% 9.73/3.26  tff(c_8382, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2773, c_76, c_8378])).
% 9.73/3.26  tff(c_13295, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13268, c_8382])).
% 9.73/3.26  tff(c_13296, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13268, c_8371])).
% 9.73/3.26  tff(c_8650, plain, (![A_620]: (m1_subset_1(A_620, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_620), k2_relat_1(A_620)))) | ~v1_funct_1(A_620) | ~v1_relat_1(A_620))), inference(cnfTransformation, [status(thm)], [f_143])).
% 9.73/3.26  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.73/3.26  tff(c_8700, plain, (![A_620]: (r1_tarski(A_620, k2_zfmisc_1(k1_relat_1(A_620), k2_relat_1(A_620))) | ~v1_funct_1(A_620) | ~v1_relat_1(A_620))), inference(resolution, [status(thm)], [c_8650, c_14])).
% 9.73/3.26  tff(c_13336, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13296, c_8700])).
% 9.73/3.26  tff(c_13353, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2773, c_76, c_13336])).
% 9.73/3.26  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.73/3.26  tff(c_8831, plain, (![C_624, A_625]: (k1_xboole_0=C_624 | ~v1_funct_2(C_624, A_625, k1_xboole_0) | k1_xboole_0=A_625 | ~m1_subset_1(C_624, k1_zfmisc_1(k2_zfmisc_1(A_625, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.73/3.26  tff(c_8840, plain, (![A_8, A_625]: (k1_xboole_0=A_8 | ~v1_funct_2(A_8, A_625, k1_xboole_0) | k1_xboole_0=A_625 | ~r1_tarski(A_8, k2_zfmisc_1(A_625, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_8831])).
% 9.73/3.26  tff(c_13945, plain, (![A_798, A_799]: (A_798='#skF_1' | ~v1_funct_2(A_798, A_799, '#skF_1') | A_799='#skF_1' | ~r1_tarski(A_798, k2_zfmisc_1(A_799, '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_12301, c_12301, c_12301, c_12301, c_8840])).
% 9.73/3.26  tff(c_13948, plain, ('#skF_3'='#skF_1' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_1') | k1_relat_1('#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_13353, c_13945])).
% 9.73/3.26  tff(c_13969, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13295, c_13948])).
% 9.73/3.26  tff(c_13970, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_13269, c_13969])).
% 9.73/3.26  tff(c_13999, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13970, c_13269])).
% 9.73/3.26  tff(c_14037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12326, c_13999])).
% 9.73/3.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.73/3.26  
% 9.73/3.26  Inference rules
% 9.73/3.26  ----------------------
% 9.73/3.26  #Ref     : 0
% 9.73/3.26  #Sup     : 2774
% 9.73/3.26  #Fact    : 0
% 9.73/3.26  #Define  : 0
% 9.73/3.26  #Split   : 69
% 9.73/3.26  #Chain   : 0
% 9.73/3.26  #Close   : 0
% 9.73/3.26  
% 9.73/3.26  Ordering : KBO
% 9.73/3.26  
% 9.73/3.26  Simplification rules
% 9.73/3.26  ----------------------
% 9.73/3.26  #Subsume      : 482
% 9.73/3.26  #Demod        : 3716
% 9.73/3.26  #Tautology    : 1332
% 9.73/3.26  #SimpNegUnit  : 35
% 9.73/3.26  #BackRed      : 620
% 9.73/3.26  
% 9.73/3.26  #Partial instantiations: 0
% 9.73/3.26  #Strategies tried      : 1
% 9.73/3.26  
% 9.73/3.26  Timing (in seconds)
% 9.73/3.26  ----------------------
% 9.73/3.27  Preprocessing        : 0.36
% 9.73/3.27  Parsing              : 0.20
% 9.73/3.27  CNF conversion       : 0.02
% 9.73/3.27  Main loop            : 2.07
% 9.73/3.27  Inferencing          : 0.63
% 9.73/3.27  Reduction            : 0.77
% 9.73/3.27  Demodulation         : 0.55
% 9.73/3.27  BG Simplification    : 0.06
% 9.73/3.27  Subsumption          : 0.44
% 9.73/3.27  Abstraction          : 0.08
% 9.73/3.27  MUC search           : 0.00
% 9.73/3.27  Cooper               : 0.00
% 9.73/3.27  Total                : 2.48
% 9.73/3.27  Index Insertion      : 0.00
% 9.73/3.27  Index Deletion       : 0.00
% 9.73/3.27  Index Matching       : 0.00
% 9.73/3.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
