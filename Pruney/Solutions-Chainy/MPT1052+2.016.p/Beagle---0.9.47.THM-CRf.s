%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:11 EST 2020

% Result     : Theorem 8.45s
% Output     : CNFRefutation 8.91s
% Verified   : 
% Statistics : Number of formulae       :  258 (1693 expanded)
%              Number of leaves         :   44 ( 561 expanded)
%              Depth                    :   14
%              Number of atoms          :  459 (3812 expanded)
%              Number of equality atoms :  186 ( 934 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_102,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_140,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_144,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_140])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6971,plain,(
    ! [A_460,B_461] :
      ( r2_hidden('#skF_2'(A_460,B_461),B_461)
      | r1_xboole_0(A_460,B_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6986,plain,(
    ! [B_464,A_465] :
      ( ~ v1_xboole_0(B_464)
      | r1_xboole_0(A_465,B_464) ) ),
    inference(resolution,[status(thm)],[c_6971,c_2])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_7021,plain,(
    ! [A_470,B_471] :
      ( k4_xboole_0(A_470,B_471) = A_470
      | ~ v1_xboole_0(B_471) ) ),
    inference(resolution,[status(thm)],[c_6986,c_22])).

tff(c_7027,plain,(
    ! [A_470] : k4_xboole_0(A_470,k1_xboole_0) = A_470 ),
    inference(resolution,[status(thm)],[c_6,c_7021])).

tff(c_6951,plain,(
    ! [A_456,B_457] :
      ( v1_xboole_0(k1_funct_2(A_456,B_457))
      | ~ v1_xboole_0(B_457)
      | v1_xboole_0(A_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_76,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_128,plain,(
    ! [B_46,A_47] :
      ( ~ r2_hidden(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_128])).

tff(c_6958,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6951,c_132])).

tff(c_6960,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6958])).

tff(c_7325,plain,(
    ! [C_501,A_502,B_503] :
      ( m1_subset_1(C_501,k1_zfmisc_1(k2_zfmisc_1(A_502,B_503)))
      | ~ r2_hidden(C_501,k1_funct_2(A_502,B_503)) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7838,plain,(
    ! [C_535,A_536,B_537] :
      ( r1_tarski(C_535,k2_zfmisc_1(A_536,B_537))
      | ~ r2_hidden(C_535,k1_funct_2(A_536,B_537)) ) ),
    inference(resolution,[status(thm)],[c_7325,c_32])).

tff(c_7869,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_7838])).

tff(c_36,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( k1_relat_1(k2_zfmisc_1(A_22,B_23)) = A_22
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_80,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_74,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_145,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_190,plain,(
    ! [A_67,B_68] :
      ( v1_xboole_0(k1_funct_2(A_67,B_68))
      | ~ v1_xboole_0(B_68)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_197,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_190,c_132])).

tff(c_199,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_586,plain,(
    ! [C_116,A_117,B_118] :
      ( m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ r2_hidden(C_116,k1_funct_2(A_117,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_965,plain,(
    ! [C_147,A_148,B_149] :
      ( r1_tarski(C_147,k2_zfmisc_1(A_148,B_149))
      | ~ r2_hidden(C_147,k1_funct_2(A_148,B_149)) ) ),
    inference(resolution,[status(thm)],[c_586,c_32])).

tff(c_996,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_965])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( k2_relat_1(k2_zfmisc_1(A_22,B_23)) = B_23
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_668,plain,(
    ! [A_127,B_128] :
      ( r1_tarski(k2_relat_1(A_127),k2_relat_1(B_128))
      | ~ r1_tarski(A_127,B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_677,plain,(
    ! [A_127,B_23,A_22] :
      ( r1_tarski(k2_relat_1(A_127),B_23)
      | ~ r1_tarski(A_127,k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(A_127)
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_668])).

tff(c_4541,plain,(
    ! [A_317,B_318,A_319] :
      ( r1_tarski(k2_relat_1(A_317),B_318)
      | ~ r1_tarski(A_317,k2_zfmisc_1(A_319,B_318))
      | ~ v1_relat_1(A_317)
      | k1_xboole_0 = B_318
      | k1_xboole_0 = A_319 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_677])).

tff(c_4547,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_996,c_4541])).

tff(c_4562,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4547])).

tff(c_4568,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4562])).

tff(c_223,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_2'(A_75,B_76),B_76)
      | r1_xboole_0(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_233,plain,(
    ! [B_77,A_78] :
      ( ~ v1_xboole_0(B_77)
      | r1_xboole_0(A_78,B_77) ) ),
    inference(resolution,[status(thm)],[c_223,c_2])).

tff(c_248,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = A_82
      | ~ v1_xboole_0(B_83) ) ),
    inference(resolution,[status(thm)],[c_233,c_22])).

tff(c_254,plain,(
    ! [A_82] : k4_xboole_0(A_82,k1_xboole_0) = A_82 ),
    inference(resolution,[status(thm)],[c_6,c_248])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_116,plain,(
    ! [A_43,B_44] : v1_relat_1(k2_zfmisc_1(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_118,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_116])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_683,plain,(
    ! [A_127] :
      ( r1_tarski(k2_relat_1(A_127),k1_xboole_0)
      | ~ r1_tarski(A_127,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_668])).

tff(c_722,plain,(
    ! [A_132] :
      ( r1_tarski(k2_relat_1(A_132),k1_xboole_0)
      | ~ r1_tarski(A_132,k1_xboole_0)
      | ~ v1_relat_1(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_683])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_725,plain,(
    ! [A_132] :
      ( k4_xboole_0(k2_relat_1(A_132),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_132,k1_xboole_0)
      | ~ v1_relat_1(A_132) ) ),
    inference(resolution,[status(thm)],[c_722,c_18])).

tff(c_752,plain,(
    ! [A_135] :
      ( k2_relat_1(A_135) = k1_xboole_0
      | ~ r1_tarski(A_135,k1_xboole_0)
      | ~ v1_relat_1(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_725])).

tff(c_765,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) = k1_xboole_0
      | ~ v1_relat_1(A_11)
      | k4_xboole_0(A_11,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_752])).

tff(c_779,plain,(
    ! [A_136] :
      ( k2_relat_1(A_136) = k1_xboole_0
      | ~ v1_relat_1(A_136)
      | k1_xboole_0 != A_136 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_765])).

tff(c_792,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_80,c_779])).

tff(c_793,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_792])).

tff(c_4643,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4568,c_793])).

tff(c_4669,plain,(
    ! [A_82] : k4_xboole_0(A_82,'#skF_3') = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4568,c_254])).

tff(c_30,plain,(
    ! [B_17] : k2_zfmisc_1(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4677,plain,(
    ! [B_17] : k2_zfmisc_1('#skF_3',B_17) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4568,c_4568,c_30])).

tff(c_1000,plain,(
    k4_xboole_0('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_996,c_18])).

tff(c_4637,plain,(
    k4_xboole_0('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4568,c_1000])).

tff(c_5156,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4669,c_4677,c_4637])).

tff(c_5157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4643,c_5156])).

tff(c_5159,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4562])).

tff(c_794,plain,(
    ! [A_137,B_138] :
      ( r1_tarski(k1_relat_1(A_137),k1_relat_1(B_138))
      | ~ r1_tarski(A_137,B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_803,plain,(
    ! [A_137,A_22,B_23] :
      ( r1_tarski(k1_relat_1(A_137),A_22)
      | ~ r1_tarski(A_137,k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(A_137)
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_794])).

tff(c_5186,plain,(
    ! [A_338,A_339,B_340] :
      ( r1_tarski(k1_relat_1(A_338),A_339)
      | ~ r1_tarski(A_338,k2_zfmisc_1(A_339,B_340))
      | ~ v1_relat_1(A_338)
      | k1_xboole_0 = B_340
      | k1_xboole_0 = A_339 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_803])).

tff(c_5192,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_996,c_5186])).

tff(c_5207,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5192])).

tff(c_5208,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5159,c_5207])).

tff(c_5214,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5208])).

tff(c_5331,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5214,c_6])).

tff(c_5333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_5331])).

tff(c_5335,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5208])).

tff(c_399,plain,(
    ! [C_92,A_93,B_94] :
      ( v1_funct_2(C_92,A_93,B_94)
      | ~ r2_hidden(C_92,k1_funct_2(A_93,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_427,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_399])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1021,plain,(
    ! [A_150,B_151,C_152] :
      ( k1_relset_1(A_150,B_151,C_152) = k1_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2206,plain,(
    ! [A_204,B_205,A_206] :
      ( k1_relset_1(A_204,B_205,A_206) = k1_relat_1(A_206)
      | ~ r1_tarski(A_206,k2_zfmisc_1(A_204,B_205)) ) ),
    inference(resolution,[status(thm)],[c_34,c_1021])).

tff(c_2224,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_996,c_2206])).

tff(c_66,plain,(
    ! [C_37,A_35,B_36] :
      ( m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ r2_hidden(C_37,k1_funct_2(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2306,plain,(
    ! [B_212,A_213,C_214] :
      ( k1_xboole_0 = B_212
      | k1_relset_1(A_213,B_212,C_214) = A_213
      | ~ v1_funct_2(C_214,A_213,B_212)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_213,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6039,plain,(
    ! [B_375,A_376,C_377] :
      ( k1_xboole_0 = B_375
      | k1_relset_1(A_376,B_375,C_377) = A_376
      | ~ v1_funct_2(C_377,A_376,B_375)
      | ~ r2_hidden(C_377,k1_funct_2(A_376,B_375)) ) ),
    inference(resolution,[status(thm)],[c_66,c_2306])).

tff(c_6096,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_6039])).

tff(c_6111,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_2224,c_6096])).

tff(c_6113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_5335,c_6111])).

tff(c_6115,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6123,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6115,c_8])).

tff(c_6114,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_6119,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6114,c_8])).

tff(c_6141,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6123,c_6119])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6134,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6119,c_6119,c_48])).

tff(c_6156,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6141,c_6141,c_6134])).

tff(c_6150,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6141,c_76])).

tff(c_6130,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6119,c_6119,c_28])).

tff(c_6223,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6141,c_6141,c_6130])).

tff(c_6745,plain,(
    ! [C_438,A_439,B_440] :
      ( m1_subset_1(C_438,k1_zfmisc_1(k2_zfmisc_1(A_439,B_440)))
      | ~ r2_hidden(C_438,k1_funct_2(A_439,B_440)) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6756,plain,(
    ! [C_441,A_442] :
      ( m1_subset_1(C_441,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(C_441,k1_funct_2(A_442,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6223,c_6745])).

tff(c_6781,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6150,c_6756])).

tff(c_6787,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_6781,c_32])).

tff(c_6127,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = '#skF_3'
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6119,c_18])).

tff(c_6296,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = '#skF_4'
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6141,c_6127])).

tff(c_6791,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6787,c_6296])).

tff(c_6166,plain,(
    ! [A_378,B_379] :
      ( r2_hidden('#skF_2'(A_378,B_379),B_379)
      | r1_xboole_0(A_378,B_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6252,plain,(
    ! [B_387,A_388] :
      ( ~ v1_xboole_0(B_387)
      | r1_xboole_0(A_388,B_387) ) ),
    inference(resolution,[status(thm)],[c_6166,c_2])).

tff(c_6262,plain,(
    ! [A_391,B_392] :
      ( k4_xboole_0(A_391,B_392) = A_391
      | ~ v1_xboole_0(B_392) ) ),
    inference(resolution,[status(thm)],[c_6252,c_22])).

tff(c_6267,plain,(
    ! [A_391] : k4_xboole_0(A_391,'#skF_4') = A_391 ),
    inference(resolution,[status(thm)],[c_6115,c_6262])).

tff(c_6867,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6791,c_6267])).

tff(c_6148,plain,(
    k1_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6141,c_145])).

tff(c_6888,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6867,c_6148])).

tff(c_6896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6156,c_6888])).

tff(c_6898,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_7528,plain,(
    ! [A_521,B_522] :
      ( r1_tarski(k1_relat_1(A_521),k1_relat_1(B_522))
      | ~ r1_tarski(A_521,B_522)
      | ~ v1_relat_1(B_522)
      | ~ v1_relat_1(A_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_7540,plain,(
    ! [B_522] :
      ( r1_tarski('#skF_3',k1_relat_1(B_522))
      | ~ r1_tarski('#skF_5',B_522)
      | ~ v1_relat_1(B_522)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6898,c_7528])).

tff(c_7563,plain,(
    ! [B_523] :
      ( r1_tarski('#skF_3',k1_relat_1(B_523))
      | ~ r1_tarski('#skF_5',B_523)
      | ~ v1_relat_1(B_523) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_7540])).

tff(c_7569,plain,(
    ! [A_22,B_23] :
      ( r1_tarski('#skF_3',A_22)
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(k2_zfmisc_1(A_22,B_23))
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_7563])).

tff(c_10694,plain,(
    ! [A_668,B_669] :
      ( r1_tarski('#skF_3',A_668)
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(A_668,B_669))
      | k1_xboole_0 = B_669
      | k1_xboole_0 = A_668 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7569])).

tff(c_10712,plain,
    ( r1_tarski('#skF_3','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7869,c_10694])).

tff(c_10714,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10712])).

tff(c_10832,plain,(
    ! [B_17] : k2_zfmisc_1('#skF_3',B_17) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10714,c_10714,c_30])).

tff(c_7549,plain,(
    ! [A_521] :
      ( r1_tarski(k1_relat_1(A_521),k1_xboole_0)
      | ~ r1_tarski(A_521,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_521) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_7528])).

tff(c_7620,plain,(
    ! [A_525] :
      ( r1_tarski(k1_relat_1(A_525),k1_xboole_0)
      | ~ r1_tarski(A_525,k1_xboole_0)
      | ~ v1_relat_1(A_525) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_7549])).

tff(c_7626,plain,(
    ! [A_525] :
      ( k4_xboole_0(k1_relat_1(A_525),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_525,k1_xboole_0)
      | ~ v1_relat_1(A_525) ) ),
    inference(resolution,[status(thm)],[c_7620,c_18])).

tff(c_7645,plain,(
    ! [A_526] :
      ( k1_relat_1(A_526) = k1_xboole_0
      | ~ r1_tarski(A_526,k1_xboole_0)
      | ~ v1_relat_1(A_526) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7027,c_7626])).

tff(c_7661,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) = k1_xboole_0
      | ~ v1_relat_1(A_11)
      | k4_xboole_0(A_11,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_7645])).

tff(c_7692,plain,(
    ! [A_529] :
      ( k1_relat_1(A_529) = k1_xboole_0
      | ~ v1_relat_1(A_529)
      | k1_xboole_0 != A_529 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7027,c_7661])).

tff(c_7704,plain,(
    ! [A_20,B_21] :
      ( k1_relat_1(k2_zfmisc_1(A_20,B_21)) = k1_xboole_0
      | k2_zfmisc_1(A_20,B_21) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_7692])).

tff(c_8315,plain,(
    ! [B_576] :
      ( k4_xboole_0('#skF_3',k1_relat_1(B_576)) = k1_xboole_0
      | ~ r1_tarski('#skF_5',B_576)
      | ~ v1_relat_1(B_576) ) ),
    inference(resolution,[status(thm)],[c_7563,c_18])).

tff(c_8330,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(A_20,B_21))
      | ~ v1_relat_1(k2_zfmisc_1(A_20,B_21))
      | k2_zfmisc_1(A_20,B_21) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7704,c_8315])).

tff(c_8349,plain,(
    ! [A_20,B_21] :
      ( k1_xboole_0 = '#skF_3'
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(A_20,B_21))
      | k2_zfmisc_1(A_20,B_21) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7027,c_8330])).

tff(c_10567,plain,(
    ! [A_660,B_661] :
      ( ~ r1_tarski('#skF_5',k2_zfmisc_1(A_660,B_661))
      | k2_zfmisc_1(A_660,B_661) != k1_xboole_0 ) ),
    inference(splitLeft,[status(thm)],[c_8349])).

tff(c_10585,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7869,c_10567])).

tff(c_10719,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10714,c_10585])).

tff(c_10990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10832,c_10719])).

tff(c_10992,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10712])).

tff(c_6897,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_7386,plain,(
    ! [A_509,B_510] :
      ( r1_tarski(k2_relat_1(A_509),k2_relat_1(B_510))
      | ~ r1_tarski(A_509,B_510)
      | ~ v1_relat_1(B_510)
      | ~ v1_relat_1(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_7395,plain,(
    ! [A_509,B_23,A_22] :
      ( r1_tarski(k2_relat_1(A_509),B_23)
      | ~ r1_tarski(A_509,k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(A_509)
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_7386])).

tff(c_11372,plain,(
    ! [A_710,B_711,A_712] :
      ( r1_tarski(k2_relat_1(A_710),B_711)
      | ~ r1_tarski(A_710,k2_zfmisc_1(A_712,B_711))
      | ~ v1_relat_1(A_710)
      | k1_xboole_0 = B_711
      | k1_xboole_0 = A_712 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7395])).

tff(c_11376,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7869,c_11372])).

tff(c_11390,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_11376])).

tff(c_11391,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_10992,c_6897,c_11390])).

tff(c_11524,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11391,c_6])).

tff(c_11526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6960,c_11524])).

tff(c_11527,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8349])).

tff(c_7575,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_5',k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_7563])).

tff(c_7582,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_7575])).

tff(c_7614,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7582])).

tff(c_11596,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11527,c_7614])).

tff(c_11639,plain,(
    ! [B_17] : k2_zfmisc_1('#skF_3',B_17) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11527,c_11527,c_30])).

tff(c_11772,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11639,c_7869])).

tff(c_11774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11596,c_11772])).

tff(c_11775,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7582])).

tff(c_11782,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11775,c_18])).

tff(c_11785,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7027,c_11782])).

tff(c_7047,plain,(
    ! [A_473,B_474] :
      ( k1_funct_2(A_473,B_474) = k1_xboole_0
      | ~ v1_xboole_0(B_474)
      | v1_xboole_0(A_473) ) ),
    inference(resolution,[status(thm)],[c_6951,c_8])).

tff(c_7054,plain,(
    ! [A_475] :
      ( k1_funct_2(A_475,k1_xboole_0) = k1_xboole_0
      | v1_xboole_0(A_475) ) ),
    inference(resolution,[status(thm)],[c_6,c_7047])).

tff(c_6961,plain,(
    ! [A_458,B_459] :
      ( r2_hidden('#skF_2'(A_458,B_459),A_458)
      | r1_xboole_0(A_458,B_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6981,plain,(
    ! [A_462,B_463] :
      ( ~ v1_xboole_0(A_462)
      | r1_xboole_0(A_462,B_463) ) ),
    inference(resolution,[status(thm)],[c_6961,c_2])).

tff(c_6985,plain,(
    ! [A_462,B_463] :
      ( k4_xboole_0(A_462,B_463) = A_462
      | ~ v1_xboole_0(A_462) ) ),
    inference(resolution,[status(thm)],[c_6981,c_22])).

tff(c_7196,plain,(
    ! [A_485,B_486] :
      ( k4_xboole_0(A_485,B_486) = A_485
      | k1_funct_2(A_485,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7054,c_6985])).

tff(c_6910,plain,(
    ! [A_445,B_446] :
      ( r1_tarski(A_445,B_446)
      | k4_xboole_0(A_445,B_446) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6917,plain,(
    k4_xboole_0(k2_relat_1('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6910,c_6897])).

tff(c_7209,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_funct_2(k2_relat_1('#skF_5'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7196,c_6917])).

tff(c_7232,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7209])).

tff(c_7401,plain,(
    ! [A_509] :
      ( r1_tarski(k2_relat_1(A_509),k1_xboole_0)
      | ~ r1_tarski(A_509,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_509) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_7386])).

tff(c_7469,plain,(
    ! [A_518] :
      ( r1_tarski(k2_relat_1(A_518),k1_xboole_0)
      | ~ r1_tarski(A_518,k1_xboole_0)
      | ~ v1_relat_1(A_518) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_7401])).

tff(c_7472,plain,(
    ! [A_518] :
      ( k4_xboole_0(k2_relat_1(A_518),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_518,k1_xboole_0)
      | ~ v1_relat_1(A_518) ) ),
    inference(resolution,[status(thm)],[c_7469,c_18])).

tff(c_7485,plain,(
    ! [A_519] :
      ( k2_relat_1(A_519) = k1_xboole_0
      | ~ r1_tarski(A_519,k1_xboole_0)
      | ~ v1_relat_1(A_519) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7027,c_7472])).

tff(c_7498,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) = k1_xboole_0
      | ~ v1_relat_1(A_11)
      | k4_xboole_0(A_11,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_7485])).

tff(c_7512,plain,(
    ! [A_520] :
      ( k2_relat_1(A_520) = k1_xboole_0
      | ~ v1_relat_1(A_520)
      | k1_xboole_0 != A_520 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7027,c_7498])).

tff(c_7521,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_80,c_7512])).

tff(c_7527,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_7232,c_7521])).

tff(c_11788,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11785,c_7527])).

tff(c_11776,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7582])).

tff(c_11847,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11785,c_11776])).

tff(c_12197,plain,(
    ! [A_742,B_743] :
      ( k4_xboole_0(A_742,B_743) = '#skF_3'
      | ~ r1_tarski(A_742,B_743) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11785,c_18])).

tff(c_12219,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11847,c_12197])).

tff(c_11820,plain,(
    ! [A_470] : k4_xboole_0(A_470,'#skF_3') = A_470 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11785,c_7027])).

tff(c_12235,plain,(
    '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_12219,c_11820])).

tff(c_12242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11788,c_12235])).

tff(c_12244,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7209])).

tff(c_12245,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12244,c_6917])).

tff(c_12249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_12245])).

tff(c_12251,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_6958])).

tff(c_12259,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12251,c_8])).

tff(c_12250,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6958])).

tff(c_12255,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_12250,c_8])).

tff(c_12288,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12259,c_12255])).

tff(c_12270,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12255,c_12255,c_46])).

tff(c_12318,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12288,c_12288,c_12270])).

tff(c_12297,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12288,c_76])).

tff(c_12267,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12255,c_12255,c_28])).

tff(c_12366,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12288,c_12288,c_12267])).

tff(c_12876,plain,(
    ! [C_809,A_810,B_811] :
      ( m1_subset_1(C_809,k1_zfmisc_1(k2_zfmisc_1(A_810,B_811)))
      | ~ r2_hidden(C_809,k1_funct_2(A_810,B_811)) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_12887,plain,(
    ! [C_812,A_813] :
      ( m1_subset_1(C_812,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(C_812,k1_funct_2(A_813,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12366,c_12876])).

tff(c_12908,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_12297,c_12887])).

tff(c_12914,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_12908,c_32])).

tff(c_12264,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = '#skF_3'
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12255,c_18])).

tff(c_12469,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = '#skF_4'
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12288,c_12264])).

tff(c_12918,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12914,c_12469])).

tff(c_12328,plain,(
    ! [A_748,B_749] :
      ( r2_hidden('#skF_2'(A_748,B_749),B_749)
      | r1_xboole_0(A_748,B_749) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12398,plain,(
    ! [B_756,A_757] :
      ( ~ v1_xboole_0(B_756)
      | r1_xboole_0(A_757,B_756) ) ),
    inference(resolution,[status(thm)],[c_12328,c_2])).

tff(c_12435,plain,(
    ! [A_762,B_763] :
      ( k4_xboole_0(A_762,B_763) = A_762
      | ~ v1_xboole_0(B_763) ) ),
    inference(resolution,[status(thm)],[c_12398,c_22])).

tff(c_12440,plain,(
    ! [A_762] : k4_xboole_0(A_762,'#skF_4') = A_762 ),
    inference(resolution,[status(thm)],[c_12251,c_12435])).

tff(c_12928,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_12918,c_12440])).

tff(c_12261,plain,(
    k4_xboole_0(k2_relat_1('#skF_5'),'#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12255,c_6917])).

tff(c_12403,plain,(
    k4_xboole_0(k2_relat_1('#skF_5'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12288,c_12261])).

tff(c_12442,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12440,c_12403])).

tff(c_12948,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12928,c_12442])).

tff(c_12959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12318,c_12948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.45/2.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.75/2.88  
% 8.75/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.75/2.89  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 8.75/2.89  
% 8.75/2.89  %Foreground sorts:
% 8.75/2.89  
% 8.75/2.89  
% 8.75/2.89  %Background operators:
% 8.75/2.89  
% 8.75/2.89  
% 8.75/2.89  %Foreground operators:
% 8.75/2.89  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 8.75/2.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.75/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.75/2.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.75/2.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.75/2.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.75/2.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.75/2.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.75/2.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.75/2.89  tff('#skF_5', type, '#skF_5': $i).
% 8.75/2.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.75/2.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.75/2.89  tff('#skF_3', type, '#skF_3': $i).
% 8.75/2.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.75/2.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.75/2.89  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 8.75/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.75/2.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.75/2.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.75/2.89  tff('#skF_4', type, '#skF_4': $i).
% 8.75/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.75/2.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.75/2.89  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 8.75/2.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.75/2.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.75/2.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.75/2.89  
% 8.91/2.92  tff(f_60, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.91/2.92  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.91/2.92  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.91/2.92  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.91/2.92  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.91/2.92  tff(f_64, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.91/2.92  tff(f_131, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 8.91/2.92  tff(f_152, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 8.91/2.92  tff(f_139, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 8.91/2.92  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.91/2.92  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.91/2.92  tff(f_88, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 8.91/2.92  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 8.91/2.92  tff(f_70, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.91/2.92  tff(f_102, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.91/2.92  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.91/2.92  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.91/2.92  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.91/2.92  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.91/2.92  tff(c_140, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.91/2.92  tff(c_144, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_140])).
% 8.91/2.92  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.91/2.92  tff(c_6971, plain, (![A_460, B_461]: (r2_hidden('#skF_2'(A_460, B_461), B_461) | r1_xboole_0(A_460, B_461))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.91/2.92  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.91/2.92  tff(c_6986, plain, (![B_464, A_465]: (~v1_xboole_0(B_464) | r1_xboole_0(A_465, B_464))), inference(resolution, [status(thm)], [c_6971, c_2])).
% 8.91/2.92  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.91/2.92  tff(c_7021, plain, (![A_470, B_471]: (k4_xboole_0(A_470, B_471)=A_470 | ~v1_xboole_0(B_471))), inference(resolution, [status(thm)], [c_6986, c_22])).
% 8.91/2.92  tff(c_7027, plain, (![A_470]: (k4_xboole_0(A_470, k1_xboole_0)=A_470)), inference(resolution, [status(thm)], [c_6, c_7021])).
% 8.91/2.92  tff(c_6951, plain, (![A_456, B_457]: (v1_xboole_0(k1_funct_2(A_456, B_457)) | ~v1_xboole_0(B_457) | v1_xboole_0(A_456))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.91/2.92  tff(c_76, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.91/2.92  tff(c_128, plain, (![B_46, A_47]: (~r2_hidden(B_46, A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.91/2.92  tff(c_132, plain, (~v1_xboole_0(k1_funct_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_128])).
% 8.91/2.92  tff(c_6958, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_6951, c_132])).
% 8.91/2.92  tff(c_6960, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_6958])).
% 8.91/2.92  tff(c_7325, plain, (![C_501, A_502, B_503]: (m1_subset_1(C_501, k1_zfmisc_1(k2_zfmisc_1(A_502, B_503))) | ~r2_hidden(C_501, k1_funct_2(A_502, B_503)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.91/2.92  tff(c_32, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.91/2.92  tff(c_7838, plain, (![C_535, A_536, B_537]: (r1_tarski(C_535, k2_zfmisc_1(A_536, B_537)) | ~r2_hidden(C_535, k1_funct_2(A_536, B_537)))), inference(resolution, [status(thm)], [c_7325, c_32])).
% 8.91/2.92  tff(c_7869, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_7838])).
% 8.91/2.92  tff(c_36, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.91/2.92  tff(c_40, plain, (![A_22, B_23]: (k1_relat_1(k2_zfmisc_1(A_22, B_23))=A_22 | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.91/2.92  tff(c_80, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.91/2.92  tff(c_74, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_152])).
% 8.91/2.92  tff(c_145, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_74])).
% 8.91/2.92  tff(c_190, plain, (![A_67, B_68]: (v1_xboole_0(k1_funct_2(A_67, B_68)) | ~v1_xboole_0(B_68) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.91/2.92  tff(c_197, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_190, c_132])).
% 8.91/2.92  tff(c_199, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_197])).
% 8.91/2.92  tff(c_586, plain, (![C_116, A_117, B_118]: (m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~r2_hidden(C_116, k1_funct_2(A_117, B_118)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.91/2.92  tff(c_965, plain, (![C_147, A_148, B_149]: (r1_tarski(C_147, k2_zfmisc_1(A_148, B_149)) | ~r2_hidden(C_147, k1_funct_2(A_148, B_149)))), inference(resolution, [status(thm)], [c_586, c_32])).
% 8.91/2.92  tff(c_996, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_965])).
% 8.91/2.92  tff(c_38, plain, (![A_22, B_23]: (k2_relat_1(k2_zfmisc_1(A_22, B_23))=B_23 | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.91/2.92  tff(c_668, plain, (![A_127, B_128]: (r1_tarski(k2_relat_1(A_127), k2_relat_1(B_128)) | ~r1_tarski(A_127, B_128) | ~v1_relat_1(B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.91/2.92  tff(c_677, plain, (![A_127, B_23, A_22]: (r1_tarski(k2_relat_1(A_127), B_23) | ~r1_tarski(A_127, k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(A_127) | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(superposition, [status(thm), theory('equality')], [c_38, c_668])).
% 8.91/2.92  tff(c_4541, plain, (![A_317, B_318, A_319]: (r1_tarski(k2_relat_1(A_317), B_318) | ~r1_tarski(A_317, k2_zfmisc_1(A_319, B_318)) | ~v1_relat_1(A_317) | k1_xboole_0=B_318 | k1_xboole_0=A_319)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_677])).
% 8.91/2.92  tff(c_4547, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~v1_relat_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_996, c_4541])).
% 8.91/2.92  tff(c_4562, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4547])).
% 8.91/2.92  tff(c_4568, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4562])).
% 8.91/2.92  tff(c_223, plain, (![A_75, B_76]: (r2_hidden('#skF_2'(A_75, B_76), B_76) | r1_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.91/2.92  tff(c_233, plain, (![B_77, A_78]: (~v1_xboole_0(B_77) | r1_xboole_0(A_78, B_77))), inference(resolution, [status(thm)], [c_223, c_2])).
% 8.91/2.92  tff(c_248, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=A_82 | ~v1_xboole_0(B_83))), inference(resolution, [status(thm)], [c_233, c_22])).
% 8.91/2.92  tff(c_254, plain, (![A_82]: (k4_xboole_0(A_82, k1_xboole_0)=A_82)), inference(resolution, [status(thm)], [c_6, c_248])).
% 8.91/2.92  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.91/2.92  tff(c_28, plain, (![A_16]: (k2_zfmisc_1(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.91/2.92  tff(c_116, plain, (![A_43, B_44]: (v1_relat_1(k2_zfmisc_1(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.91/2.92  tff(c_118, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_116])).
% 8.91/2.92  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.91/2.92  tff(c_683, plain, (![A_127]: (r1_tarski(k2_relat_1(A_127), k1_xboole_0) | ~r1_tarski(A_127, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_46, c_668])).
% 8.91/2.92  tff(c_722, plain, (![A_132]: (r1_tarski(k2_relat_1(A_132), k1_xboole_0) | ~r1_tarski(A_132, k1_xboole_0) | ~v1_relat_1(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_683])).
% 8.91/2.92  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.91/2.92  tff(c_725, plain, (![A_132]: (k4_xboole_0(k2_relat_1(A_132), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_132, k1_xboole_0) | ~v1_relat_1(A_132))), inference(resolution, [status(thm)], [c_722, c_18])).
% 8.91/2.92  tff(c_752, plain, (![A_135]: (k2_relat_1(A_135)=k1_xboole_0 | ~r1_tarski(A_135, k1_xboole_0) | ~v1_relat_1(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_725])).
% 8.91/2.92  tff(c_765, plain, (![A_11]: (k2_relat_1(A_11)=k1_xboole_0 | ~v1_relat_1(A_11) | k4_xboole_0(A_11, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_752])).
% 8.91/2.92  tff(c_779, plain, (![A_136]: (k2_relat_1(A_136)=k1_xboole_0 | ~v1_relat_1(A_136) | k1_xboole_0!=A_136)), inference(demodulation, [status(thm), theory('equality')], [c_254, c_765])).
% 8.91/2.92  tff(c_792, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_80, c_779])).
% 8.91/2.92  tff(c_793, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_792])).
% 8.91/2.92  tff(c_4643, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4568, c_793])).
% 8.91/2.92  tff(c_4669, plain, (![A_82]: (k4_xboole_0(A_82, '#skF_3')=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_4568, c_254])).
% 8.91/2.92  tff(c_30, plain, (![B_17]: (k2_zfmisc_1(k1_xboole_0, B_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.91/2.92  tff(c_4677, plain, (![B_17]: (k2_zfmisc_1('#skF_3', B_17)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4568, c_4568, c_30])).
% 8.91/2.92  tff(c_1000, plain, (k4_xboole_0('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_996, c_18])).
% 8.91/2.92  tff(c_4637, plain, (k4_xboole_0('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4568, c_1000])).
% 8.91/2.92  tff(c_5156, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4669, c_4677, c_4637])).
% 8.91/2.92  tff(c_5157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4643, c_5156])).
% 8.91/2.92  tff(c_5159, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4562])).
% 8.91/2.92  tff(c_794, plain, (![A_137, B_138]: (r1_tarski(k1_relat_1(A_137), k1_relat_1(B_138)) | ~r1_tarski(A_137, B_138) | ~v1_relat_1(B_138) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.91/2.92  tff(c_803, plain, (![A_137, A_22, B_23]: (r1_tarski(k1_relat_1(A_137), A_22) | ~r1_tarski(A_137, k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(A_137) | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(superposition, [status(thm), theory('equality')], [c_40, c_794])).
% 8.91/2.92  tff(c_5186, plain, (![A_338, A_339, B_340]: (r1_tarski(k1_relat_1(A_338), A_339) | ~r1_tarski(A_338, k2_zfmisc_1(A_339, B_340)) | ~v1_relat_1(A_338) | k1_xboole_0=B_340 | k1_xboole_0=A_339)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_803])).
% 8.91/2.92  tff(c_5192, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_996, c_5186])).
% 8.91/2.92  tff(c_5207, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5192])).
% 8.91/2.92  tff(c_5208, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5159, c_5207])).
% 8.91/2.92  tff(c_5214, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5208])).
% 8.91/2.92  tff(c_5331, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5214, c_6])).
% 8.91/2.92  tff(c_5333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_5331])).
% 8.91/2.92  tff(c_5335, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_5208])).
% 8.91/2.92  tff(c_399, plain, (![C_92, A_93, B_94]: (v1_funct_2(C_92, A_93, B_94) | ~r2_hidden(C_92, k1_funct_2(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.91/2.92  tff(c_427, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_399])).
% 8.91/2.92  tff(c_34, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.91/2.92  tff(c_1021, plain, (![A_150, B_151, C_152]: (k1_relset_1(A_150, B_151, C_152)=k1_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.91/2.92  tff(c_2206, plain, (![A_204, B_205, A_206]: (k1_relset_1(A_204, B_205, A_206)=k1_relat_1(A_206) | ~r1_tarski(A_206, k2_zfmisc_1(A_204, B_205)))), inference(resolution, [status(thm)], [c_34, c_1021])).
% 8.91/2.92  tff(c_2224, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_996, c_2206])).
% 8.91/2.92  tff(c_66, plain, (![C_37, A_35, B_36]: (m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~r2_hidden(C_37, k1_funct_2(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.91/2.92  tff(c_2306, plain, (![B_212, A_213, C_214]: (k1_xboole_0=B_212 | k1_relset_1(A_213, B_212, C_214)=A_213 | ~v1_funct_2(C_214, A_213, B_212) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_213, B_212))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.91/2.92  tff(c_6039, plain, (![B_375, A_376, C_377]: (k1_xboole_0=B_375 | k1_relset_1(A_376, B_375, C_377)=A_376 | ~v1_funct_2(C_377, A_376, B_375) | ~r2_hidden(C_377, k1_funct_2(A_376, B_375)))), inference(resolution, [status(thm)], [c_66, c_2306])).
% 8.91/2.92  tff(c_6096, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_6039])).
% 8.91/2.92  tff(c_6111, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_427, c_2224, c_6096])).
% 8.91/2.92  tff(c_6113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_5335, c_6111])).
% 8.91/2.92  tff(c_6115, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_197])).
% 8.91/2.92  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.91/2.92  tff(c_6123, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6115, c_8])).
% 8.91/2.92  tff(c_6114, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_197])).
% 8.91/2.92  tff(c_6119, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6114, c_8])).
% 8.91/2.92  tff(c_6141, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6123, c_6119])).
% 8.91/2.92  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.91/2.92  tff(c_6134, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6119, c_6119, c_48])).
% 8.91/2.92  tff(c_6156, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6141, c_6141, c_6134])).
% 8.91/2.92  tff(c_6150, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6141, c_76])).
% 8.91/2.92  tff(c_6130, plain, (![A_16]: (k2_zfmisc_1(A_16, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6119, c_6119, c_28])).
% 8.91/2.92  tff(c_6223, plain, (![A_16]: (k2_zfmisc_1(A_16, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6141, c_6141, c_6130])).
% 8.91/2.92  tff(c_6745, plain, (![C_438, A_439, B_440]: (m1_subset_1(C_438, k1_zfmisc_1(k2_zfmisc_1(A_439, B_440))) | ~r2_hidden(C_438, k1_funct_2(A_439, B_440)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.91/2.92  tff(c_6756, plain, (![C_441, A_442]: (m1_subset_1(C_441, k1_zfmisc_1('#skF_4')) | ~r2_hidden(C_441, k1_funct_2(A_442, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6223, c_6745])).
% 8.91/2.92  tff(c_6781, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_6150, c_6756])).
% 8.91/2.92  tff(c_6787, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_6781, c_32])).
% 8.91/2.92  tff(c_6127, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)='#skF_3' | ~r1_tarski(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_6119, c_18])).
% 8.91/2.92  tff(c_6296, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)='#skF_4' | ~r1_tarski(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_6141, c_6127])).
% 8.91/2.92  tff(c_6791, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6787, c_6296])).
% 8.91/2.92  tff(c_6166, plain, (![A_378, B_379]: (r2_hidden('#skF_2'(A_378, B_379), B_379) | r1_xboole_0(A_378, B_379))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.91/2.92  tff(c_6252, plain, (![B_387, A_388]: (~v1_xboole_0(B_387) | r1_xboole_0(A_388, B_387))), inference(resolution, [status(thm)], [c_6166, c_2])).
% 8.91/2.92  tff(c_6262, plain, (![A_391, B_392]: (k4_xboole_0(A_391, B_392)=A_391 | ~v1_xboole_0(B_392))), inference(resolution, [status(thm)], [c_6252, c_22])).
% 8.91/2.92  tff(c_6267, plain, (![A_391]: (k4_xboole_0(A_391, '#skF_4')=A_391)), inference(resolution, [status(thm)], [c_6115, c_6262])).
% 8.91/2.92  tff(c_6867, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6791, c_6267])).
% 8.91/2.92  tff(c_6148, plain, (k1_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6141, c_145])).
% 8.91/2.92  tff(c_6888, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6867, c_6148])).
% 8.91/2.92  tff(c_6896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6156, c_6888])).
% 8.91/2.92  tff(c_6898, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_74])).
% 8.91/2.92  tff(c_7528, plain, (![A_521, B_522]: (r1_tarski(k1_relat_1(A_521), k1_relat_1(B_522)) | ~r1_tarski(A_521, B_522) | ~v1_relat_1(B_522) | ~v1_relat_1(A_521))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.91/2.92  tff(c_7540, plain, (![B_522]: (r1_tarski('#skF_3', k1_relat_1(B_522)) | ~r1_tarski('#skF_5', B_522) | ~v1_relat_1(B_522) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6898, c_7528])).
% 8.91/2.92  tff(c_7563, plain, (![B_523]: (r1_tarski('#skF_3', k1_relat_1(B_523)) | ~r1_tarski('#skF_5', B_523) | ~v1_relat_1(B_523))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_7540])).
% 8.91/2.92  tff(c_7569, plain, (![A_22, B_23]: (r1_tarski('#skF_3', A_22) | ~r1_tarski('#skF_5', k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(k2_zfmisc_1(A_22, B_23)) | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(superposition, [status(thm), theory('equality')], [c_40, c_7563])).
% 8.91/2.92  tff(c_10694, plain, (![A_668, B_669]: (r1_tarski('#skF_3', A_668) | ~r1_tarski('#skF_5', k2_zfmisc_1(A_668, B_669)) | k1_xboole_0=B_669 | k1_xboole_0=A_668)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7569])).
% 8.91/2.92  tff(c_10712, plain, (r1_tarski('#skF_3', '#skF_3') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_7869, c_10694])).
% 8.91/2.92  tff(c_10714, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_10712])).
% 8.91/2.92  tff(c_10832, plain, (![B_17]: (k2_zfmisc_1('#skF_3', B_17)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10714, c_10714, c_30])).
% 8.91/2.92  tff(c_7549, plain, (![A_521]: (r1_tarski(k1_relat_1(A_521), k1_xboole_0) | ~r1_tarski(A_521, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_521))), inference(superposition, [status(thm), theory('equality')], [c_48, c_7528])).
% 8.91/2.92  tff(c_7620, plain, (![A_525]: (r1_tarski(k1_relat_1(A_525), k1_xboole_0) | ~r1_tarski(A_525, k1_xboole_0) | ~v1_relat_1(A_525))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_7549])).
% 8.91/2.92  tff(c_7626, plain, (![A_525]: (k4_xboole_0(k1_relat_1(A_525), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_525, k1_xboole_0) | ~v1_relat_1(A_525))), inference(resolution, [status(thm)], [c_7620, c_18])).
% 8.91/2.92  tff(c_7645, plain, (![A_526]: (k1_relat_1(A_526)=k1_xboole_0 | ~r1_tarski(A_526, k1_xboole_0) | ~v1_relat_1(A_526))), inference(demodulation, [status(thm), theory('equality')], [c_7027, c_7626])).
% 8.91/2.92  tff(c_7661, plain, (![A_11]: (k1_relat_1(A_11)=k1_xboole_0 | ~v1_relat_1(A_11) | k4_xboole_0(A_11, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_7645])).
% 8.91/2.92  tff(c_7692, plain, (![A_529]: (k1_relat_1(A_529)=k1_xboole_0 | ~v1_relat_1(A_529) | k1_xboole_0!=A_529)), inference(demodulation, [status(thm), theory('equality')], [c_7027, c_7661])).
% 8.91/2.92  tff(c_7704, plain, (![A_20, B_21]: (k1_relat_1(k2_zfmisc_1(A_20, B_21))=k1_xboole_0 | k2_zfmisc_1(A_20, B_21)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_7692])).
% 8.91/2.92  tff(c_8315, plain, (![B_576]: (k4_xboole_0('#skF_3', k1_relat_1(B_576))=k1_xboole_0 | ~r1_tarski('#skF_5', B_576) | ~v1_relat_1(B_576))), inference(resolution, [status(thm)], [c_7563, c_18])).
% 8.91/2.92  tff(c_8330, plain, (![A_20, B_21]: (k4_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0 | ~r1_tarski('#skF_5', k2_zfmisc_1(A_20, B_21)) | ~v1_relat_1(k2_zfmisc_1(A_20, B_21)) | k2_zfmisc_1(A_20, B_21)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7704, c_8315])).
% 8.91/2.92  tff(c_8349, plain, (![A_20, B_21]: (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_5', k2_zfmisc_1(A_20, B_21)) | k2_zfmisc_1(A_20, B_21)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7027, c_8330])).
% 8.91/2.92  tff(c_10567, plain, (![A_660, B_661]: (~r1_tarski('#skF_5', k2_zfmisc_1(A_660, B_661)) | k2_zfmisc_1(A_660, B_661)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8349])).
% 8.91/2.92  tff(c_10585, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_7869, c_10567])).
% 8.91/2.92  tff(c_10719, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10714, c_10585])).
% 8.91/2.92  tff(c_10990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10832, c_10719])).
% 8.91/2.92  tff(c_10992, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_10712])).
% 8.91/2.92  tff(c_6897, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 8.91/2.92  tff(c_7386, plain, (![A_509, B_510]: (r1_tarski(k2_relat_1(A_509), k2_relat_1(B_510)) | ~r1_tarski(A_509, B_510) | ~v1_relat_1(B_510) | ~v1_relat_1(A_509))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.91/2.92  tff(c_7395, plain, (![A_509, B_23, A_22]: (r1_tarski(k2_relat_1(A_509), B_23) | ~r1_tarski(A_509, k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(A_509) | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(superposition, [status(thm), theory('equality')], [c_38, c_7386])).
% 8.91/2.92  tff(c_11372, plain, (![A_710, B_711, A_712]: (r1_tarski(k2_relat_1(A_710), B_711) | ~r1_tarski(A_710, k2_zfmisc_1(A_712, B_711)) | ~v1_relat_1(A_710) | k1_xboole_0=B_711 | k1_xboole_0=A_712)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7395])).
% 8.91/2.92  tff(c_11376, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~v1_relat_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_7869, c_11372])).
% 8.91/2.92  tff(c_11390, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_11376])).
% 8.91/2.92  tff(c_11391, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_10992, c_6897, c_11390])).
% 8.91/2.92  tff(c_11524, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11391, c_6])).
% 8.91/2.92  tff(c_11526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6960, c_11524])).
% 8.91/2.92  tff(c_11527, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_8349])).
% 8.91/2.92  tff(c_7575, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_5', k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_7563])).
% 8.91/2.92  tff(c_7582, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_7575])).
% 8.91/2.92  tff(c_7614, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7582])).
% 8.91/2.92  tff(c_11596, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11527, c_7614])).
% 8.91/2.92  tff(c_11639, plain, (![B_17]: (k2_zfmisc_1('#skF_3', B_17)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11527, c_11527, c_30])).
% 8.91/2.92  tff(c_11772, plain, (r1_tarski('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11639, c_7869])).
% 8.91/2.92  tff(c_11774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11596, c_11772])).
% 8.91/2.92  tff(c_11775, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_7582])).
% 8.91/2.92  tff(c_11782, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_11775, c_18])).
% 8.91/2.92  tff(c_11785, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7027, c_11782])).
% 8.91/2.92  tff(c_7047, plain, (![A_473, B_474]: (k1_funct_2(A_473, B_474)=k1_xboole_0 | ~v1_xboole_0(B_474) | v1_xboole_0(A_473))), inference(resolution, [status(thm)], [c_6951, c_8])).
% 8.91/2.92  tff(c_7054, plain, (![A_475]: (k1_funct_2(A_475, k1_xboole_0)=k1_xboole_0 | v1_xboole_0(A_475))), inference(resolution, [status(thm)], [c_6, c_7047])).
% 8.91/2.92  tff(c_6961, plain, (![A_458, B_459]: (r2_hidden('#skF_2'(A_458, B_459), A_458) | r1_xboole_0(A_458, B_459))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.91/2.92  tff(c_6981, plain, (![A_462, B_463]: (~v1_xboole_0(A_462) | r1_xboole_0(A_462, B_463))), inference(resolution, [status(thm)], [c_6961, c_2])).
% 8.91/2.92  tff(c_6985, plain, (![A_462, B_463]: (k4_xboole_0(A_462, B_463)=A_462 | ~v1_xboole_0(A_462))), inference(resolution, [status(thm)], [c_6981, c_22])).
% 8.91/2.92  tff(c_7196, plain, (![A_485, B_486]: (k4_xboole_0(A_485, B_486)=A_485 | k1_funct_2(A_485, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7054, c_6985])).
% 8.91/2.92  tff(c_6910, plain, (![A_445, B_446]: (r1_tarski(A_445, B_446) | k4_xboole_0(A_445, B_446)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.91/2.92  tff(c_6917, plain, (k4_xboole_0(k2_relat_1('#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6910, c_6897])).
% 8.91/2.92  tff(c_7209, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_funct_2(k2_relat_1('#skF_5'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7196, c_6917])).
% 8.91/2.92  tff(c_7232, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7209])).
% 8.91/2.92  tff(c_7401, plain, (![A_509]: (r1_tarski(k2_relat_1(A_509), k1_xboole_0) | ~r1_tarski(A_509, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_509))), inference(superposition, [status(thm), theory('equality')], [c_46, c_7386])).
% 8.91/2.92  tff(c_7469, plain, (![A_518]: (r1_tarski(k2_relat_1(A_518), k1_xboole_0) | ~r1_tarski(A_518, k1_xboole_0) | ~v1_relat_1(A_518))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_7401])).
% 8.91/2.92  tff(c_7472, plain, (![A_518]: (k4_xboole_0(k2_relat_1(A_518), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_518, k1_xboole_0) | ~v1_relat_1(A_518))), inference(resolution, [status(thm)], [c_7469, c_18])).
% 8.91/2.92  tff(c_7485, plain, (![A_519]: (k2_relat_1(A_519)=k1_xboole_0 | ~r1_tarski(A_519, k1_xboole_0) | ~v1_relat_1(A_519))), inference(demodulation, [status(thm), theory('equality')], [c_7027, c_7472])).
% 8.91/2.92  tff(c_7498, plain, (![A_11]: (k2_relat_1(A_11)=k1_xboole_0 | ~v1_relat_1(A_11) | k4_xboole_0(A_11, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_7485])).
% 8.91/2.92  tff(c_7512, plain, (![A_520]: (k2_relat_1(A_520)=k1_xboole_0 | ~v1_relat_1(A_520) | k1_xboole_0!=A_520)), inference(demodulation, [status(thm), theory('equality')], [c_7027, c_7498])).
% 8.91/2.92  tff(c_7521, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_80, c_7512])).
% 8.91/2.92  tff(c_7527, plain, (k1_xboole_0!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_7232, c_7521])).
% 8.91/2.92  tff(c_11788, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11785, c_7527])).
% 8.91/2.92  tff(c_11776, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_7582])).
% 8.91/2.92  tff(c_11847, plain, (r1_tarski('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11785, c_11776])).
% 8.91/2.92  tff(c_12197, plain, (![A_742, B_743]: (k4_xboole_0(A_742, B_743)='#skF_3' | ~r1_tarski(A_742, B_743))), inference(demodulation, [status(thm), theory('equality')], [c_11785, c_18])).
% 8.91/2.92  tff(c_12219, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_11847, c_12197])).
% 8.91/2.92  tff(c_11820, plain, (![A_470]: (k4_xboole_0(A_470, '#skF_3')=A_470)), inference(demodulation, [status(thm), theory('equality')], [c_11785, c_7027])).
% 8.91/2.92  tff(c_12235, plain, ('#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_12219, c_11820])).
% 8.91/2.92  tff(c_12242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11788, c_12235])).
% 8.91/2.92  tff(c_12244, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7209])).
% 8.91/2.92  tff(c_12245, plain, (k4_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12244, c_6917])).
% 8.91/2.92  tff(c_12249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_12245])).
% 8.91/2.92  tff(c_12251, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_6958])).
% 8.91/2.92  tff(c_12259, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_12251, c_8])).
% 8.91/2.92  tff(c_12250, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_6958])).
% 8.91/2.92  tff(c_12255, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_12250, c_8])).
% 8.91/2.92  tff(c_12288, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12259, c_12255])).
% 8.91/2.92  tff(c_12270, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12255, c_12255, c_46])).
% 8.91/2.92  tff(c_12318, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12288, c_12288, c_12270])).
% 8.91/2.92  tff(c_12297, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12288, c_76])).
% 8.91/2.92  tff(c_12267, plain, (![A_16]: (k2_zfmisc_1(A_16, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12255, c_12255, c_28])).
% 8.91/2.92  tff(c_12366, plain, (![A_16]: (k2_zfmisc_1(A_16, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12288, c_12288, c_12267])).
% 8.91/2.92  tff(c_12876, plain, (![C_809, A_810, B_811]: (m1_subset_1(C_809, k1_zfmisc_1(k2_zfmisc_1(A_810, B_811))) | ~r2_hidden(C_809, k1_funct_2(A_810, B_811)))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.91/2.92  tff(c_12887, plain, (![C_812, A_813]: (m1_subset_1(C_812, k1_zfmisc_1('#skF_4')) | ~r2_hidden(C_812, k1_funct_2(A_813, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_12366, c_12876])).
% 8.91/2.92  tff(c_12908, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_12297, c_12887])).
% 8.91/2.92  tff(c_12914, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_12908, c_32])).
% 8.91/2.92  tff(c_12264, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)='#skF_3' | ~r1_tarski(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_12255, c_18])).
% 8.91/2.92  tff(c_12469, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)='#skF_4' | ~r1_tarski(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_12288, c_12264])).
% 8.91/2.92  tff(c_12918, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_12914, c_12469])).
% 8.91/2.92  tff(c_12328, plain, (![A_748, B_749]: (r2_hidden('#skF_2'(A_748, B_749), B_749) | r1_xboole_0(A_748, B_749))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.91/2.92  tff(c_12398, plain, (![B_756, A_757]: (~v1_xboole_0(B_756) | r1_xboole_0(A_757, B_756))), inference(resolution, [status(thm)], [c_12328, c_2])).
% 8.91/2.92  tff(c_12435, plain, (![A_762, B_763]: (k4_xboole_0(A_762, B_763)=A_762 | ~v1_xboole_0(B_763))), inference(resolution, [status(thm)], [c_12398, c_22])).
% 8.91/2.92  tff(c_12440, plain, (![A_762]: (k4_xboole_0(A_762, '#skF_4')=A_762)), inference(resolution, [status(thm)], [c_12251, c_12435])).
% 8.91/2.92  tff(c_12928, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_12918, c_12440])).
% 8.91/2.92  tff(c_12261, plain, (k4_xboole_0(k2_relat_1('#skF_5'), '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12255, c_6917])).
% 8.91/2.92  tff(c_12403, plain, (k4_xboole_0(k2_relat_1('#skF_5'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12288, c_12261])).
% 8.91/2.92  tff(c_12442, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12440, c_12403])).
% 8.91/2.92  tff(c_12948, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12928, c_12442])).
% 8.91/2.92  tff(c_12959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12318, c_12948])).
% 8.91/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.91/2.92  
% 8.91/2.92  Inference rules
% 8.91/2.92  ----------------------
% 8.91/2.92  #Ref     : 0
% 8.91/2.92  #Sup     : 2800
% 8.91/2.92  #Fact    : 4
% 8.91/2.92  #Define  : 0
% 8.91/2.92  #Split   : 29
% 8.91/2.92  #Chain   : 0
% 8.91/2.92  #Close   : 0
% 8.91/2.92  
% 8.91/2.92  Ordering : KBO
% 8.91/2.92  
% 8.91/2.92  Simplification rules
% 8.91/2.92  ----------------------
% 8.91/2.92  #Subsume      : 550
% 8.91/2.92  #Demod        : 3067
% 8.91/2.92  #Tautology    : 1390
% 8.91/2.92  #SimpNegUnit  : 123
% 8.91/2.92  #BackRed      : 715
% 8.91/2.92  
% 8.91/2.92  #Partial instantiations: 0
% 8.91/2.92  #Strategies tried      : 1
% 8.91/2.92  
% 8.91/2.92  Timing (in seconds)
% 8.91/2.92  ----------------------
% 8.91/2.92  Preprocessing        : 0.34
% 8.91/2.92  Parsing              : 0.18
% 8.91/2.92  CNF conversion       : 0.02
% 8.91/2.92  Main loop            : 1.76
% 8.91/2.92  Inferencing          : 0.58
% 8.91/2.92  Reduction            : 0.57
% 8.91/2.92  Demodulation         : 0.39
% 8.91/2.92  BG Simplification    : 0.06
% 8.91/2.92  Subsumption          : 0.41
% 8.91/2.92  Abstraction          : 0.07
% 8.91/2.92  MUC search           : 0.00
% 8.91/2.92  Cooper               : 0.00
% 8.91/2.92  Total                : 2.18
% 8.91/2.92  Index Insertion      : 0.00
% 8.91/2.92  Index Deletion       : 0.00
% 8.91/2.92  Index Matching       : 0.00
% 8.91/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
