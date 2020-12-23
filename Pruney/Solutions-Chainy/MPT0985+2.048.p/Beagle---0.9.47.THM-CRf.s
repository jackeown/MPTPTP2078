%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:33 EST 2020

% Result     : Theorem 10.35s
% Output     : CNFRefutation 10.87s
% Verified   : 
% Statistics : Number of formulae       :  403 (7327 expanded)
%              Number of leaves         :   47 (2503 expanded)
%              Depth                    :   25
%              Number of atoms          :  898 (21617 expanded)
%              Number of equality atoms :  162 (4533 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v8_relat_2 > v4_relat_2 > v3_relat_2 > v2_funct_1 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v3_relat_2,type,(
    v3_relat_2: $i > $o )).

tff(f_204,negated_conjecture,(
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

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_115,axiom,(
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

tff(f_168,axiom,(
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
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_187,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_158,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
      & v1_relat_1(B)
      & v4_relat_1(B,A)
      & v5_relat_1(B,A)
      & v1_relat_2(B)
      & v3_relat_2(B)
      & v4_relat_2(B)
      & v8_relat_2(B)
      & v1_partfun1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_partfun1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_108,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_4187,plain,(
    ! [C_326,A_327,B_328] :
      ( v1_relat_1(C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_327,B_328))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4204,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_4187])).

tff(c_4425,plain,(
    ! [C_352,A_353,B_354] :
      ( v4_relat_1(C_352,A_353)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4444,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_4425])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_112,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_42,plain,(
    ! [A_24] :
      ( v1_relat_1(k2_funct_1(A_24))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_106,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_104,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_4980,plain,(
    ! [A_397,B_398,C_399] :
      ( k2_relset_1(A_397,B_398,C_399) = k2_relat_1(C_399)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_397,B_398))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4989,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_4980])).

tff(c_5003,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_4989])).

tff(c_4733,plain,(
    ! [A_378] :
      ( k1_relat_1(k2_funct_1(A_378)) = k2_relat_1(A_378)
      | ~ v2_funct_1(A_378)
      | ~ v1_funct_1(A_378)
      | ~ v1_relat_1(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4263,plain,(
    ! [B_331,A_332] :
      ( v4_relat_1(B_331,A_332)
      | ~ r1_tarski(k1_relat_1(B_331),A_332)
      | ~ v1_relat_1(B_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4273,plain,(
    ! [B_331] :
      ( v4_relat_1(B_331,k1_relat_1(B_331))
      | ~ v1_relat_1(B_331) ) ),
    inference(resolution,[status(thm)],[c_6,c_4263])).

tff(c_5907,plain,(
    ! [A_466] :
      ( v4_relat_1(k2_funct_1(A_466),k2_relat_1(A_466))
      | ~ v1_relat_1(k2_funct_1(A_466))
      | ~ v2_funct_1(A_466)
      | ~ v1_funct_1(A_466)
      | ~ v1_relat_1(A_466) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4733,c_4273])).

tff(c_5913,plain,
    ( v4_relat_1(k2_funct_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5003,c_5907])).

tff(c_5927,plain,
    ( v4_relat_1(k2_funct_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_112,c_106,c_5913])).

tff(c_5934,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5927])).

tff(c_5937,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_5934])).

tff(c_5941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_112,c_5937])).

tff(c_5943,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5927])).

tff(c_50,plain,(
    ! [A_25] :
      ( k2_relat_1(k2_funct_1(A_25)) = k1_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_207,plain,(
    ! [A_62] :
      ( v1_funct_1(k2_funct_1(A_62))
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_102,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_205,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_210,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_207,c_205])).

tff(c_213,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_210])).

tff(c_247,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_253,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_247])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_253])).

tff(c_269,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_5942,plain,(
    v4_relat_1(k2_funct_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_5927])).

tff(c_6655,plain,(
    ! [A_504,A_505] :
      ( r1_tarski(k2_relat_1(A_504),A_505)
      | ~ v4_relat_1(k2_funct_1(A_504),A_505)
      | ~ v1_relat_1(k2_funct_1(A_504))
      | ~ v2_funct_1(A_504)
      | ~ v1_funct_1(A_504)
      | ~ v1_relat_1(A_504) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4733,c_22])).

tff(c_6764,plain,(
    ! [A_513] :
      ( r1_tarski(k2_relat_1(A_513),k1_relat_1(k2_funct_1(A_513)))
      | ~ v2_funct_1(A_513)
      | ~ v1_funct_1(A_513)
      | ~ v1_relat_1(A_513)
      | ~ v1_relat_1(k2_funct_1(A_513)) ) ),
    inference(resolution,[status(thm)],[c_4273,c_6655])).

tff(c_6790,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5003,c_6764])).

tff(c_6818,plain,(
    r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5943,c_4204,c_112,c_106,c_6790])).

tff(c_4377,plain,(
    ! [B_347,A_348] :
      ( r1_tarski(k1_relat_1(B_347),A_348)
      | ~ v4_relat_1(B_347,A_348)
      | ~ v1_relat_1(B_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4387,plain,(
    ! [B_347,A_348] :
      ( k1_relat_1(B_347) = A_348
      | ~ r1_tarski(A_348,k1_relat_1(B_347))
      | ~ v4_relat_1(B_347,A_348)
      | ~ v1_relat_1(B_347) ) ),
    inference(resolution,[status(thm)],[c_4377,c_2])).

tff(c_6828,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4'
    | ~ v4_relat_1(k2_funct_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_6818,c_4387])).

tff(c_6842,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5943,c_5942,c_6828])).

tff(c_84,plain,(
    ! [A_40] :
      ( m1_subset_1(A_40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40),k2_relat_1(A_40))))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_6888,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6842,c_84])).

tff(c_6930,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5943,c_269,c_6888])).

tff(c_56,plain,(
    ! [C_31,B_30,A_29] :
      ( v5_relat_1(C_31,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_7239,plain,(
    v5_relat_1(k2_funct_1('#skF_5'),k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_6930,c_56])).

tff(c_7254,plain,
    ( v5_relat_1(k2_funct_1('#skF_5'),k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_7239])).

tff(c_7261,plain,(
    v5_relat_1(k2_funct_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_112,c_106,c_7254])).

tff(c_4754,plain,(
    ! [A_379] :
      ( k2_relat_1(k2_funct_1(A_379)) = k1_relat_1(A_379)
      | ~ v2_funct_1(A_379)
      | ~ v1_funct_1(A_379)
      | ~ v1_relat_1(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4769,plain,(
    ! [A_379,A_15] :
      ( r1_tarski(k1_relat_1(A_379),A_15)
      | ~ v5_relat_1(k2_funct_1(A_379),A_15)
      | ~ v1_relat_1(k2_funct_1(A_379))
      | ~ v2_funct_1(A_379)
      | ~ v1_funct_1(A_379)
      | ~ v1_relat_1(A_379) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4754,c_26])).

tff(c_7248,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_7239,c_4769])).

tff(c_7257,plain,(
    r1_tarski(k1_relat_1('#skF_5'),k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_112,c_106,c_5943,c_7248])).

tff(c_4281,plain,(
    ! [B_335,A_336] :
      ( r1_tarski(k2_relat_1(B_335),A_336)
      | ~ v5_relat_1(B_335,A_336)
      | ~ v1_relat_1(B_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4287,plain,(
    ! [B_335,A_336] :
      ( k2_relat_1(B_335) = A_336
      | ~ r1_tarski(A_336,k2_relat_1(B_335))
      | ~ v5_relat_1(B_335,A_336)
      | ~ v1_relat_1(B_335) ) ),
    inference(resolution,[status(thm)],[c_4281,c_2])).

tff(c_7283,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = k1_relat_1('#skF_5')
    | ~ v5_relat_1(k2_funct_1('#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_7257,c_4287])).

tff(c_7303,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5943,c_7261,c_7283])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( v5_relat_1(B_16,A_15)
      | ~ r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7384,plain,(
    ! [A_15] :
      ( v5_relat_1(k2_funct_1('#skF_5'),A_15)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_15)
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7303,c_24])).

tff(c_7436,plain,(
    ! [A_15] :
      ( v5_relat_1(k2_funct_1('#skF_5'),A_15)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5943,c_7384])).

tff(c_86,plain,(
    ! [A_40] :
      ( v1_funct_2(A_40,k1_relat_1(A_40),k2_relat_1(A_40))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_6894,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6842,c_86])).

tff(c_6934,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5943,c_269,c_6894])).

tff(c_6949,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_6934])).

tff(c_6953,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_112,c_106,c_6949])).

tff(c_4793,plain,(
    ! [A_381] :
      ( m1_subset_1(A_381,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_381),k2_relat_1(A_381))))
      | ~ v1_funct_1(A_381)
      | ~ v1_relat_1(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_4810,plain,(
    ! [A_25] :
      ( m1_subset_1(k2_funct_1(A_25),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_25)),k1_relat_1(A_25))))
      | ~ v1_funct_1(k2_funct_1(A_25))
      | ~ v1_relat_1(k2_funct_1(A_25))
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_4793])).

tff(c_32,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4217,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4204,c_32])).

tff(c_4219,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4217])).

tff(c_5394,plain,(
    ! [B_440,D_441,A_442,C_443] :
      ( k1_xboole_0 = B_440
      | m1_subset_1(D_441,k1_zfmisc_1(k2_zfmisc_1(A_442,C_443)))
      | ~ r1_tarski(B_440,C_443)
      | ~ m1_subset_1(D_441,k1_zfmisc_1(k2_zfmisc_1(A_442,B_440)))
      | ~ v1_funct_2(D_441,A_442,B_440)
      | ~ v1_funct_1(D_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_8391,plain,(
    ! [B_563,D_564,A_565,A_566] :
      ( k2_relat_1(B_563) = k1_xboole_0
      | m1_subset_1(D_564,k1_zfmisc_1(k2_zfmisc_1(A_565,A_566)))
      | ~ m1_subset_1(D_564,k1_zfmisc_1(k2_zfmisc_1(A_565,k2_relat_1(B_563))))
      | ~ v1_funct_2(D_564,A_565,k2_relat_1(B_563))
      | ~ v1_funct_1(D_564)
      | ~ v5_relat_1(B_563,A_566)
      | ~ v1_relat_1(B_563) ) ),
    inference(resolution,[status(thm)],[c_26,c_5394])).

tff(c_8397,plain,(
    ! [D_564,A_565,A_566] :
      ( k2_relat_1(k2_funct_1('#skF_5')) = k1_xboole_0
      | m1_subset_1(D_564,k1_zfmisc_1(k2_zfmisc_1(A_565,A_566)))
      | ~ m1_subset_1(D_564,k1_zfmisc_1(k2_zfmisc_1(A_565,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_564,A_565,k2_relat_1(k2_funct_1('#skF_5')))
      | ~ v1_funct_1(D_564)
      | ~ v5_relat_1(k2_funct_1('#skF_5'),A_566)
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7303,c_8391])).

tff(c_8434,plain,(
    ! [D_564,A_565,A_566] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | m1_subset_1(D_564,k1_zfmisc_1(k2_zfmisc_1(A_565,A_566)))
      | ~ m1_subset_1(D_564,k1_zfmisc_1(k2_zfmisc_1(A_565,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_564,A_565,k1_relat_1('#skF_5'))
      | ~ v1_funct_1(D_564)
      | ~ v5_relat_1(k2_funct_1('#skF_5'),A_566) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5943,c_7303,c_7303,c_8397])).

tff(c_8467,plain,(
    ! [D_567,A_568,A_569] :
      ( m1_subset_1(D_567,k1_zfmisc_1(k2_zfmisc_1(A_568,A_569)))
      | ~ m1_subset_1(D_567,k1_zfmisc_1(k2_zfmisc_1(A_568,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_567,A_568,k1_relat_1('#skF_5'))
      | ~ v1_funct_1(D_567)
      | ~ v5_relat_1(k2_funct_1('#skF_5'),A_569) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4219,c_8434])).

tff(c_8470,plain,(
    ! [A_569] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),A_569)))
      | ~ v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),k1_relat_1('#skF_5'))
      | ~ v5_relat_1(k2_funct_1('#skF_5'),A_569)
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4810,c_8467])).

tff(c_8493,plain,(
    ! [A_570] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_570)))
      | ~ v5_relat_1(k2_funct_1('#skF_5'),A_570) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_112,c_106,c_5943,c_269,c_6953,c_6842,c_6842,c_8470])).

tff(c_268,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_312,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_8570,plain,(
    ~ v5_relat_1(k2_funct_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8493,c_312])).

tff(c_8583,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_7436,c_8570])).

tff(c_8589,plain,
    ( ~ v4_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_8583])).

tff(c_8593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_4444,c_8589])).

tff(c_8594,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4217])).

tff(c_349,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_366,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_349])).

tff(c_444,plain,(
    ! [C_93,A_94,B_95] :
      ( v4_relat_1(C_93,A_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_463,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_444])).

tff(c_756,plain,(
    ! [A_139,B_140,C_141] :
      ( k2_relset_1(A_139,B_140,C_141) = k2_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_762,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_756])).

tff(c_775,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_762])).

tff(c_629,plain,(
    ! [A_129] :
      ( k1_relat_1(k2_funct_1(A_129)) = k2_relat_1(A_129)
      | ~ v2_funct_1(A_129)
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_400,plain,(
    ! [B_84,A_85] :
      ( v4_relat_1(B_84,A_85)
      | ~ r1_tarski(k1_relat_1(B_84),A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_405,plain,(
    ! [B_84] :
      ( v4_relat_1(B_84,k1_relat_1(B_84))
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_400])).

tff(c_1891,plain,(
    ! [A_228] :
      ( v4_relat_1(k2_funct_1(A_228),k2_relat_1(A_228))
      | ~ v1_relat_1(k2_funct_1(A_228))
      | ~ v2_funct_1(A_228)
      | ~ v1_funct_1(A_228)
      | ~ v1_relat_1(A_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_405])).

tff(c_1897,plain,
    ( v4_relat_1(k2_funct_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_1891])).

tff(c_1908,plain,
    ( v4_relat_1(k2_funct_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_112,c_106,c_1897])).

tff(c_1913,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1908])).

tff(c_1917,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1913])).

tff(c_1921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_112,c_1917])).

tff(c_1923,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1908])).

tff(c_1922,plain,(
    v4_relat_1(k2_funct_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1908])).

tff(c_2500,plain,(
    ! [A_266,A_267] :
      ( r1_tarski(k2_relat_1(A_266),A_267)
      | ~ v4_relat_1(k2_funct_1(A_266),A_267)
      | ~ v1_relat_1(k2_funct_1(A_266))
      | ~ v2_funct_1(A_266)
      | ~ v1_funct_1(A_266)
      | ~ v1_relat_1(A_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_22])).

tff(c_2572,plain,(
    ! [A_271] :
      ( r1_tarski(k2_relat_1(A_271),k1_relat_1(k2_funct_1(A_271)))
      | ~ v2_funct_1(A_271)
      | ~ v1_funct_1(A_271)
      | ~ v1_relat_1(A_271)
      | ~ v1_relat_1(k2_funct_1(A_271)) ) ),
    inference(resolution,[status(thm)],[c_405,c_2500])).

tff(c_2597,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_2572])).

tff(c_2620,plain,(
    r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_366,c_112,c_106,c_2597])).

tff(c_532,plain,(
    ! [B_109,A_110] :
      ( r1_tarski(k1_relat_1(B_109),A_110)
      | ~ v4_relat_1(B_109,A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_539,plain,(
    ! [B_109,A_110] :
      ( k1_relat_1(B_109) = A_110
      | ~ r1_tarski(A_110,k1_relat_1(B_109))
      | ~ v4_relat_1(B_109,A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_532,c_2])).

tff(c_2632,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4'
    | ~ v4_relat_1(k2_funct_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2620,c_539])).

tff(c_2648,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_1922,c_2632])).

tff(c_2692,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2648,c_84])).

tff(c_2734,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_269,c_2692])).

tff(c_2901,plain,(
    v5_relat_1(k2_funct_1('#skF_5'),k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_2734,c_56])).

tff(c_2918,plain,
    ( v5_relat_1(k2_funct_1('#skF_5'),k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2901])).

tff(c_2925,plain,(
    v5_relat_1(k2_funct_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_112,c_106,c_2918])).

tff(c_707,plain,(
    ! [A_133] :
      ( k2_relat_1(k2_funct_1(A_133)) = k1_relat_1(A_133)
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_716,plain,(
    ! [A_133,A_15] :
      ( r1_tarski(k1_relat_1(A_133),A_15)
      | ~ v5_relat_1(k2_funct_1(A_133),A_15)
      | ~ v1_relat_1(k2_funct_1(A_133))
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_26])).

tff(c_2912,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2901,c_716])).

tff(c_2921,plain,(
    r1_tarski(k1_relat_1('#skF_5'),k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_112,c_106,c_1923,c_2912])).

tff(c_488,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(k2_relat_1(B_101),A_102)
      | ~ v5_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_498,plain,(
    ! [B_101,A_102] :
      ( k2_relat_1(B_101) = A_102
      | ~ r1_tarski(A_102,k2_relat_1(B_101))
      | ~ v5_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_488,c_2])).

tff(c_2969,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = k1_relat_1('#skF_5')
    | ~ v5_relat_1(k2_funct_1('#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2921,c_498])).

tff(c_2990,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_2925,c_2969])).

tff(c_3077,plain,(
    ! [A_15] :
      ( v5_relat_1(k2_funct_1('#skF_5'),A_15)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_15)
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2990,c_24])).

tff(c_3130,plain,(
    ! [A_15] :
      ( v5_relat_1(k2_funct_1('#skF_5'),A_15)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_3077])).

tff(c_2748,plain,(
    ! [A_272] :
      ( v1_funct_2(k2_funct_1(A_272),k1_relat_1(k2_funct_1(A_272)),k1_relat_1(A_272))
      | ~ v1_funct_1(k2_funct_1(A_272))
      | ~ v1_relat_1(k2_funct_1(A_272))
      | ~ v2_funct_1(A_272)
      | ~ v1_funct_1(A_272)
      | ~ v1_relat_1(A_272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_86])).

tff(c_2751,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2648,c_2748])).

tff(c_2762,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_112,c_106,c_1923,c_269,c_2751])).

tff(c_822,plain,(
    ! [A_145] :
      ( m1_subset_1(A_145,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_145),k2_relat_1(A_145))))
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_845,plain,(
    ! [A_25] :
      ( m1_subset_1(k2_funct_1(A_25),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_25)),k1_relat_1(A_25))))
      | ~ v1_funct_1(k2_funct_1(A_25))
      | ~ v1_relat_1(k2_funct_1(A_25))
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_822])).

tff(c_383,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_366,c_32])).

tff(c_385,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_1342,plain,(
    ! [B_191,D_192,A_193,C_194] :
      ( k1_xboole_0 = B_191
      | m1_subset_1(D_192,k1_zfmisc_1(k2_zfmisc_1(A_193,C_194)))
      | ~ r1_tarski(B_191,C_194)
      | ~ m1_subset_1(D_192,k1_zfmisc_1(k2_zfmisc_1(A_193,B_191)))
      | ~ v1_funct_2(D_192,A_193,B_191)
      | ~ v1_funct_1(D_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_3928,plain,(
    ! [B_314,D_315,A_316,A_317] :
      ( k2_relat_1(B_314) = k1_xboole_0
      | m1_subset_1(D_315,k1_zfmisc_1(k2_zfmisc_1(A_316,A_317)))
      | ~ m1_subset_1(D_315,k1_zfmisc_1(k2_zfmisc_1(A_316,k2_relat_1(B_314))))
      | ~ v1_funct_2(D_315,A_316,k2_relat_1(B_314))
      | ~ v1_funct_1(D_315)
      | ~ v5_relat_1(B_314,A_317)
      | ~ v1_relat_1(B_314) ) ),
    inference(resolution,[status(thm)],[c_26,c_1342])).

tff(c_3934,plain,(
    ! [D_315,A_316,A_317] :
      ( k2_relat_1(k2_funct_1('#skF_5')) = k1_xboole_0
      | m1_subset_1(D_315,k1_zfmisc_1(k2_zfmisc_1(A_316,A_317)))
      | ~ m1_subset_1(D_315,k1_zfmisc_1(k2_zfmisc_1(A_316,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_315,A_316,k2_relat_1(k2_funct_1('#skF_5')))
      | ~ v1_funct_1(D_315)
      | ~ v5_relat_1(k2_funct_1('#skF_5'),A_317)
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2990,c_3928])).

tff(c_3967,plain,(
    ! [D_315,A_316,A_317] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | m1_subset_1(D_315,k1_zfmisc_1(k2_zfmisc_1(A_316,A_317)))
      | ~ m1_subset_1(D_315,k1_zfmisc_1(k2_zfmisc_1(A_316,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_315,A_316,k1_relat_1('#skF_5'))
      | ~ v1_funct_1(D_315)
      | ~ v5_relat_1(k2_funct_1('#skF_5'),A_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_2990,c_2990,c_3934])).

tff(c_3993,plain,(
    ! [D_318,A_319,A_320] :
      ( m1_subset_1(D_318,k1_zfmisc_1(k2_zfmisc_1(A_319,A_320)))
      | ~ m1_subset_1(D_318,k1_zfmisc_1(k2_zfmisc_1(A_319,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_318,A_319,k1_relat_1('#skF_5'))
      | ~ v1_funct_1(D_318)
      | ~ v5_relat_1(k2_funct_1('#skF_5'),A_320) ) ),
    inference(negUnitSimplification,[status(thm)],[c_385,c_3967])).

tff(c_3996,plain,(
    ! [A_320] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),A_320)))
      | ~ v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),k1_relat_1('#skF_5'))
      | ~ v5_relat_1(k2_funct_1('#skF_5'),A_320)
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_845,c_3993])).

tff(c_4028,plain,(
    ! [A_321] :
      ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_321)))
      | ~ v5_relat_1(k2_funct_1('#skF_5'),A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_112,c_106,c_1923,c_269,c_2762,c_2648,c_2648,c_3996])).

tff(c_4111,plain,(
    ~ v5_relat_1(k2_funct_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4028,c_312])).

tff(c_4118,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3130,c_4111])).

tff(c_4124,plain,
    ( ~ v4_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_4118])).

tff(c_4128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_463,c_4124])).

tff(c_4129,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_4130,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_4158,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4129,c_4130])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_130,plain,(
    ! [A_53,B_54] : v1_relat_1(k2_zfmisc_1(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_132,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_130])).

tff(c_290,plain,(
    ! [A_76] :
      ( k2_relat_1(A_76) = k1_xboole_0
      | k1_relat_1(A_76) != k1_xboole_0
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_307,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_132,c_290])).

tff(c_313,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_4134,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4129,c_4129,c_313])).

tff(c_4165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4158,c_4134])).

tff(c_4166,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_8598,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8594,c_8594,c_4166])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8607,plain,(
    ! [A_5] : m1_subset_1('#skF_5',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8594,c_14])).

tff(c_9251,plain,(
    ! [A_632,B_633,C_634] :
      ( k2_relset_1(A_632,B_633,C_634) = k2_relat_1(C_634)
      | ~ m1_subset_1(C_634,k1_zfmisc_1(k2_zfmisc_1(A_632,B_633))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_9258,plain,(
    ! [A_632,B_633] : k2_relset_1(A_632,B_633,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8607,c_9251])).

tff(c_9268,plain,(
    ! [A_635,B_636] : k2_relset_1(A_635,B_636,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8598,c_9258])).

tff(c_9272,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9268,c_104])).

tff(c_8610,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_5',B_4) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8594,c_8594,c_12])).

tff(c_9306,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9272,c_9272,c_8610])).

tff(c_9316,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9272,c_312])).

tff(c_9497,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9306,c_9316])).

tff(c_9315,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9272,c_4204])).

tff(c_9321,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9272,c_112])).

tff(c_9320,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9272,c_106])).

tff(c_8595,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4217])).

tff(c_8616,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8594,c_8595])).

tff(c_9313,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9272,c_9272,c_8616])).

tff(c_9202,plain,(
    ! [A_627] :
      ( k2_relat_1(k2_funct_1(A_627)) = k1_relat_1(A_627)
      | ~ v2_funct_1(A_627)
      | ~ v1_funct_1(A_627)
      | ~ v1_relat_1(A_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8699,plain,(
    ! [B_575,A_576] :
      ( v5_relat_1(B_575,A_576)
      | ~ r1_tarski(k2_relat_1(B_575),A_576)
      | ~ v1_relat_1(B_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8709,plain,(
    ! [B_575] :
      ( v5_relat_1(B_575,k2_relat_1(B_575))
      | ~ v1_relat_1(B_575) ) ),
    inference(resolution,[status(thm)],[c_6,c_8699])).

tff(c_10519,plain,(
    ! [A_731] :
      ( v5_relat_1(k2_funct_1(A_731),k1_relat_1(A_731))
      | ~ v1_relat_1(k2_funct_1(A_731))
      | ~ v2_funct_1(A_731)
      | ~ v1_funct_1(A_731)
      | ~ v1_relat_1(A_731) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9202,c_8709])).

tff(c_10522,plain,
    ( v5_relat_1(k2_funct_1('#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9313,c_10519])).

tff(c_10527,plain,
    ( v5_relat_1(k2_funct_1('#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9315,c_9321,c_9320,c_10522])).

tff(c_10528,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10527])).

tff(c_10547,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_10528])).

tff(c_10551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9315,c_9321,c_10547])).

tff(c_10553,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10527])).

tff(c_9317,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9272,c_269])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8608,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8594,c_8594,c_10])).

tff(c_9308,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9272,c_9272,c_8608])).

tff(c_10552,plain,(
    v5_relat_1(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_10527])).

tff(c_8746,plain,(
    ! [C_583,B_584,A_585] :
      ( v5_relat_1(C_583,B_584)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(A_585,B_584))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8760,plain,(
    ! [B_584] : v5_relat_1('#skF_5',B_584) ),
    inference(resolution,[status(thm)],[c_8607,c_8746])).

tff(c_8816,plain,(
    ! [B_591,A_592] :
      ( r1_tarski(k2_relat_1(B_591),A_592)
      | ~ v5_relat_1(B_591,A_592)
      | ~ v1_relat_1(B_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8824,plain,(
    ! [A_592] :
      ( r1_tarski('#skF_5',A_592)
      | ~ v5_relat_1('#skF_5',A_592)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8598,c_8816])).

tff(c_8830,plain,(
    ! [A_593] : r1_tarski('#skF_5',A_593) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4204,c_8760,c_8824])).

tff(c_8833,plain,(
    ! [A_593] :
      ( A_593 = '#skF_5'
      | ~ r1_tarski(A_593,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8830,c_2])).

tff(c_9647,plain,(
    ! [A_656] :
      ( A_656 = '#skF_4'
      | ~ r1_tarski(A_656,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9272,c_9272,c_8833])).

tff(c_9666,plain,(
    ! [B_16] :
      ( k2_relat_1(B_16) = '#skF_4'
      | ~ v5_relat_1(B_16,'#skF_4')
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_26,c_9647])).

tff(c_10572,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_10552,c_9666])).

tff(c_10575,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10553,c_10572])).

tff(c_10604,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10575,c_84])).

tff(c_10648,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10553,c_9317,c_9308,c_10604])).

tff(c_10650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9497,c_10648])).

tff(c_10651,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_13902,plain,(
    ! [C_949,A_950,B_951] :
      ( v1_relat_1(C_949)
      | ~ m1_subset_1(C_949,k1_zfmisc_1(k2_zfmisc_1(A_950,B_951))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_13923,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_13902])).

tff(c_10652,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_13920,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10652,c_13902])).

tff(c_14151,plain,(
    ! [C_972,A_973,B_974] :
      ( v4_relat_1(C_972,A_973)
      | ~ m1_subset_1(C_972,k1_zfmisc_1(k2_zfmisc_1(A_973,B_974))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_14171,plain,(
    v4_relat_1(k2_funct_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10652,c_14151])).

tff(c_14859,plain,(
    ! [A_1036,B_1037,C_1038] :
      ( k2_relset_1(A_1036,B_1037,C_1038) = k2_relat_1(C_1038)
      | ~ m1_subset_1(C_1038,k1_zfmisc_1(k2_zfmisc_1(A_1036,B_1037))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_14871,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_14859])).

tff(c_14886,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_14871])).

tff(c_14177,plain,(
    ! [B_976,A_977] :
      ( v4_relat_1(B_976,A_977)
      | ~ r1_tarski(k1_relat_1(B_976),A_977)
      | ~ v1_relat_1(B_976) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14191,plain,(
    ! [B_976] :
      ( v4_relat_1(B_976,k1_relat_1(B_976))
      | ~ v1_relat_1(B_976) ) ),
    inference(resolution,[status(thm)],[c_6,c_14177])).

tff(c_14599,plain,(
    ! [A_1014] :
      ( k1_relat_1(k2_funct_1(A_1014)) = k2_relat_1(A_1014)
      | ~ v2_funct_1(A_1014)
      | ~ v1_funct_1(A_1014)
      | ~ v1_relat_1(A_1014) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_15941,plain,(
    ! [A_1112,A_1113] :
      ( r1_tarski(k2_relat_1(A_1112),A_1113)
      | ~ v4_relat_1(k2_funct_1(A_1112),A_1113)
      | ~ v1_relat_1(k2_funct_1(A_1112))
      | ~ v2_funct_1(A_1112)
      | ~ v1_funct_1(A_1112)
      | ~ v1_relat_1(A_1112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14599,c_22])).

tff(c_16586,plain,(
    ! [A_1140] :
      ( r1_tarski(k2_relat_1(A_1140),k1_relat_1(k2_funct_1(A_1140)))
      | ~ v2_funct_1(A_1140)
      | ~ v1_funct_1(A_1140)
      | ~ v1_relat_1(A_1140)
      | ~ v1_relat_1(k2_funct_1(A_1140)) ) ),
    inference(resolution,[status(thm)],[c_14191,c_15941])).

tff(c_16612,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14886,c_16586])).

tff(c_16640,plain,(
    r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13920,c_13923,c_112,c_106,c_16612])).

tff(c_14035,plain,(
    ! [B_959,A_960] :
      ( r1_tarski(k1_relat_1(B_959),A_960)
      | ~ v4_relat_1(B_959,A_960)
      | ~ v1_relat_1(B_959) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14041,plain,(
    ! [B_959,A_960] :
      ( k1_relat_1(B_959) = A_960
      | ~ r1_tarski(A_960,k1_relat_1(B_959))
      | ~ v4_relat_1(B_959,A_960)
      | ~ v1_relat_1(B_959) ) ),
    inference(resolution,[status(thm)],[c_14035,c_2])).

tff(c_16650,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4'
    | ~ v4_relat_1(k2_funct_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16640,c_14041])).

tff(c_16664,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13920,c_14171,c_16650])).

tff(c_14504,plain,(
    ! [A_1007] :
      ( k2_relat_1(k2_funct_1(A_1007)) = k1_relat_1(A_1007)
      | ~ v2_funct_1(A_1007)
      | ~ v1_funct_1(A_1007)
      | ~ v1_relat_1(A_1007) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_16771,plain,(
    ! [A_1141] :
      ( v1_funct_2(k2_funct_1(A_1141),k1_relat_1(k2_funct_1(A_1141)),k1_relat_1(A_1141))
      | ~ v1_funct_1(k2_funct_1(A_1141))
      | ~ v1_relat_1(k2_funct_1(A_1141))
      | ~ v2_funct_1(A_1141)
      | ~ v1_funct_1(A_1141)
      | ~ v1_relat_1(A_1141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14504,c_86])).

tff(c_16774,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16664,c_16771])).

tff(c_16788,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13923,c_112,c_106,c_13920,c_269,c_16774])).

tff(c_16704,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16664,c_84])).

tff(c_16745,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13920,c_269,c_16704])).

tff(c_16925,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_16745])).

tff(c_16945,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13923,c_112,c_106,c_16925])).

tff(c_13936,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_13923,c_32])).

tff(c_13983,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13936])).

tff(c_14093,plain,(
    ! [C_966,B_967,A_968] :
      ( v5_relat_1(C_966,B_967)
      | ~ m1_subset_1(C_966,k1_zfmisc_1(k2_zfmisc_1(A_968,B_967))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_14113,plain,(
    v5_relat_1(k2_funct_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10652,c_14093])).

tff(c_16208,plain,(
    ! [A_1127,A_1128] :
      ( r1_tarski(k1_relat_1(A_1127),A_1128)
      | ~ v5_relat_1(k2_funct_1(A_1127),A_1128)
      | ~ v1_relat_1(k2_funct_1(A_1127))
      | ~ v2_funct_1(A_1127)
      | ~ v1_funct_1(A_1127)
      | ~ v1_relat_1(A_1127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14504,c_26])).

tff(c_16224,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14113,c_16208])).

tff(c_16238,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13923,c_112,c_106,c_13920,c_16224])).

tff(c_96,plain,(
    ! [B_42,D_44,A_41,C_43] :
      ( k1_xboole_0 = B_42
      | v1_funct_2(D_44,A_41,C_43)
      | ~ r1_tarski(B_42,C_43)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_2(D_44,A_41,B_42)
      | ~ v1_funct_1(D_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_16243,plain,(
    ! [D_44,A_41] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | v1_funct_2(D_44,A_41,'#skF_3')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_41,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_44,A_41,k1_relat_1('#skF_5'))
      | ~ v1_funct_1(D_44) ) ),
    inference(resolution,[status(thm)],[c_16238,c_96])).

tff(c_16256,plain,(
    ! [D_44,A_41] :
      ( v1_funct_2(D_44,A_41,'#skF_3')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_41,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_44,A_41,k1_relat_1('#skF_5'))
      | ~ v1_funct_1(D_44) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13983,c_16243])).

tff(c_17188,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16945,c_16256])).

tff(c_17219,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_16788,c_17188])).

tff(c_17221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10651,c_17219])).

tff(c_17222,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13936])).

tff(c_10678,plain,(
    ! [C_735,A_736,B_737] :
      ( v1_relat_1(C_735)
      | ~ m1_subset_1(C_735,k1_zfmisc_1(k2_zfmisc_1(A_736,B_737))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10699,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_10678])).

tff(c_10696,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10652,c_10678])).

tff(c_11265,plain,(
    ! [A_808,B_809,C_810] :
      ( k2_relset_1(A_808,B_809,C_810) = k2_relat_1(C_810)
      | ~ m1_subset_1(C_810,k1_zfmisc_1(k2_zfmisc_1(A_808,B_809))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_11274,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_11265])).

tff(c_11288,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_11274])).

tff(c_11109,plain,(
    ! [A_794] :
      ( k1_relat_1(k2_funct_1(A_794)) = k2_relat_1(A_794)
      | ~ v2_funct_1(A_794)
      | ~ v1_funct_1(A_794)
      | ~ v1_relat_1(A_794) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12996,plain,(
    ! [A_925] :
      ( v1_funct_2(k2_funct_1(A_925),k2_relat_1(A_925),k2_relat_1(k2_funct_1(A_925)))
      | ~ v1_funct_1(k2_funct_1(A_925))
      | ~ v1_relat_1(k2_funct_1(A_925))
      | ~ v2_funct_1(A_925)
      | ~ v1_funct_1(A_925)
      | ~ v1_relat_1(A_925) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11109,c_86])).

tff(c_13008,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11288,c_12996])).

tff(c_13024,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10699,c_112,c_106,c_10696,c_269,c_13008])).

tff(c_13034,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_13024])).

tff(c_13038,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10699,c_112,c_106,c_13034])).

tff(c_10848,plain,(
    ! [C_754,A_755,B_756] :
      ( v4_relat_1(C_754,A_755)
      | ~ m1_subset_1(C_754,k1_zfmisc_1(k2_zfmisc_1(A_755,B_756))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10868,plain,(
    v4_relat_1(k2_funct_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10652,c_10848])).

tff(c_10874,plain,(
    ! [B_758,A_759] :
      ( v4_relat_1(B_758,A_759)
      | ~ r1_tarski(k1_relat_1(B_758),A_759)
      | ~ v1_relat_1(B_758) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10879,plain,(
    ! [B_758] :
      ( v4_relat_1(B_758,k1_relat_1(B_758))
      | ~ v1_relat_1(B_758) ) ),
    inference(resolution,[status(thm)],[c_6,c_10874])).

tff(c_12467,plain,(
    ! [A_897,A_898] :
      ( r1_tarski(k2_relat_1(A_897),A_898)
      | ~ v4_relat_1(k2_funct_1(A_897),A_898)
      | ~ v1_relat_1(k2_funct_1(A_897))
      | ~ v2_funct_1(A_897)
      | ~ v1_funct_1(A_897)
      | ~ v1_relat_1(A_897) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11109,c_22])).

tff(c_13129,plain,(
    ! [A_933] :
      ( r1_tarski(k2_relat_1(A_933),k1_relat_1(k2_funct_1(A_933)))
      | ~ v2_funct_1(A_933)
      | ~ v1_funct_1(A_933)
      | ~ v1_relat_1(A_933)
      | ~ v1_relat_1(k2_funct_1(A_933)) ) ),
    inference(resolution,[status(thm)],[c_10879,c_12467])).

tff(c_13154,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11288,c_13129])).

tff(c_13177,plain,(
    r1_tarski('#skF_4',k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10696,c_10699,c_112,c_106,c_13154])).

tff(c_10892,plain,(
    ! [B_765,A_766] :
      ( r1_tarski(k1_relat_1(B_765),A_766)
      | ~ v4_relat_1(B_765,A_766)
      | ~ v1_relat_1(B_765) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10899,plain,(
    ! [B_765,A_766] :
      ( k1_relat_1(B_765) = A_766
      | ~ r1_tarski(A_766,k1_relat_1(B_765))
      | ~ v4_relat_1(B_765,A_766)
      | ~ v1_relat_1(B_765) ) ),
    inference(resolution,[status(thm)],[c_10892,c_2])).

tff(c_13187,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4'
    | ~ v4_relat_1(k2_funct_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_13177,c_10899])).

tff(c_13202,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10696,c_10868,c_13187])).

tff(c_13265,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13202,c_84])).

tff(c_13310,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10696,c_269,c_13265])).

tff(c_13562,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_13310])).

tff(c_13582,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10699,c_112,c_106,c_13562])).

tff(c_10716,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_10699,c_32])).

tff(c_10718,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10716])).

tff(c_10807,plain,(
    ! [C_747,B_748,A_749] :
      ( v5_relat_1(C_747,B_748)
      | ~ m1_subset_1(C_747,k1_zfmisc_1(k2_zfmisc_1(A_749,B_748))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10827,plain,(
    v5_relat_1(k2_funct_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_10652,c_10807])).

tff(c_11016,plain,(
    ! [A_787] :
      ( k2_relat_1(k2_funct_1(A_787)) = k1_relat_1(A_787)
      | ~ v2_funct_1(A_787)
      | ~ v1_funct_1(A_787)
      | ~ v1_relat_1(A_787) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12869,plain,(
    ! [A_920,A_921] :
      ( r1_tarski(k1_relat_1(A_920),A_921)
      | ~ v5_relat_1(k2_funct_1(A_920),A_921)
      | ~ v1_relat_1(k2_funct_1(A_920))
      | ~ v2_funct_1(A_920)
      | ~ v1_funct_1(A_920)
      | ~ v1_relat_1(A_920) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11016,c_26])).

tff(c_12892,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10827,c_12869])).

tff(c_12904,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10699,c_112,c_106,c_10696,c_12892])).

tff(c_12910,plain,(
    ! [D_44,A_41] :
      ( k1_relat_1('#skF_5') = k1_xboole_0
      | v1_funct_2(D_44,A_41,'#skF_3')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_41,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_44,A_41,k1_relat_1('#skF_5'))
      | ~ v1_funct_1(D_44) ) ),
    inference(resolution,[status(thm)],[c_12904,c_96])).

tff(c_12924,plain,(
    ! [D_44,A_41] :
      ( v1_funct_2(D_44,A_41,'#skF_3')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_41,k1_relat_1('#skF_5'))))
      | ~ v1_funct_2(D_44,A_41,k1_relat_1('#skF_5'))
      | ~ v1_funct_1(D_44) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10718,c_12910])).

tff(c_13816,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_13582,c_12924])).

tff(c_13847,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_13038,c_13816])).

tff(c_13849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10651,c_13847])).

tff(c_13850,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10716])).

tff(c_13851,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10716])).

tff(c_13872,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13850,c_13851])).

tff(c_10653,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_13854,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13850,c_13850,c_10653])).

tff(c_13880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13872,c_13854])).

tff(c_13881,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_17228,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17222,c_17222,c_13881])).

tff(c_30,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_13937,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_13923,c_30])).

tff(c_13950,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13937])).

tff(c_17224,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17222,c_13950])).

tff(c_17270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17228,c_17224])).

tff(c_17271,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13937])).

tff(c_17272,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13937])).

tff(c_17293,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17271,c_17272])).

tff(c_17284,plain,(
    ! [A_5] : m1_subset_1('#skF_5',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17271,c_14])).

tff(c_18724,plain,(
    ! [A_1288,B_1289,C_1290] :
      ( k2_relset_1(A_1288,B_1289,C_1290) = k2_relat_1(C_1290)
      | ~ m1_subset_1(C_1290,k1_zfmisc_1(k2_zfmisc_1(A_1288,B_1289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_18731,plain,(
    ! [A_1288,B_1289] : k2_relset_1(A_1288,B_1289,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_17284,c_18724])).

tff(c_18745,plain,(
    ! [A_1291,B_1292] : k2_relset_1(A_1291,B_1292,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17293,c_18731])).

tff(c_18749,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_18745,c_104])).

tff(c_80,plain,(
    ! [A_38] : v1_relat_1('#skF_2'(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_177,plain,(
    ! [A_60] : m1_subset_1('#skF_2'(A_60),k1_zfmisc_1(k2_zfmisc_1(A_60,A_60))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_181,plain,(
    m1_subset_1('#skF_2'(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_177])).

tff(c_17281,plain,(
    m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17271,c_17271,c_181])).

tff(c_17285,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17271,c_17271,c_10])).

tff(c_18025,plain,(
    ! [C_1218,A_1219,B_1220] :
      ( v4_relat_1(C_1218,A_1219)
      | ~ m1_subset_1(C_1218,k1_zfmisc_1(k2_zfmisc_1(A_1219,B_1220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_18075,plain,(
    ! [C_1224,A_1225] :
      ( v4_relat_1(C_1224,A_1225)
      | ~ m1_subset_1(C_1224,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17285,c_18025])).

tff(c_18081,plain,(
    ! [A_1225] : v4_relat_1('#skF_2'('#skF_5'),A_1225) ),
    inference(resolution,[status(thm)],[c_17281,c_18075])).

tff(c_18039,plain,(
    ! [A_1219] : v4_relat_1('#skF_5',A_1219) ),
    inference(resolution,[status(thm)],[c_17284,c_18025])).

tff(c_13882,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_17274,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17271,c_17271,c_13882])).

tff(c_17962,plain,(
    ! [B_1210,A_1211] :
      ( r1_tarski(k1_relat_1(B_1210),A_1211)
      | ~ v4_relat_1(B_1210,A_1211)
      | ~ v1_relat_1(B_1210) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_17967,plain,(
    ! [A_1211] :
      ( r1_tarski('#skF_5',A_1211)
      | ~ v4_relat_1('#skF_5',A_1211)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17274,c_17962])).

tff(c_17970,plain,(
    ! [A_1211] :
      ( r1_tarski('#skF_5',A_1211)
      | ~ v4_relat_1('#skF_5',A_1211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13923,c_17967])).

tff(c_18046,plain,(
    ! [A_1222] : r1_tarski('#skF_5',A_1222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18039,c_17970])).

tff(c_18050,plain,(
    ! [A_1223] :
      ( A_1223 = '#skF_5'
      | ~ r1_tarski(A_1223,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18046,c_2])).

tff(c_18180,plain,(
    ! [B_1239] :
      ( k1_relat_1(B_1239) = '#skF_5'
      | ~ v4_relat_1(B_1239,'#skF_5')
      | ~ v1_relat_1(B_1239) ) ),
    inference(resolution,[status(thm)],[c_22,c_18050])).

tff(c_18184,plain,
    ( k1_relat_1('#skF_2'('#skF_5')) = '#skF_5'
    | ~ v1_relat_1('#skF_2'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_18081,c_18180])).

tff(c_18195,plain,(
    k1_relat_1('#skF_2'('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_18184])).

tff(c_187,plain,(
    ! [A_61] :
      ( k1_relat_1(A_61) != k1_xboole_0
      | k1_xboole_0 = A_61
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_203,plain,(
    ! [A_38] :
      ( k1_relat_1('#skF_2'(A_38)) != k1_xboole_0
      | '#skF_2'(A_38) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80,c_187])).

tff(c_17277,plain,(
    ! [A_38] :
      ( k1_relat_1('#skF_2'(A_38)) != '#skF_5'
      | '#skF_2'(A_38) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17271,c_17271,c_203])).

tff(c_18211,plain,(
    '#skF_2'('#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_18195,c_17277])).

tff(c_66,plain,(
    ! [A_38] : v1_partfun1('#skF_2'(A_38),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_18260,plain,(
    v1_partfun1('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18211,c_66])).

tff(c_18769,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18749,c_18749,c_18260])).

tff(c_18806,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18749,c_112])).

tff(c_19037,plain,(
    ! [A_1307] : m1_subset_1('#skF_4',k1_zfmisc_1(A_1307)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18749,c_17284])).

tff(c_62,plain,(
    ! [C_37,A_35,B_36] :
      ( v1_funct_2(C_37,A_35,B_36)
      | ~ v1_partfun1(C_37,A_35)
      | ~ v1_funct_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_19041,plain,(
    ! [A_35,B_36] :
      ( v1_funct_2('#skF_4',A_35,B_36)
      | ~ v1_partfun1('#skF_4',A_35)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_19037,c_62])).

tff(c_19292,plain,(
    ! [A_1329,B_1330] :
      ( v1_funct_2('#skF_4',A_1329,B_1330)
      | ~ v1_partfun1('#skF_4',A_1329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18806,c_19041])).

tff(c_17901,plain,(
    ! [A_1209] :
      ( k2_relat_1(k2_funct_1(A_1209)) = k1_relat_1(A_1209)
      | ~ v2_funct_1(A_1209)
      | ~ v1_funct_1(A_1209)
      | ~ v1_relat_1(A_1209) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_13949,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0
    | k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13920,c_30])).

tff(c_17422,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17271,c_17271,c_13949])).

tff(c_17423,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_17422])).

tff(c_17916,plain,
    ( k1_relat_1('#skF_5') != '#skF_5'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_17901,c_17423])).

tff(c_17926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13923,c_112,c_106,c_17274,c_17916])).

tff(c_17927,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_17422])).

tff(c_13948,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != k1_xboole_0
    | k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13920,c_32])).

tff(c_17408,plain,
    ( k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5'
    | k2_funct_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17271,c_17271,c_13948])).

tff(c_17409,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_17408])).

tff(c_17929,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17927,c_17409])).

tff(c_17936,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17274,c_17929])).

tff(c_17937,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_17408])).

tff(c_17941,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17937,c_10651])).

tff(c_18790,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18749,c_17941])).

tff(c_19295,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_19292,c_18790])).

tff(c_19299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18769,c_19295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:20:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.35/4.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.50/4.13  
% 10.50/4.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.50/4.13  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v8_relat_2 > v4_relat_2 > v3_relat_2 > v2_funct_1 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 10.50/4.13  
% 10.50/4.13  %Foreground sorts:
% 10.50/4.13  
% 10.50/4.13  
% 10.50/4.13  %Background operators:
% 10.50/4.13  
% 10.50/4.13  
% 10.50/4.13  %Foreground operators:
% 10.50/4.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.50/4.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.50/4.13  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.50/4.13  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.50/4.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.50/4.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.50/4.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.50/4.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.50/4.13  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 10.50/4.13  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 10.50/4.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.50/4.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.50/4.13  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 10.50/4.13  tff('#skF_5', type, '#skF_5': $i).
% 10.50/4.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.50/4.13  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.50/4.13  tff('#skF_3', type, '#skF_3': $i).
% 10.50/4.13  tff('#skF_1', type, '#skF_1': $i).
% 10.50/4.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.50/4.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.50/4.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.50/4.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.50/4.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.50/4.13  tff('#skF_4', type, '#skF_4': $i).
% 10.50/4.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.50/4.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.50/4.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.50/4.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.50/4.13  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 10.50/4.13  
% 10.87/4.17  tff(f_204, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 10.87/4.17  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.87/4.17  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.87/4.17  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 10.87/4.17  tff(f_99, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.87/4.17  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.87/4.17  tff(f_115, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 10.87/4.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.87/4.17  tff(f_168, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 10.87/4.17  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 10.87/4.17  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 10.87/4.17  tff(f_187, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 10.87/4.17  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.87/4.17  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.87/4.17  tff(f_82, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 10.87/4.17  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.87/4.17  tff(f_158, axiom, (![A]: (?[B]: ((((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_relat_2(B)) & v3_relat_2(B)) & v4_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_partfun1)).
% 10.87/4.17  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 10.87/4.17  tff(c_108, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 10.87/4.17  tff(c_4187, plain, (![C_326, A_327, B_328]: (v1_relat_1(C_326) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_327, B_328))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.87/4.17  tff(c_4204, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_4187])).
% 10.87/4.17  tff(c_4425, plain, (![C_352, A_353, B_354]: (v4_relat_1(C_352, A_353) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/4.17  tff(c_4444, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_108, c_4425])).
% 10.87/4.17  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.87/4.17  tff(c_112, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 10.87/4.17  tff(c_42, plain, (![A_24]: (v1_relat_1(k2_funct_1(A_24)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.87/4.17  tff(c_106, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 10.87/4.17  tff(c_104, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_204])).
% 10.87/4.17  tff(c_4980, plain, (![A_397, B_398, C_399]: (k2_relset_1(A_397, B_398, C_399)=k2_relat_1(C_399) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_397, B_398))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.87/4.17  tff(c_4989, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_4980])).
% 10.87/4.17  tff(c_5003, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_4989])).
% 10.87/4.17  tff(c_4733, plain, (![A_378]: (k1_relat_1(k2_funct_1(A_378))=k2_relat_1(A_378) | ~v2_funct_1(A_378) | ~v1_funct_1(A_378) | ~v1_relat_1(A_378))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.87/4.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.87/4.17  tff(c_4263, plain, (![B_331, A_332]: (v4_relat_1(B_331, A_332) | ~r1_tarski(k1_relat_1(B_331), A_332) | ~v1_relat_1(B_331))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.87/4.17  tff(c_4273, plain, (![B_331]: (v4_relat_1(B_331, k1_relat_1(B_331)) | ~v1_relat_1(B_331))), inference(resolution, [status(thm)], [c_6, c_4263])).
% 10.87/4.17  tff(c_5907, plain, (![A_466]: (v4_relat_1(k2_funct_1(A_466), k2_relat_1(A_466)) | ~v1_relat_1(k2_funct_1(A_466)) | ~v2_funct_1(A_466) | ~v1_funct_1(A_466) | ~v1_relat_1(A_466))), inference(superposition, [status(thm), theory('equality')], [c_4733, c_4273])).
% 10.87/4.17  tff(c_5913, plain, (v4_relat_1(k2_funct_1('#skF_5'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5003, c_5907])).
% 10.87/4.17  tff(c_5927, plain, (v4_relat_1(k2_funct_1('#skF_5'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_112, c_106, c_5913])).
% 10.87/4.17  tff(c_5934, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_5927])).
% 10.87/4.17  tff(c_5937, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_5934])).
% 10.87/4.17  tff(c_5941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4204, c_112, c_5937])).
% 10.87/4.17  tff(c_5943, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_5927])).
% 10.87/4.17  tff(c_50, plain, (![A_25]: (k2_relat_1(k2_funct_1(A_25))=k1_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.87/4.17  tff(c_207, plain, (![A_62]: (v1_funct_1(k2_funct_1(A_62)) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.87/4.17  tff(c_102, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 10.87/4.17  tff(c_205, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_102])).
% 10.87/4.17  tff(c_210, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_207, c_205])).
% 10.87/4.17  tff(c_213, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_210])).
% 10.87/4.17  tff(c_247, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.87/4.17  tff(c_253, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_247])).
% 10.87/4.17  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_213, c_253])).
% 10.87/4.17  tff(c_269, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_102])).
% 10.87/4.17  tff(c_5942, plain, (v4_relat_1(k2_funct_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_5927])).
% 10.87/4.17  tff(c_6655, plain, (![A_504, A_505]: (r1_tarski(k2_relat_1(A_504), A_505) | ~v4_relat_1(k2_funct_1(A_504), A_505) | ~v1_relat_1(k2_funct_1(A_504)) | ~v2_funct_1(A_504) | ~v1_funct_1(A_504) | ~v1_relat_1(A_504))), inference(superposition, [status(thm), theory('equality')], [c_4733, c_22])).
% 10.87/4.17  tff(c_6764, plain, (![A_513]: (r1_tarski(k2_relat_1(A_513), k1_relat_1(k2_funct_1(A_513))) | ~v2_funct_1(A_513) | ~v1_funct_1(A_513) | ~v1_relat_1(A_513) | ~v1_relat_1(k2_funct_1(A_513)))), inference(resolution, [status(thm)], [c_4273, c_6655])).
% 10.87/4.17  tff(c_6790, plain, (r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5003, c_6764])).
% 10.87/4.17  tff(c_6818, plain, (r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_5943, c_4204, c_112, c_106, c_6790])).
% 10.87/4.17  tff(c_4377, plain, (![B_347, A_348]: (r1_tarski(k1_relat_1(B_347), A_348) | ~v4_relat_1(B_347, A_348) | ~v1_relat_1(B_347))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.87/4.17  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.87/4.17  tff(c_4387, plain, (![B_347, A_348]: (k1_relat_1(B_347)=A_348 | ~r1_tarski(A_348, k1_relat_1(B_347)) | ~v4_relat_1(B_347, A_348) | ~v1_relat_1(B_347))), inference(resolution, [status(thm)], [c_4377, c_2])).
% 10.87/4.17  tff(c_6828, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4' | ~v4_relat_1(k2_funct_1('#skF_5'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_6818, c_4387])).
% 10.87/4.17  tff(c_6842, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5943, c_5942, c_6828])).
% 10.87/4.17  tff(c_84, plain, (![A_40]: (m1_subset_1(A_40, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40), k2_relat_1(A_40)))) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_168])).
% 10.87/4.17  tff(c_6888, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6842, c_84])).
% 10.87/4.17  tff(c_6930, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_5943, c_269, c_6888])).
% 10.87/4.17  tff(c_56, plain, (![C_31, B_30, A_29]: (v5_relat_1(C_31, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/4.17  tff(c_7239, plain, (v5_relat_1(k2_funct_1('#skF_5'), k2_relat_1(k2_funct_1('#skF_5')))), inference(resolution, [status(thm)], [c_6930, c_56])).
% 10.87/4.17  tff(c_7254, plain, (v5_relat_1(k2_funct_1('#skF_5'), k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_7239])).
% 10.87/4.17  tff(c_7261, plain, (v5_relat_1(k2_funct_1('#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_112, c_106, c_7254])).
% 10.87/4.17  tff(c_4754, plain, (![A_379]: (k2_relat_1(k2_funct_1(A_379))=k1_relat_1(A_379) | ~v2_funct_1(A_379) | ~v1_funct_1(A_379) | ~v1_relat_1(A_379))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.87/4.17  tff(c_26, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.87/4.17  tff(c_4769, plain, (![A_379, A_15]: (r1_tarski(k1_relat_1(A_379), A_15) | ~v5_relat_1(k2_funct_1(A_379), A_15) | ~v1_relat_1(k2_funct_1(A_379)) | ~v2_funct_1(A_379) | ~v1_funct_1(A_379) | ~v1_relat_1(A_379))), inference(superposition, [status(thm), theory('equality')], [c_4754, c_26])).
% 10.87/4.17  tff(c_7248, plain, (r1_tarski(k1_relat_1('#skF_5'), k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_7239, c_4769])).
% 10.87/4.17  tff(c_7257, plain, (r1_tarski(k1_relat_1('#skF_5'), k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_112, c_106, c_5943, c_7248])).
% 10.87/4.17  tff(c_4281, plain, (![B_335, A_336]: (r1_tarski(k2_relat_1(B_335), A_336) | ~v5_relat_1(B_335, A_336) | ~v1_relat_1(B_335))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.87/4.17  tff(c_4287, plain, (![B_335, A_336]: (k2_relat_1(B_335)=A_336 | ~r1_tarski(A_336, k2_relat_1(B_335)) | ~v5_relat_1(B_335, A_336) | ~v1_relat_1(B_335))), inference(resolution, [status(thm)], [c_4281, c_2])).
% 10.87/4.17  tff(c_7283, plain, (k2_relat_1(k2_funct_1('#skF_5'))=k1_relat_1('#skF_5') | ~v5_relat_1(k2_funct_1('#skF_5'), k1_relat_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_7257, c_4287])).
% 10.87/4.17  tff(c_7303, plain, (k2_relat_1(k2_funct_1('#skF_5'))=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5943, c_7261, c_7283])).
% 10.87/4.17  tff(c_24, plain, (![B_16, A_15]: (v5_relat_1(B_16, A_15) | ~r1_tarski(k2_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.87/4.17  tff(c_7384, plain, (![A_15]: (v5_relat_1(k2_funct_1('#skF_5'), A_15) | ~r1_tarski(k1_relat_1('#skF_5'), A_15) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_7303, c_24])).
% 10.87/4.17  tff(c_7436, plain, (![A_15]: (v5_relat_1(k2_funct_1('#skF_5'), A_15) | ~r1_tarski(k1_relat_1('#skF_5'), A_15))), inference(demodulation, [status(thm), theory('equality')], [c_5943, c_7384])).
% 10.87/4.17  tff(c_86, plain, (![A_40]: (v1_funct_2(A_40, k1_relat_1(A_40), k2_relat_1(A_40)) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_168])).
% 10.87/4.17  tff(c_6894, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6842, c_86])).
% 10.87/4.17  tff(c_6934, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_5943, c_269, c_6894])).
% 10.87/4.17  tff(c_6949, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_6934])).
% 10.87/4.17  tff(c_6953, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_112, c_106, c_6949])).
% 10.87/4.17  tff(c_4793, plain, (![A_381]: (m1_subset_1(A_381, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_381), k2_relat_1(A_381)))) | ~v1_funct_1(A_381) | ~v1_relat_1(A_381))), inference(cnfTransformation, [status(thm)], [f_168])).
% 10.87/4.17  tff(c_4810, plain, (![A_25]: (m1_subset_1(k2_funct_1(A_25), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_25)), k1_relat_1(A_25)))) | ~v1_funct_1(k2_funct_1(A_25)) | ~v1_relat_1(k2_funct_1(A_25)) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_50, c_4793])).
% 10.87/4.17  tff(c_32, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.87/4.17  tff(c_4217, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4204, c_32])).
% 10.87/4.17  tff(c_4219, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4217])).
% 10.87/4.17  tff(c_5394, plain, (![B_440, D_441, A_442, C_443]: (k1_xboole_0=B_440 | m1_subset_1(D_441, k1_zfmisc_1(k2_zfmisc_1(A_442, C_443))) | ~r1_tarski(B_440, C_443) | ~m1_subset_1(D_441, k1_zfmisc_1(k2_zfmisc_1(A_442, B_440))) | ~v1_funct_2(D_441, A_442, B_440) | ~v1_funct_1(D_441))), inference(cnfTransformation, [status(thm)], [f_187])).
% 10.87/4.17  tff(c_8391, plain, (![B_563, D_564, A_565, A_566]: (k2_relat_1(B_563)=k1_xboole_0 | m1_subset_1(D_564, k1_zfmisc_1(k2_zfmisc_1(A_565, A_566))) | ~m1_subset_1(D_564, k1_zfmisc_1(k2_zfmisc_1(A_565, k2_relat_1(B_563)))) | ~v1_funct_2(D_564, A_565, k2_relat_1(B_563)) | ~v1_funct_1(D_564) | ~v5_relat_1(B_563, A_566) | ~v1_relat_1(B_563))), inference(resolution, [status(thm)], [c_26, c_5394])).
% 10.87/4.17  tff(c_8397, plain, (![D_564, A_565, A_566]: (k2_relat_1(k2_funct_1('#skF_5'))=k1_xboole_0 | m1_subset_1(D_564, k1_zfmisc_1(k2_zfmisc_1(A_565, A_566))) | ~m1_subset_1(D_564, k1_zfmisc_1(k2_zfmisc_1(A_565, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_564, A_565, k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(D_564) | ~v5_relat_1(k2_funct_1('#skF_5'), A_566) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_7303, c_8391])).
% 10.87/4.17  tff(c_8434, plain, (![D_564, A_565, A_566]: (k1_relat_1('#skF_5')=k1_xboole_0 | m1_subset_1(D_564, k1_zfmisc_1(k2_zfmisc_1(A_565, A_566))) | ~m1_subset_1(D_564, k1_zfmisc_1(k2_zfmisc_1(A_565, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_564, A_565, k1_relat_1('#skF_5')) | ~v1_funct_1(D_564) | ~v5_relat_1(k2_funct_1('#skF_5'), A_566))), inference(demodulation, [status(thm), theory('equality')], [c_5943, c_7303, c_7303, c_8397])).
% 10.87/4.17  tff(c_8467, plain, (![D_567, A_568, A_569]: (m1_subset_1(D_567, k1_zfmisc_1(k2_zfmisc_1(A_568, A_569))) | ~m1_subset_1(D_567, k1_zfmisc_1(k2_zfmisc_1(A_568, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_567, A_568, k1_relat_1('#skF_5')) | ~v1_funct_1(D_567) | ~v5_relat_1(k2_funct_1('#skF_5'), A_569))), inference(negUnitSimplification, [status(thm)], [c_4219, c_8434])).
% 10.87/4.17  tff(c_8470, plain, (![A_569]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), A_569))) | ~v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), k1_relat_1('#skF_5')) | ~v5_relat_1(k2_funct_1('#skF_5'), A_569) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4810, c_8467])).
% 10.87/4.17  tff(c_8493, plain, (![A_570]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_570))) | ~v5_relat_1(k2_funct_1('#skF_5'), A_570))), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_112, c_106, c_5943, c_269, c_6953, c_6842, c_6842, c_8470])).
% 10.87/4.17  tff(c_268, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_102])).
% 10.87/4.17  tff(c_312, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_268])).
% 10.87/4.17  tff(c_8570, plain, (~v5_relat_1(k2_funct_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_8493, c_312])).
% 10.87/4.17  tff(c_8583, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_7436, c_8570])).
% 10.87/4.17  tff(c_8589, plain, (~v4_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_8583])).
% 10.87/4.17  tff(c_8593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4204, c_4444, c_8589])).
% 10.87/4.17  tff(c_8594, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_4217])).
% 10.87/4.17  tff(c_349, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.87/4.17  tff(c_366, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_349])).
% 10.87/4.17  tff(c_444, plain, (![C_93, A_94, B_95]: (v4_relat_1(C_93, A_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/4.17  tff(c_463, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_108, c_444])).
% 10.87/4.17  tff(c_756, plain, (![A_139, B_140, C_141]: (k2_relset_1(A_139, B_140, C_141)=k2_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.87/4.17  tff(c_762, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_756])).
% 10.87/4.17  tff(c_775, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_762])).
% 10.87/4.17  tff(c_629, plain, (![A_129]: (k1_relat_1(k2_funct_1(A_129))=k2_relat_1(A_129) | ~v2_funct_1(A_129) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.87/4.17  tff(c_400, plain, (![B_84, A_85]: (v4_relat_1(B_84, A_85) | ~r1_tarski(k1_relat_1(B_84), A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.87/4.17  tff(c_405, plain, (![B_84]: (v4_relat_1(B_84, k1_relat_1(B_84)) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_6, c_400])).
% 10.87/4.17  tff(c_1891, plain, (![A_228]: (v4_relat_1(k2_funct_1(A_228), k2_relat_1(A_228)) | ~v1_relat_1(k2_funct_1(A_228)) | ~v2_funct_1(A_228) | ~v1_funct_1(A_228) | ~v1_relat_1(A_228))), inference(superposition, [status(thm), theory('equality')], [c_629, c_405])).
% 10.87/4.17  tff(c_1897, plain, (v4_relat_1(k2_funct_1('#skF_5'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_775, c_1891])).
% 10.87/4.17  tff(c_1908, plain, (v4_relat_1(k2_funct_1('#skF_5'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_112, c_106, c_1897])).
% 10.87/4.17  tff(c_1913, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1908])).
% 10.87/4.17  tff(c_1917, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_1913])).
% 10.87/4.17  tff(c_1921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_366, c_112, c_1917])).
% 10.87/4.17  tff(c_1923, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1908])).
% 10.87/4.17  tff(c_1922, plain, (v4_relat_1(k2_funct_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_1908])).
% 10.87/4.17  tff(c_2500, plain, (![A_266, A_267]: (r1_tarski(k2_relat_1(A_266), A_267) | ~v4_relat_1(k2_funct_1(A_266), A_267) | ~v1_relat_1(k2_funct_1(A_266)) | ~v2_funct_1(A_266) | ~v1_funct_1(A_266) | ~v1_relat_1(A_266))), inference(superposition, [status(thm), theory('equality')], [c_629, c_22])).
% 10.87/4.17  tff(c_2572, plain, (![A_271]: (r1_tarski(k2_relat_1(A_271), k1_relat_1(k2_funct_1(A_271))) | ~v2_funct_1(A_271) | ~v1_funct_1(A_271) | ~v1_relat_1(A_271) | ~v1_relat_1(k2_funct_1(A_271)))), inference(resolution, [status(thm)], [c_405, c_2500])).
% 10.87/4.17  tff(c_2597, plain, (r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_775, c_2572])).
% 10.87/4.17  tff(c_2620, plain, (r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1923, c_366, c_112, c_106, c_2597])).
% 10.87/4.17  tff(c_532, plain, (![B_109, A_110]: (r1_tarski(k1_relat_1(B_109), A_110) | ~v4_relat_1(B_109, A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.87/4.17  tff(c_539, plain, (![B_109, A_110]: (k1_relat_1(B_109)=A_110 | ~r1_tarski(A_110, k1_relat_1(B_109)) | ~v4_relat_1(B_109, A_110) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_532, c_2])).
% 10.87/4.17  tff(c_2632, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4' | ~v4_relat_1(k2_funct_1('#skF_5'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_2620, c_539])).
% 10.87/4.17  tff(c_2648, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1923, c_1922, c_2632])).
% 10.87/4.17  tff(c_2692, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2648, c_84])).
% 10.87/4.17  tff(c_2734, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_1923, c_269, c_2692])).
% 10.87/4.17  tff(c_2901, plain, (v5_relat_1(k2_funct_1('#skF_5'), k2_relat_1(k2_funct_1('#skF_5')))), inference(resolution, [status(thm)], [c_2734, c_56])).
% 10.87/4.17  tff(c_2918, plain, (v5_relat_1(k2_funct_1('#skF_5'), k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_2901])).
% 10.87/4.17  tff(c_2925, plain, (v5_relat_1(k2_funct_1('#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_112, c_106, c_2918])).
% 10.87/4.17  tff(c_707, plain, (![A_133]: (k2_relat_1(k2_funct_1(A_133))=k1_relat_1(A_133) | ~v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.87/4.17  tff(c_716, plain, (![A_133, A_15]: (r1_tarski(k1_relat_1(A_133), A_15) | ~v5_relat_1(k2_funct_1(A_133), A_15) | ~v1_relat_1(k2_funct_1(A_133)) | ~v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(superposition, [status(thm), theory('equality')], [c_707, c_26])).
% 10.87/4.17  tff(c_2912, plain, (r1_tarski(k1_relat_1('#skF_5'), k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2901, c_716])).
% 10.87/4.17  tff(c_2921, plain, (r1_tarski(k1_relat_1('#skF_5'), k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_112, c_106, c_1923, c_2912])).
% 10.87/4.17  tff(c_488, plain, (![B_101, A_102]: (r1_tarski(k2_relat_1(B_101), A_102) | ~v5_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.87/4.17  tff(c_498, plain, (![B_101, A_102]: (k2_relat_1(B_101)=A_102 | ~r1_tarski(A_102, k2_relat_1(B_101)) | ~v5_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_488, c_2])).
% 10.87/4.17  tff(c_2969, plain, (k2_relat_1(k2_funct_1('#skF_5'))=k1_relat_1('#skF_5') | ~v5_relat_1(k2_funct_1('#skF_5'), k1_relat_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_2921, c_498])).
% 10.87/4.17  tff(c_2990, plain, (k2_relat_1(k2_funct_1('#skF_5'))=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1923, c_2925, c_2969])).
% 10.87/4.17  tff(c_3077, plain, (![A_15]: (v5_relat_1(k2_funct_1('#skF_5'), A_15) | ~r1_tarski(k1_relat_1('#skF_5'), A_15) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2990, c_24])).
% 10.87/4.17  tff(c_3130, plain, (![A_15]: (v5_relat_1(k2_funct_1('#skF_5'), A_15) | ~r1_tarski(k1_relat_1('#skF_5'), A_15))), inference(demodulation, [status(thm), theory('equality')], [c_1923, c_3077])).
% 10.87/4.17  tff(c_2748, plain, (![A_272]: (v1_funct_2(k2_funct_1(A_272), k1_relat_1(k2_funct_1(A_272)), k1_relat_1(A_272)) | ~v1_funct_1(k2_funct_1(A_272)) | ~v1_relat_1(k2_funct_1(A_272)) | ~v2_funct_1(A_272) | ~v1_funct_1(A_272) | ~v1_relat_1(A_272))), inference(superposition, [status(thm), theory('equality')], [c_707, c_86])).
% 10.87/4.17  tff(c_2751, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2648, c_2748])).
% 10.87/4.17  tff(c_2762, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_112, c_106, c_1923, c_269, c_2751])).
% 10.87/4.17  tff(c_822, plain, (![A_145]: (m1_subset_1(A_145, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_145), k2_relat_1(A_145)))) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_168])).
% 10.87/4.17  tff(c_845, plain, (![A_25]: (m1_subset_1(k2_funct_1(A_25), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_25)), k1_relat_1(A_25)))) | ~v1_funct_1(k2_funct_1(A_25)) | ~v1_relat_1(k2_funct_1(A_25)) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_50, c_822])).
% 10.87/4.17  tff(c_383, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_366, c_32])).
% 10.87/4.17  tff(c_385, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_383])).
% 10.87/4.17  tff(c_1342, plain, (![B_191, D_192, A_193, C_194]: (k1_xboole_0=B_191 | m1_subset_1(D_192, k1_zfmisc_1(k2_zfmisc_1(A_193, C_194))) | ~r1_tarski(B_191, C_194) | ~m1_subset_1(D_192, k1_zfmisc_1(k2_zfmisc_1(A_193, B_191))) | ~v1_funct_2(D_192, A_193, B_191) | ~v1_funct_1(D_192))), inference(cnfTransformation, [status(thm)], [f_187])).
% 10.87/4.17  tff(c_3928, plain, (![B_314, D_315, A_316, A_317]: (k2_relat_1(B_314)=k1_xboole_0 | m1_subset_1(D_315, k1_zfmisc_1(k2_zfmisc_1(A_316, A_317))) | ~m1_subset_1(D_315, k1_zfmisc_1(k2_zfmisc_1(A_316, k2_relat_1(B_314)))) | ~v1_funct_2(D_315, A_316, k2_relat_1(B_314)) | ~v1_funct_1(D_315) | ~v5_relat_1(B_314, A_317) | ~v1_relat_1(B_314))), inference(resolution, [status(thm)], [c_26, c_1342])).
% 10.87/4.17  tff(c_3934, plain, (![D_315, A_316, A_317]: (k2_relat_1(k2_funct_1('#skF_5'))=k1_xboole_0 | m1_subset_1(D_315, k1_zfmisc_1(k2_zfmisc_1(A_316, A_317))) | ~m1_subset_1(D_315, k1_zfmisc_1(k2_zfmisc_1(A_316, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_315, A_316, k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(D_315) | ~v5_relat_1(k2_funct_1('#skF_5'), A_317) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2990, c_3928])).
% 10.87/4.17  tff(c_3967, plain, (![D_315, A_316, A_317]: (k1_relat_1('#skF_5')=k1_xboole_0 | m1_subset_1(D_315, k1_zfmisc_1(k2_zfmisc_1(A_316, A_317))) | ~m1_subset_1(D_315, k1_zfmisc_1(k2_zfmisc_1(A_316, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_315, A_316, k1_relat_1('#skF_5')) | ~v1_funct_1(D_315) | ~v5_relat_1(k2_funct_1('#skF_5'), A_317))), inference(demodulation, [status(thm), theory('equality')], [c_1923, c_2990, c_2990, c_3934])).
% 10.87/4.17  tff(c_3993, plain, (![D_318, A_319, A_320]: (m1_subset_1(D_318, k1_zfmisc_1(k2_zfmisc_1(A_319, A_320))) | ~m1_subset_1(D_318, k1_zfmisc_1(k2_zfmisc_1(A_319, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_318, A_319, k1_relat_1('#skF_5')) | ~v1_funct_1(D_318) | ~v5_relat_1(k2_funct_1('#skF_5'), A_320))), inference(negUnitSimplification, [status(thm)], [c_385, c_3967])).
% 10.87/4.17  tff(c_3996, plain, (![A_320]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), A_320))) | ~v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), k1_relat_1('#skF_5')) | ~v5_relat_1(k2_funct_1('#skF_5'), A_320) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_845, c_3993])).
% 10.87/4.17  tff(c_4028, plain, (![A_321]: (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_321))) | ~v5_relat_1(k2_funct_1('#skF_5'), A_321))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_112, c_106, c_1923, c_269, c_2762, c_2648, c_2648, c_3996])).
% 10.87/4.17  tff(c_4111, plain, (~v5_relat_1(k2_funct_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_4028, c_312])).
% 10.87/4.17  tff(c_4118, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_3130, c_4111])).
% 10.87/4.17  tff(c_4124, plain, (~v4_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_4118])).
% 10.87/4.17  tff(c_4128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_366, c_463, c_4124])).
% 10.87/4.17  tff(c_4129, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_383])).
% 10.87/4.17  tff(c_4130, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_383])).
% 10.87/4.17  tff(c_4158, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4129, c_4130])).
% 10.87/4.17  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.87/4.17  tff(c_130, plain, (![A_53, B_54]: (v1_relat_1(k2_zfmisc_1(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.87/4.17  tff(c_132, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_130])).
% 10.87/4.17  tff(c_290, plain, (![A_76]: (k2_relat_1(A_76)=k1_xboole_0 | k1_relat_1(A_76)!=k1_xboole_0 | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.87/4.17  tff(c_307, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_132, c_290])).
% 10.87/4.17  tff(c_313, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_307])).
% 10.87/4.17  tff(c_4134, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4129, c_4129, c_313])).
% 10.87/4.17  tff(c_4165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4158, c_4134])).
% 10.87/4.17  tff(c_4166, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_307])).
% 10.87/4.17  tff(c_8598, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8594, c_8594, c_4166])).
% 10.87/4.17  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.87/4.17  tff(c_8607, plain, (![A_5]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_8594, c_14])).
% 10.87/4.17  tff(c_9251, plain, (![A_632, B_633, C_634]: (k2_relset_1(A_632, B_633, C_634)=k2_relat_1(C_634) | ~m1_subset_1(C_634, k1_zfmisc_1(k2_zfmisc_1(A_632, B_633))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.87/4.17  tff(c_9258, plain, (![A_632, B_633]: (k2_relset_1(A_632, B_633, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_8607, c_9251])).
% 10.87/4.17  tff(c_9268, plain, (![A_635, B_636]: (k2_relset_1(A_635, B_636, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8598, c_9258])).
% 10.87/4.17  tff(c_9272, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_9268, c_104])).
% 10.87/4.17  tff(c_8610, plain, (![B_4]: (k2_zfmisc_1('#skF_5', B_4)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8594, c_8594, c_12])).
% 10.87/4.17  tff(c_9306, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9272, c_9272, c_8610])).
% 10.87/4.17  tff(c_9316, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9272, c_312])).
% 10.87/4.17  tff(c_9497, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9306, c_9316])).
% 10.87/4.17  tff(c_9315, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9272, c_4204])).
% 10.87/4.17  tff(c_9321, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9272, c_112])).
% 10.87/4.17  tff(c_9320, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9272, c_106])).
% 10.87/4.17  tff(c_8595, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4217])).
% 10.87/4.17  tff(c_8616, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8594, c_8595])).
% 10.87/4.17  tff(c_9313, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9272, c_9272, c_8616])).
% 10.87/4.17  tff(c_9202, plain, (![A_627]: (k2_relat_1(k2_funct_1(A_627))=k1_relat_1(A_627) | ~v2_funct_1(A_627) | ~v1_funct_1(A_627) | ~v1_relat_1(A_627))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.87/4.17  tff(c_8699, plain, (![B_575, A_576]: (v5_relat_1(B_575, A_576) | ~r1_tarski(k2_relat_1(B_575), A_576) | ~v1_relat_1(B_575))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.87/4.17  tff(c_8709, plain, (![B_575]: (v5_relat_1(B_575, k2_relat_1(B_575)) | ~v1_relat_1(B_575))), inference(resolution, [status(thm)], [c_6, c_8699])).
% 10.87/4.17  tff(c_10519, plain, (![A_731]: (v5_relat_1(k2_funct_1(A_731), k1_relat_1(A_731)) | ~v1_relat_1(k2_funct_1(A_731)) | ~v2_funct_1(A_731) | ~v1_funct_1(A_731) | ~v1_relat_1(A_731))), inference(superposition, [status(thm), theory('equality')], [c_9202, c_8709])).
% 10.87/4.17  tff(c_10522, plain, (v5_relat_1(k2_funct_1('#skF_4'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9313, c_10519])).
% 10.87/4.17  tff(c_10527, plain, (v5_relat_1(k2_funct_1('#skF_4'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9315, c_9321, c_9320, c_10522])).
% 10.87/4.17  tff(c_10528, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_10527])).
% 10.87/4.17  tff(c_10547, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_10528])).
% 10.87/4.17  tff(c_10551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9315, c_9321, c_10547])).
% 10.87/4.17  tff(c_10553, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_10527])).
% 10.87/4.17  tff(c_9317, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9272, c_269])).
% 10.87/4.17  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.87/4.17  tff(c_8608, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8594, c_8594, c_10])).
% 10.87/4.17  tff(c_9308, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9272, c_9272, c_8608])).
% 10.87/4.17  tff(c_10552, plain, (v5_relat_1(k2_funct_1('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_10527])).
% 10.87/4.17  tff(c_8746, plain, (![C_583, B_584, A_585]: (v5_relat_1(C_583, B_584) | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(A_585, B_584))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/4.17  tff(c_8760, plain, (![B_584]: (v5_relat_1('#skF_5', B_584))), inference(resolution, [status(thm)], [c_8607, c_8746])).
% 10.87/4.17  tff(c_8816, plain, (![B_591, A_592]: (r1_tarski(k2_relat_1(B_591), A_592) | ~v5_relat_1(B_591, A_592) | ~v1_relat_1(B_591))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.87/4.17  tff(c_8824, plain, (![A_592]: (r1_tarski('#skF_5', A_592) | ~v5_relat_1('#skF_5', A_592) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8598, c_8816])).
% 10.87/4.17  tff(c_8830, plain, (![A_593]: (r1_tarski('#skF_5', A_593))), inference(demodulation, [status(thm), theory('equality')], [c_4204, c_8760, c_8824])).
% 10.87/4.17  tff(c_8833, plain, (![A_593]: (A_593='#skF_5' | ~r1_tarski(A_593, '#skF_5'))), inference(resolution, [status(thm)], [c_8830, c_2])).
% 10.87/4.17  tff(c_9647, plain, (![A_656]: (A_656='#skF_4' | ~r1_tarski(A_656, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9272, c_9272, c_8833])).
% 10.87/4.17  tff(c_9666, plain, (![B_16]: (k2_relat_1(B_16)='#skF_4' | ~v5_relat_1(B_16, '#skF_4') | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_26, c_9647])).
% 10.87/4.17  tff(c_10572, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10552, c_9666])).
% 10.87/4.17  tff(c_10575, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10553, c_10572])).
% 10.87/4.17  tff(c_10604, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10575, c_84])).
% 10.87/4.17  tff(c_10648, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10553, c_9317, c_9308, c_10604])).
% 10.87/4.17  tff(c_10650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9497, c_10648])).
% 10.87/4.17  tff(c_10651, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_268])).
% 10.87/4.17  tff(c_13902, plain, (![C_949, A_950, B_951]: (v1_relat_1(C_949) | ~m1_subset_1(C_949, k1_zfmisc_1(k2_zfmisc_1(A_950, B_951))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.87/4.17  tff(c_13923, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_13902])).
% 10.87/4.17  tff(c_10652, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_268])).
% 10.87/4.17  tff(c_13920, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_10652, c_13902])).
% 10.87/4.17  tff(c_14151, plain, (![C_972, A_973, B_974]: (v4_relat_1(C_972, A_973) | ~m1_subset_1(C_972, k1_zfmisc_1(k2_zfmisc_1(A_973, B_974))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/4.17  tff(c_14171, plain, (v4_relat_1(k2_funct_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_10652, c_14151])).
% 10.87/4.17  tff(c_14859, plain, (![A_1036, B_1037, C_1038]: (k2_relset_1(A_1036, B_1037, C_1038)=k2_relat_1(C_1038) | ~m1_subset_1(C_1038, k1_zfmisc_1(k2_zfmisc_1(A_1036, B_1037))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.87/4.17  tff(c_14871, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_14859])).
% 10.87/4.17  tff(c_14886, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_14871])).
% 10.87/4.17  tff(c_14177, plain, (![B_976, A_977]: (v4_relat_1(B_976, A_977) | ~r1_tarski(k1_relat_1(B_976), A_977) | ~v1_relat_1(B_976))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.87/4.17  tff(c_14191, plain, (![B_976]: (v4_relat_1(B_976, k1_relat_1(B_976)) | ~v1_relat_1(B_976))), inference(resolution, [status(thm)], [c_6, c_14177])).
% 10.87/4.17  tff(c_14599, plain, (![A_1014]: (k1_relat_1(k2_funct_1(A_1014))=k2_relat_1(A_1014) | ~v2_funct_1(A_1014) | ~v1_funct_1(A_1014) | ~v1_relat_1(A_1014))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.87/4.17  tff(c_15941, plain, (![A_1112, A_1113]: (r1_tarski(k2_relat_1(A_1112), A_1113) | ~v4_relat_1(k2_funct_1(A_1112), A_1113) | ~v1_relat_1(k2_funct_1(A_1112)) | ~v2_funct_1(A_1112) | ~v1_funct_1(A_1112) | ~v1_relat_1(A_1112))), inference(superposition, [status(thm), theory('equality')], [c_14599, c_22])).
% 10.87/4.17  tff(c_16586, plain, (![A_1140]: (r1_tarski(k2_relat_1(A_1140), k1_relat_1(k2_funct_1(A_1140))) | ~v2_funct_1(A_1140) | ~v1_funct_1(A_1140) | ~v1_relat_1(A_1140) | ~v1_relat_1(k2_funct_1(A_1140)))), inference(resolution, [status(thm)], [c_14191, c_15941])).
% 10.87/4.17  tff(c_16612, plain, (r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14886, c_16586])).
% 10.87/4.17  tff(c_16640, plain, (r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_13920, c_13923, c_112, c_106, c_16612])).
% 10.87/4.17  tff(c_14035, plain, (![B_959, A_960]: (r1_tarski(k1_relat_1(B_959), A_960) | ~v4_relat_1(B_959, A_960) | ~v1_relat_1(B_959))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.87/4.17  tff(c_14041, plain, (![B_959, A_960]: (k1_relat_1(B_959)=A_960 | ~r1_tarski(A_960, k1_relat_1(B_959)) | ~v4_relat_1(B_959, A_960) | ~v1_relat_1(B_959))), inference(resolution, [status(thm)], [c_14035, c_2])).
% 10.87/4.17  tff(c_16650, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4' | ~v4_relat_1(k2_funct_1('#skF_5'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_16640, c_14041])).
% 10.87/4.17  tff(c_16664, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13920, c_14171, c_16650])).
% 10.87/4.17  tff(c_14504, plain, (![A_1007]: (k2_relat_1(k2_funct_1(A_1007))=k1_relat_1(A_1007) | ~v2_funct_1(A_1007) | ~v1_funct_1(A_1007) | ~v1_relat_1(A_1007))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.87/4.17  tff(c_16771, plain, (![A_1141]: (v1_funct_2(k2_funct_1(A_1141), k1_relat_1(k2_funct_1(A_1141)), k1_relat_1(A_1141)) | ~v1_funct_1(k2_funct_1(A_1141)) | ~v1_relat_1(k2_funct_1(A_1141)) | ~v2_funct_1(A_1141) | ~v1_funct_1(A_1141) | ~v1_relat_1(A_1141))), inference(superposition, [status(thm), theory('equality')], [c_14504, c_86])).
% 10.87/4.17  tff(c_16774, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16664, c_16771])).
% 10.87/4.17  tff(c_16788, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_13923, c_112, c_106, c_13920, c_269, c_16774])).
% 10.87/4.17  tff(c_16704, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16664, c_84])).
% 10.87/4.17  tff(c_16745, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_13920, c_269, c_16704])).
% 10.87/4.17  tff(c_16925, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_16745])).
% 10.87/4.17  tff(c_16945, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_13923, c_112, c_106, c_16925])).
% 10.87/4.17  tff(c_13936, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_13923, c_32])).
% 10.87/4.17  tff(c_13983, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13936])).
% 10.87/4.17  tff(c_14093, plain, (![C_966, B_967, A_968]: (v5_relat_1(C_966, B_967) | ~m1_subset_1(C_966, k1_zfmisc_1(k2_zfmisc_1(A_968, B_967))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/4.17  tff(c_14113, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_10652, c_14093])).
% 10.87/4.17  tff(c_16208, plain, (![A_1127, A_1128]: (r1_tarski(k1_relat_1(A_1127), A_1128) | ~v5_relat_1(k2_funct_1(A_1127), A_1128) | ~v1_relat_1(k2_funct_1(A_1127)) | ~v2_funct_1(A_1127) | ~v1_funct_1(A_1127) | ~v1_relat_1(A_1127))), inference(superposition, [status(thm), theory('equality')], [c_14504, c_26])).
% 10.87/4.17  tff(c_16224, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14113, c_16208])).
% 10.87/4.17  tff(c_16238, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13923, c_112, c_106, c_13920, c_16224])).
% 10.87/4.17  tff(c_96, plain, (![B_42, D_44, A_41, C_43]: (k1_xboole_0=B_42 | v1_funct_2(D_44, A_41, C_43) | ~r1_tarski(B_42, C_43) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_2(D_44, A_41, B_42) | ~v1_funct_1(D_44))), inference(cnfTransformation, [status(thm)], [f_187])).
% 10.87/4.17  tff(c_16243, plain, (![D_44, A_41]: (k1_relat_1('#skF_5')=k1_xboole_0 | v1_funct_2(D_44, A_41, '#skF_3') | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_41, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_44, A_41, k1_relat_1('#skF_5')) | ~v1_funct_1(D_44))), inference(resolution, [status(thm)], [c_16238, c_96])).
% 10.87/4.17  tff(c_16256, plain, (![D_44, A_41]: (v1_funct_2(D_44, A_41, '#skF_3') | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_41, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_44, A_41, k1_relat_1('#skF_5')) | ~v1_funct_1(D_44))), inference(negUnitSimplification, [status(thm)], [c_13983, c_16243])).
% 10.87/4.17  tff(c_17188, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_16945, c_16256])).
% 10.87/4.17  tff(c_17219, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_16788, c_17188])).
% 10.87/4.17  tff(c_17221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10651, c_17219])).
% 10.87/4.17  tff(c_17222, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_13936])).
% 10.87/4.17  tff(c_10678, plain, (![C_735, A_736, B_737]: (v1_relat_1(C_735) | ~m1_subset_1(C_735, k1_zfmisc_1(k2_zfmisc_1(A_736, B_737))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.87/4.17  tff(c_10699, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_10678])).
% 10.87/4.17  tff(c_10696, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_10652, c_10678])).
% 10.87/4.17  tff(c_11265, plain, (![A_808, B_809, C_810]: (k2_relset_1(A_808, B_809, C_810)=k2_relat_1(C_810) | ~m1_subset_1(C_810, k1_zfmisc_1(k2_zfmisc_1(A_808, B_809))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.87/4.17  tff(c_11274, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_11265])).
% 10.87/4.17  tff(c_11288, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_11274])).
% 10.87/4.17  tff(c_11109, plain, (![A_794]: (k1_relat_1(k2_funct_1(A_794))=k2_relat_1(A_794) | ~v2_funct_1(A_794) | ~v1_funct_1(A_794) | ~v1_relat_1(A_794))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.87/4.17  tff(c_12996, plain, (![A_925]: (v1_funct_2(k2_funct_1(A_925), k2_relat_1(A_925), k2_relat_1(k2_funct_1(A_925))) | ~v1_funct_1(k2_funct_1(A_925)) | ~v1_relat_1(k2_funct_1(A_925)) | ~v2_funct_1(A_925) | ~v1_funct_1(A_925) | ~v1_relat_1(A_925))), inference(superposition, [status(thm), theory('equality')], [c_11109, c_86])).
% 10.87/4.17  tff(c_13008, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11288, c_12996])).
% 10.87/4.17  tff(c_13024, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_10699, c_112, c_106, c_10696, c_269, c_13008])).
% 10.87/4.17  tff(c_13034, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_13024])).
% 10.87/4.17  tff(c_13038, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_10699, c_112, c_106, c_13034])).
% 10.87/4.17  tff(c_10848, plain, (![C_754, A_755, B_756]: (v4_relat_1(C_754, A_755) | ~m1_subset_1(C_754, k1_zfmisc_1(k2_zfmisc_1(A_755, B_756))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/4.17  tff(c_10868, plain, (v4_relat_1(k2_funct_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_10652, c_10848])).
% 10.87/4.17  tff(c_10874, plain, (![B_758, A_759]: (v4_relat_1(B_758, A_759) | ~r1_tarski(k1_relat_1(B_758), A_759) | ~v1_relat_1(B_758))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.87/4.17  tff(c_10879, plain, (![B_758]: (v4_relat_1(B_758, k1_relat_1(B_758)) | ~v1_relat_1(B_758))), inference(resolution, [status(thm)], [c_6, c_10874])).
% 10.87/4.17  tff(c_12467, plain, (![A_897, A_898]: (r1_tarski(k2_relat_1(A_897), A_898) | ~v4_relat_1(k2_funct_1(A_897), A_898) | ~v1_relat_1(k2_funct_1(A_897)) | ~v2_funct_1(A_897) | ~v1_funct_1(A_897) | ~v1_relat_1(A_897))), inference(superposition, [status(thm), theory('equality')], [c_11109, c_22])).
% 10.87/4.17  tff(c_13129, plain, (![A_933]: (r1_tarski(k2_relat_1(A_933), k1_relat_1(k2_funct_1(A_933))) | ~v2_funct_1(A_933) | ~v1_funct_1(A_933) | ~v1_relat_1(A_933) | ~v1_relat_1(k2_funct_1(A_933)))), inference(resolution, [status(thm)], [c_10879, c_12467])).
% 10.87/4.17  tff(c_13154, plain, (r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11288, c_13129])).
% 10.87/4.17  tff(c_13177, plain, (r1_tarski('#skF_4', k1_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_10696, c_10699, c_112, c_106, c_13154])).
% 10.87/4.17  tff(c_10892, plain, (![B_765, A_766]: (r1_tarski(k1_relat_1(B_765), A_766) | ~v4_relat_1(B_765, A_766) | ~v1_relat_1(B_765))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.87/4.17  tff(c_10899, plain, (![B_765, A_766]: (k1_relat_1(B_765)=A_766 | ~r1_tarski(A_766, k1_relat_1(B_765)) | ~v4_relat_1(B_765, A_766) | ~v1_relat_1(B_765))), inference(resolution, [status(thm)], [c_10892, c_2])).
% 10.87/4.17  tff(c_13187, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4' | ~v4_relat_1(k2_funct_1('#skF_5'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_13177, c_10899])).
% 10.87/4.17  tff(c_13202, plain, (k1_relat_1(k2_funct_1('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10696, c_10868, c_13187])).
% 10.87/4.17  tff(c_13265, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_13202, c_84])).
% 10.87/4.17  tff(c_13310, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_10696, c_269, c_13265])).
% 10.87/4.17  tff(c_13562, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_13310])).
% 10.87/4.17  tff(c_13582, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_10699, c_112, c_106, c_13562])).
% 10.87/4.17  tff(c_10716, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_10699, c_32])).
% 10.87/4.17  tff(c_10718, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10716])).
% 10.87/4.17  tff(c_10807, plain, (![C_747, B_748, A_749]: (v5_relat_1(C_747, B_748) | ~m1_subset_1(C_747, k1_zfmisc_1(k2_zfmisc_1(A_749, B_748))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/4.17  tff(c_10827, plain, (v5_relat_1(k2_funct_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_10652, c_10807])).
% 10.87/4.17  tff(c_11016, plain, (![A_787]: (k2_relat_1(k2_funct_1(A_787))=k1_relat_1(A_787) | ~v2_funct_1(A_787) | ~v1_funct_1(A_787) | ~v1_relat_1(A_787))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.87/4.17  tff(c_12869, plain, (![A_920, A_921]: (r1_tarski(k1_relat_1(A_920), A_921) | ~v5_relat_1(k2_funct_1(A_920), A_921) | ~v1_relat_1(k2_funct_1(A_920)) | ~v2_funct_1(A_920) | ~v1_funct_1(A_920) | ~v1_relat_1(A_920))), inference(superposition, [status(thm), theory('equality')], [c_11016, c_26])).
% 10.87/4.17  tff(c_12892, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10827, c_12869])).
% 10.87/4.17  tff(c_12904, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10699, c_112, c_106, c_10696, c_12892])).
% 10.87/4.17  tff(c_12910, plain, (![D_44, A_41]: (k1_relat_1('#skF_5')=k1_xboole_0 | v1_funct_2(D_44, A_41, '#skF_3') | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_41, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_44, A_41, k1_relat_1('#skF_5')) | ~v1_funct_1(D_44))), inference(resolution, [status(thm)], [c_12904, c_96])).
% 10.87/4.17  tff(c_12924, plain, (![D_44, A_41]: (v1_funct_2(D_44, A_41, '#skF_3') | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_41, k1_relat_1('#skF_5')))) | ~v1_funct_2(D_44, A_41, k1_relat_1('#skF_5')) | ~v1_funct_1(D_44))), inference(negUnitSimplification, [status(thm)], [c_10718, c_12910])).
% 10.87/4.17  tff(c_13816, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_13582, c_12924])).
% 10.87/4.17  tff(c_13847, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_13038, c_13816])).
% 10.87/4.17  tff(c_13849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10651, c_13847])).
% 10.87/4.17  tff(c_13850, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_10716])).
% 10.87/4.17  tff(c_13851, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10716])).
% 10.87/4.17  tff(c_13872, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13850, c_13851])).
% 10.87/4.17  tff(c_10653, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_307])).
% 10.87/4.17  tff(c_13854, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13850, c_13850, c_10653])).
% 10.87/4.17  tff(c_13880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13872, c_13854])).
% 10.87/4.17  tff(c_13881, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_307])).
% 10.87/4.17  tff(c_17228, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17222, c_17222, c_13881])).
% 10.87/4.17  tff(c_30, plain, (![A_19]: (k2_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.87/4.17  tff(c_13937, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_13923, c_30])).
% 10.87/4.17  tff(c_13950, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13937])).
% 10.87/4.17  tff(c_17224, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17222, c_13950])).
% 10.87/4.17  tff(c_17270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17228, c_17224])).
% 10.87/4.17  tff(c_17271, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_13937])).
% 10.87/4.17  tff(c_17272, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_13937])).
% 10.87/4.17  tff(c_17293, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17271, c_17272])).
% 10.87/4.17  tff(c_17284, plain, (![A_5]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_17271, c_14])).
% 10.87/4.17  tff(c_18724, plain, (![A_1288, B_1289, C_1290]: (k2_relset_1(A_1288, B_1289, C_1290)=k2_relat_1(C_1290) | ~m1_subset_1(C_1290, k1_zfmisc_1(k2_zfmisc_1(A_1288, B_1289))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.87/4.17  tff(c_18731, plain, (![A_1288, B_1289]: (k2_relset_1(A_1288, B_1289, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_17284, c_18724])).
% 10.87/4.17  tff(c_18745, plain, (![A_1291, B_1292]: (k2_relset_1(A_1291, B_1292, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17293, c_18731])).
% 10.87/4.17  tff(c_18749, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_18745, c_104])).
% 10.87/4.17  tff(c_80, plain, (![A_38]: (v1_relat_1('#skF_2'(A_38)))), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.87/4.17  tff(c_177, plain, (![A_60]: (m1_subset_1('#skF_2'(A_60), k1_zfmisc_1(k2_zfmisc_1(A_60, A_60))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.87/4.17  tff(c_181, plain, (m1_subset_1('#skF_2'(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_177])).
% 10.87/4.17  tff(c_17281, plain, (m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_17271, c_17271, c_181])).
% 10.87/4.17  tff(c_17285, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17271, c_17271, c_10])).
% 10.87/4.17  tff(c_18025, plain, (![C_1218, A_1219, B_1220]: (v4_relat_1(C_1218, A_1219) | ~m1_subset_1(C_1218, k1_zfmisc_1(k2_zfmisc_1(A_1219, B_1220))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/4.17  tff(c_18075, plain, (![C_1224, A_1225]: (v4_relat_1(C_1224, A_1225) | ~m1_subset_1(C_1224, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_17285, c_18025])).
% 10.87/4.17  tff(c_18081, plain, (![A_1225]: (v4_relat_1('#skF_2'('#skF_5'), A_1225))), inference(resolution, [status(thm)], [c_17281, c_18075])).
% 10.87/4.17  tff(c_18039, plain, (![A_1219]: (v4_relat_1('#skF_5', A_1219))), inference(resolution, [status(thm)], [c_17284, c_18025])).
% 10.87/4.17  tff(c_13882, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_307])).
% 10.87/4.17  tff(c_17274, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17271, c_17271, c_13882])).
% 10.87/4.17  tff(c_17962, plain, (![B_1210, A_1211]: (r1_tarski(k1_relat_1(B_1210), A_1211) | ~v4_relat_1(B_1210, A_1211) | ~v1_relat_1(B_1210))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.87/4.17  tff(c_17967, plain, (![A_1211]: (r1_tarski('#skF_5', A_1211) | ~v4_relat_1('#skF_5', A_1211) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_17274, c_17962])).
% 10.87/4.17  tff(c_17970, plain, (![A_1211]: (r1_tarski('#skF_5', A_1211) | ~v4_relat_1('#skF_5', A_1211))), inference(demodulation, [status(thm), theory('equality')], [c_13923, c_17967])).
% 10.87/4.17  tff(c_18046, plain, (![A_1222]: (r1_tarski('#skF_5', A_1222))), inference(demodulation, [status(thm), theory('equality')], [c_18039, c_17970])).
% 10.87/4.17  tff(c_18050, plain, (![A_1223]: (A_1223='#skF_5' | ~r1_tarski(A_1223, '#skF_5'))), inference(resolution, [status(thm)], [c_18046, c_2])).
% 10.87/4.17  tff(c_18180, plain, (![B_1239]: (k1_relat_1(B_1239)='#skF_5' | ~v4_relat_1(B_1239, '#skF_5') | ~v1_relat_1(B_1239))), inference(resolution, [status(thm)], [c_22, c_18050])).
% 10.87/4.17  tff(c_18184, plain, (k1_relat_1('#skF_2'('#skF_5'))='#skF_5' | ~v1_relat_1('#skF_2'('#skF_5'))), inference(resolution, [status(thm)], [c_18081, c_18180])).
% 10.87/4.17  tff(c_18195, plain, (k1_relat_1('#skF_2'('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_18184])).
% 10.87/4.17  tff(c_187, plain, (![A_61]: (k1_relat_1(A_61)!=k1_xboole_0 | k1_xboole_0=A_61 | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.87/4.17  tff(c_203, plain, (![A_38]: (k1_relat_1('#skF_2'(A_38))!=k1_xboole_0 | '#skF_2'(A_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_187])).
% 10.87/4.17  tff(c_17277, plain, (![A_38]: (k1_relat_1('#skF_2'(A_38))!='#skF_5' | '#skF_2'(A_38)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17271, c_17271, c_203])).
% 10.87/4.17  tff(c_18211, plain, ('#skF_2'('#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_18195, c_17277])).
% 10.87/4.17  tff(c_66, plain, (![A_38]: (v1_partfun1('#skF_2'(A_38), A_38))), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.87/4.17  tff(c_18260, plain, (v1_partfun1('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18211, c_66])).
% 10.87/4.17  tff(c_18769, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18749, c_18749, c_18260])).
% 10.87/4.17  tff(c_18806, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18749, c_112])).
% 10.87/4.17  tff(c_19037, plain, (![A_1307]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_1307)))), inference(demodulation, [status(thm), theory('equality')], [c_18749, c_17284])).
% 10.87/4.17  tff(c_62, plain, (![C_37, A_35, B_36]: (v1_funct_2(C_37, A_35, B_36) | ~v1_partfun1(C_37, A_35) | ~v1_funct_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 10.87/4.17  tff(c_19041, plain, (![A_35, B_36]: (v1_funct_2('#skF_4', A_35, B_36) | ~v1_partfun1('#skF_4', A_35) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_19037, c_62])).
% 10.87/4.17  tff(c_19292, plain, (![A_1329, B_1330]: (v1_funct_2('#skF_4', A_1329, B_1330) | ~v1_partfun1('#skF_4', A_1329))), inference(demodulation, [status(thm), theory('equality')], [c_18806, c_19041])).
% 10.87/4.17  tff(c_17901, plain, (![A_1209]: (k2_relat_1(k2_funct_1(A_1209))=k1_relat_1(A_1209) | ~v2_funct_1(A_1209) | ~v1_funct_1(A_1209) | ~v1_relat_1(A_1209))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.87/4.17  tff(c_13949, plain, (k2_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0 | k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_13920, c_30])).
% 10.87/4.17  tff(c_17422, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17271, c_17271, c_13949])).
% 10.87/4.17  tff(c_17423, plain, (k2_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_17422])).
% 10.87/4.17  tff(c_17916, plain, (k1_relat_1('#skF_5')!='#skF_5' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_17901, c_17423])).
% 10.87/4.17  tff(c_17926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13923, c_112, c_106, c_17274, c_17916])).
% 10.87/4.17  tff(c_17927, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_17422])).
% 10.87/4.17  tff(c_13948, plain, (k1_relat_1(k2_funct_1('#skF_5'))!=k1_xboole_0 | k2_funct_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_13920, c_32])).
% 10.87/4.17  tff(c_17408, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5' | k2_funct_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17271, c_17271, c_13948])).
% 10.87/4.17  tff(c_17409, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_17408])).
% 10.87/4.17  tff(c_17929, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17927, c_17409])).
% 10.87/4.17  tff(c_17936, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17274, c_17929])).
% 10.87/4.17  tff(c_17937, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_17408])).
% 10.87/4.17  tff(c_17941, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17937, c_10651])).
% 10.87/4.17  tff(c_18790, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18749, c_17941])).
% 10.87/4.17  tff(c_19295, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_19292, c_18790])).
% 10.87/4.17  tff(c_19299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18769, c_19295])).
% 10.87/4.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.87/4.17  
% 10.87/4.17  Inference rules
% 10.87/4.17  ----------------------
% 10.87/4.17  #Ref     : 0
% 10.87/4.17  #Sup     : 3997
% 10.87/4.17  #Fact    : 0
% 10.87/4.17  #Define  : 0
% 10.87/4.17  #Split   : 83
% 10.87/4.17  #Chain   : 0
% 10.87/4.17  #Close   : 0
% 10.87/4.17  
% 10.87/4.17  Ordering : KBO
% 10.87/4.17  
% 10.87/4.17  Simplification rules
% 10.87/4.17  ----------------------
% 10.87/4.17  #Subsume      : 964
% 10.87/4.17  #Demod        : 4789
% 10.87/4.17  #Tautology    : 1438
% 10.87/4.17  #SimpNegUnit  : 142
% 10.87/4.17  #BackRed      : 248
% 10.87/4.17  
% 10.87/4.17  #Partial instantiations: 0
% 10.87/4.17  #Strategies tried      : 1
% 10.87/4.17  
% 10.87/4.17  Timing (in seconds)
% 10.87/4.17  ----------------------
% 10.87/4.18  Preprocessing        : 0.37
% 10.87/4.18  Parsing              : 0.20
% 10.87/4.18  CNF conversion       : 0.03
% 10.87/4.18  Main loop            : 2.96
% 10.87/4.18  Inferencing          : 0.91
% 10.87/4.18  Reduction            : 1.15
% 10.87/4.18  Demodulation         : 0.85
% 10.87/4.18  BG Simplification    : 0.08
% 10.87/4.18  Subsumption          : 0.61
% 10.87/4.18  Abstraction          : 0.10
% 10.87/4.18  MUC search           : 0.00
% 10.87/4.18  Cooper               : 0.00
% 10.87/4.18  Total                : 3.46
% 10.87/4.18  Index Insertion      : 0.00
% 10.87/4.18  Index Deletion       : 0.00
% 10.87/4.18  Index Matching       : 0.00
% 10.87/4.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
