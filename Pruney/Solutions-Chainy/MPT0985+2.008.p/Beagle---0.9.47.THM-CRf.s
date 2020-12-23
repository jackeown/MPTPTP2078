%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:26 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 8.36s
% Verified   : 
% Statistics : Number of formulae       :  191 (1092 expanded)
%              Number of leaves         :   47 ( 380 expanded)
%              Depth                    :   19
%              Number of atoms          :  313 (3274 expanded)
%              Number of equality atoms :   93 ( 772 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_218,negated_conjecture,(
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

tff(f_156,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_163,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_167,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_189,axiom,(
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

tff(f_171,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_201,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_104,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_6164,plain,(
    ! [C_271,A_272,B_273] :
      ( v1_relat_1(C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_6176,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_6164])).

tff(c_108,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_984,plain,(
    ! [C_111,B_112,A_113] :
      ( v1_xboole_0(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(B_112,A_113)))
      | ~ v1_xboole_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_992,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_984])).

tff(c_995,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_992])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_878,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_886,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_878])).

tff(c_50,plain,(
    ! [A_18] :
      ( v1_relat_1(k2_funct_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_245,plain,(
    ! [A_62] :
      ( v1_funct_1(k2_funct_1(A_62))
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_98,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_210,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_248,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_245,c_210])).

tff(c_251,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_248])).

tff(c_561,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_564,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_561])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_564])).

tff(c_574,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_102,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_106,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1328,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1336,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_1328])).

tff(c_2911,plain,(
    ! [B_173,A_174,C_175] :
      ( k1_xboole_0 = B_173
      | k1_relset_1(A_174,B_173,C_175) = A_174
      | ~ v1_funct_2(C_175,A_174,B_173)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_2917,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_2911])).

tff(c_2925,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1336,c_2917])).

tff(c_2928,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2925])).

tff(c_100,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1499,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1502,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_1499])).

tff(c_1508,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1502])).

tff(c_26,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2942,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2928,c_26])).

tff(c_2950,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_1508,c_2942])).

tff(c_58,plain,(
    ! [A_22,B_24] :
      ( k9_relat_1(k2_funct_1(A_22),k9_relat_1(A_22,B_24)) = B_24
      | ~ r1_tarski(B_24,k1_relat_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2968,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2950,c_58])).

tff(c_2972,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_108,c_102,c_10,c_2928,c_2968])).

tff(c_2979,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2972,c_58])).

tff(c_2983,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_2979])).

tff(c_4162,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2983])).

tff(c_4165,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_4162])).

tff(c_4169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_108,c_4165])).

tff(c_4171,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2983])).

tff(c_62,plain,(
    ! [A_25] :
      ( k1_relat_1(k2_funct_1(A_25)) = k2_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4170,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2983])).

tff(c_4873,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4170])).

tff(c_4876,plain,
    ( ~ r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_4873])).

tff(c_4879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_108,c_102,c_10,c_1508,c_4876])).

tff(c_4881,plain,(
    r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4170])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4902,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4881,c_6])).

tff(c_5028,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4902])).

tff(c_5031,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_5028])).

tff(c_5034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_108,c_102,c_10,c_1508,c_5031])).

tff(c_5035,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4902])).

tff(c_5056,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5035,c_26])).

tff(c_5069,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4171,c_2972,c_5056])).

tff(c_92,plain,(
    ! [B_44,A_43] :
      ( m1_subset_1(B_44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_44),A_43)))
      | ~ r1_tarski(k2_relat_1(B_44),A_43)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_5047,plain,(
    ! [A_43] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_43)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_43)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5035,c_92])).

tff(c_5063,plain,(
    ! [A_43] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_43)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4171,c_574,c_5047])).

tff(c_5389,plain,(
    ! [A_233] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_233)))
      | ~ r1_tarski('#skF_1',A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5069,c_5063])).

tff(c_573,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_639,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_573])).

tff(c_5416,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_5389,c_639])).

tff(c_5432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5416])).

tff(c_5433,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2925])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_5481,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5433,c_2])).

tff(c_5486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_995,c_5481])).

tff(c_5487,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_5510,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5487,c_4])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5548,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5510,c_14])).

tff(c_5488,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_5530,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_5488,c_4])).

tff(c_5582,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5510,c_5530])).

tff(c_166,plain,(
    ! [A_56] :
      ( v1_xboole_0(k4_relat_1(A_56))
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_178,plain,(
    ! [A_56] :
      ( k4_relat_1(A_56) = k1_xboole_0
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_166,c_4])).

tff(c_5527,plain,(
    k4_relat_1('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5488,c_178])).

tff(c_5598,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5582,c_5510,c_5527])).

tff(c_5565,plain,(
    ! [A_234] :
      ( k4_relat_1(A_234) = k2_funct_1(A_234)
      | ~ v2_funct_1(A_234)
      | ~ v1_funct_1(A_234)
      | ~ v1_relat_1(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5574,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_5565])).

tff(c_5581,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_108,c_5574])).

tff(c_5701,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5598,c_5581])).

tff(c_5587,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5582,c_639])).

tff(c_5924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5548,c_5701,c_5587])).

tff(c_5926,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_6288,plain,(
    ! [C_280,B_281,A_282] :
      ( v1_xboole_0(C_280)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(B_281,A_282)))
      | ~ v1_xboole_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_6299,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_5926,c_6288])).

tff(c_6304,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6299])).

tff(c_6630,plain,(
    ! [A_300,B_301,C_302] :
      ( k2_relset_1(A_300,B_301,C_302) = k2_relat_1(C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_6636,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_6630])).

tff(c_6643,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_6636])).

tff(c_5925,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_6849,plain,(
    ! [A_309,B_310,C_311] :
      ( k1_relset_1(A_309,B_310,C_311) = k1_relat_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_6860,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5926,c_6849])).

tff(c_8894,plain,(
    ! [B_360,C_361,A_362] :
      ( k1_xboole_0 = B_360
      | v1_funct_2(C_361,A_362,B_360)
      | k1_relset_1(A_362,B_360,C_361) != A_362
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_362,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_8900,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_5926,c_8894])).

tff(c_8910,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6860,c_8900])).

tff(c_8911,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5925,c_8910])).

tff(c_8917,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8911])).

tff(c_8920,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8917])).

tff(c_8923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6176,c_108,c_102,c_6643,c_8920])).

tff(c_8924,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8911])).

tff(c_8972,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8924,c_2])).

tff(c_8977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6304,c_8972])).

tff(c_8979,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_6299])).

tff(c_8999,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_8979,c_4])).

tff(c_80,plain,(
    ! [A_40] :
      ( v1_funct_2(k1_xboole_0,A_40,k1_xboole_0)
      | k1_xboole_0 = A_40
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_40,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_110,plain,(
    ! [A_40] :
      ( v1_funct_2(k1_xboole_0,A_40,k1_xboole_0)
      | k1_xboole_0 = A_40 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_9429,plain,(
    ! [A_383] :
      ( v1_funct_2('#skF_1',A_383,'#skF_1')
      | A_383 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8999,c_8999,c_8999,c_110])).

tff(c_8978,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6299])).

tff(c_9205,plain,(
    ! [A_372] :
      ( A_372 = '#skF_1'
      | ~ v1_xboole_0(A_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8999,c_4])).

tff(c_9218,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_8978,c_9205])).

tff(c_9228,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9218,c_5925])).

tff(c_9433,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_9429,c_9228])).

tff(c_6300,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_6288])).

tff(c_6303,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6300])).

tff(c_9437,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9433,c_6303])).

tff(c_9440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8979,c_9437])).

tff(c_9441,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6300])).

tff(c_9464,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9441,c_4])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9506,plain,(
    ! [A_4] : r1_tarski('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9464,c_12])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9504,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9464,c_9464,c_30])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9505,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9464,c_9464,c_32])).

tff(c_10090,plain,(
    ! [B_419,A_420] :
      ( v1_funct_2(B_419,k1_relat_1(B_419),A_420)
      | ~ r1_tarski(k2_relat_1(B_419),A_420)
      | ~ v1_funct_1(B_419)
      | ~ v1_relat_1(B_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_10096,plain,(
    ! [A_420] :
      ( v1_funct_2('#skF_3','#skF_3',A_420)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_420)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9505,c_10090])).

tff(c_10101,plain,(
    ! [A_420] : v1_funct_2('#skF_3','#skF_3',A_420) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6176,c_108,c_9506,c_9504,c_10096])).

tff(c_9442,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_6300])).

tff(c_9484,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_9442,c_4])).

tff(c_9526,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9464,c_9484])).

tff(c_9481,plain,(
    k4_relat_1('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9442,c_178])).

tff(c_9555,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9526,c_9464,c_9481])).

tff(c_9592,plain,(
    ! [A_389] :
      ( k4_relat_1(A_389) = k2_funct_1(A_389)
      | ~ v2_funct_1(A_389)
      | ~ v1_funct_1(A_389)
      | ~ v1_relat_1(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_9601,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_9592])).

tff(c_9608,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6176,c_108,c_9555,c_9601])).

tff(c_9531,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9526,c_5925])).

tff(c_9768,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9608,c_9531])).

tff(c_10106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10101,c_9768])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:42 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.97/2.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.79  
% 7.97/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.79  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.97/2.79  
% 7.97/2.79  %Foreground sorts:
% 7.97/2.79  
% 7.97/2.79  
% 7.97/2.79  %Background operators:
% 7.97/2.79  
% 7.97/2.79  
% 7.97/2.79  %Foreground operators:
% 7.97/2.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.97/2.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.97/2.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.97/2.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.97/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.97/2.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.97/2.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.97/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.97/2.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.97/2.79  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 7.97/2.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.97/2.79  tff('#skF_2', type, '#skF_2': $i).
% 7.97/2.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.97/2.79  tff('#skF_3', type, '#skF_3': $i).
% 7.97/2.79  tff('#skF_1', type, '#skF_1': $i).
% 7.97/2.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.97/2.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.97/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.97/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.97/2.79  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.97/2.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.97/2.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.97/2.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.97/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.97/2.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.97/2.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.97/2.79  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.97/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.97/2.79  
% 8.36/2.82  tff(f_218, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.36/2.82  tff(f_156, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.36/2.82  tff(f_163, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 8.36/2.82  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.36/2.82  tff(f_111, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.36/2.82  tff(f_167, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.36/2.82  tff(f_189, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.36/2.82  tff(f_171, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.36/2.82  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 8.36/2.82  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 8.36/2.82  tff(f_144, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 8.36/2.82  tff(f_201, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 8.36/2.82  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.36/2.82  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.36/2.82  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.36/2.82  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_relat_1)).
% 8.36/2.82  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 8.36/2.82  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.36/2.82  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 8.36/2.82  tff(c_104, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.36/2.82  tff(c_6164, plain, (![C_271, A_272, B_273]: (v1_relat_1(C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.36/2.82  tff(c_6176, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_6164])).
% 8.36/2.82  tff(c_108, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.36/2.82  tff(c_984, plain, (![C_111, B_112, A_113]: (v1_xboole_0(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(B_112, A_113))) | ~v1_xboole_0(A_113))), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.36/2.82  tff(c_992, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_104, c_984])).
% 8.36/2.82  tff(c_995, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_992])).
% 8.36/2.82  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.36/2.82  tff(c_878, plain, (![C_98, A_99, B_100]: (v1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.36/2.82  tff(c_886, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_878])).
% 8.36/2.82  tff(c_50, plain, (![A_18]: (v1_relat_1(k2_funct_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.36/2.82  tff(c_245, plain, (![A_62]: (v1_funct_1(k2_funct_1(A_62)) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.36/2.82  tff(c_98, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.36/2.82  tff(c_210, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_98])).
% 8.36/2.82  tff(c_248, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_245, c_210])).
% 8.36/2.82  tff(c_251, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_248])).
% 8.36/2.82  tff(c_561, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.36/2.82  tff(c_564, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_561])).
% 8.36/2.82  tff(c_572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_251, c_564])).
% 8.36/2.82  tff(c_574, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_98])).
% 8.36/2.82  tff(c_102, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.36/2.82  tff(c_106, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.36/2.82  tff(c_1328, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.36/2.82  tff(c_1336, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_1328])).
% 8.36/2.82  tff(c_2911, plain, (![B_173, A_174, C_175]: (k1_xboole_0=B_173 | k1_relset_1(A_174, B_173, C_175)=A_174 | ~v1_funct_2(C_175, A_174, B_173) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.36/2.82  tff(c_2917, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_104, c_2911])).
% 8.36/2.82  tff(c_2925, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1336, c_2917])).
% 8.36/2.82  tff(c_2928, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_2925])).
% 8.36/2.82  tff(c_100, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_218])).
% 8.36/2.82  tff(c_1499, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.36/2.82  tff(c_1502, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_1499])).
% 8.36/2.82  tff(c_1508, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1502])).
% 8.36/2.82  tff(c_26, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.36/2.82  tff(c_2942, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2928, c_26])).
% 8.36/2.82  tff(c_2950, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_886, c_1508, c_2942])).
% 8.36/2.82  tff(c_58, plain, (![A_22, B_24]: (k9_relat_1(k2_funct_1(A_22), k9_relat_1(A_22, B_24))=B_24 | ~r1_tarski(B_24, k1_relat_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.36/2.82  tff(c_2968, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2950, c_58])).
% 8.36/2.82  tff(c_2972, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_886, c_108, c_102, c_10, c_2928, c_2968])).
% 8.36/2.82  tff(c_2979, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2972, c_58])).
% 8.36/2.82  tff(c_2983, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_574, c_2979])).
% 8.36/2.82  tff(c_4162, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2983])).
% 8.36/2.82  tff(c_4165, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_4162])).
% 8.36/2.82  tff(c_4169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_886, c_108, c_4165])).
% 8.36/2.82  tff(c_4171, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2983])).
% 8.36/2.82  tff(c_62, plain, (![A_25]: (k1_relat_1(k2_funct_1(A_25))=k2_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.36/2.82  tff(c_4170, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_2983])).
% 8.36/2.82  tff(c_4873, plain, (~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_4170])).
% 8.36/2.82  tff(c_4876, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_62, c_4873])).
% 8.36/2.82  tff(c_4879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_886, c_108, c_102, c_10, c_1508, c_4876])).
% 8.36/2.82  tff(c_4881, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_4170])).
% 8.36/2.82  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.36/2.82  tff(c_4902, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_4881, c_6])).
% 8.36/2.82  tff(c_5028, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_4902])).
% 8.36/2.82  tff(c_5031, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_62, c_5028])).
% 8.36/2.82  tff(c_5034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_886, c_108, c_102, c_10, c_1508, c_5031])).
% 8.36/2.82  tff(c_5035, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_4902])).
% 8.36/2.82  tff(c_5056, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5035, c_26])).
% 8.36/2.82  tff(c_5069, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4171, c_2972, c_5056])).
% 8.36/2.82  tff(c_92, plain, (![B_44, A_43]: (m1_subset_1(B_44, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_44), A_43))) | ~r1_tarski(k2_relat_1(B_44), A_43) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.36/2.82  tff(c_5047, plain, (![A_43]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_43))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_43) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5035, c_92])).
% 8.36/2.82  tff(c_5063, plain, (![A_43]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_43))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_43))), inference(demodulation, [status(thm), theory('equality')], [c_4171, c_574, c_5047])).
% 8.36/2.82  tff(c_5389, plain, (![A_233]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_233))) | ~r1_tarski('#skF_1', A_233))), inference(demodulation, [status(thm), theory('equality')], [c_5069, c_5063])).
% 8.36/2.82  tff(c_573, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_98])).
% 8.36/2.82  tff(c_639, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_573])).
% 8.36/2.82  tff(c_5416, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_5389, c_639])).
% 8.36/2.82  tff(c_5432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_5416])).
% 8.36/2.82  tff(c_5433, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2925])).
% 8.36/2.82  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.36/2.82  tff(c_5481, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5433, c_2])).
% 8.36/2.82  tff(c_5486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_995, c_5481])).
% 8.36/2.82  tff(c_5487, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_992])).
% 8.36/2.82  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 8.36/2.82  tff(c_5510, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_5487, c_4])).
% 8.36/2.82  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.36/2.82  tff(c_5548, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_5510, c_14])).
% 8.36/2.82  tff(c_5488, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_992])).
% 8.36/2.82  tff(c_5530, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_5488, c_4])).
% 8.36/2.82  tff(c_5582, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5510, c_5530])).
% 8.36/2.82  tff(c_166, plain, (![A_56]: (v1_xboole_0(k4_relat_1(A_56)) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.36/2.82  tff(c_178, plain, (![A_56]: (k4_relat_1(A_56)=k1_xboole_0 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_166, c_4])).
% 8.36/2.82  tff(c_5527, plain, (k4_relat_1('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_5488, c_178])).
% 8.36/2.82  tff(c_5598, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5582, c_5510, c_5527])).
% 8.36/2.82  tff(c_5565, plain, (![A_234]: (k4_relat_1(A_234)=k2_funct_1(A_234) | ~v2_funct_1(A_234) | ~v1_funct_1(A_234) | ~v1_relat_1(A_234))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.36/2.82  tff(c_5574, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_102, c_5565])).
% 8.36/2.82  tff(c_5581, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_886, c_108, c_5574])).
% 8.36/2.82  tff(c_5701, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5598, c_5581])).
% 8.36/2.82  tff(c_5587, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5582, c_639])).
% 8.36/2.82  tff(c_5924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5548, c_5701, c_5587])).
% 8.36/2.82  tff(c_5926, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_573])).
% 8.36/2.82  tff(c_6288, plain, (![C_280, B_281, A_282]: (v1_xboole_0(C_280) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(B_281, A_282))) | ~v1_xboole_0(A_282))), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.36/2.82  tff(c_6299, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_5926, c_6288])).
% 8.36/2.82  tff(c_6304, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_6299])).
% 8.36/2.82  tff(c_6630, plain, (![A_300, B_301, C_302]: (k2_relset_1(A_300, B_301, C_302)=k2_relat_1(C_302) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.36/2.82  tff(c_6636, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_6630])).
% 8.36/2.82  tff(c_6643, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_6636])).
% 8.36/2.82  tff(c_5925, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_573])).
% 8.36/2.82  tff(c_6849, plain, (![A_309, B_310, C_311]: (k1_relset_1(A_309, B_310, C_311)=k1_relat_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.36/2.82  tff(c_6860, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5926, c_6849])).
% 8.36/2.82  tff(c_8894, plain, (![B_360, C_361, A_362]: (k1_xboole_0=B_360 | v1_funct_2(C_361, A_362, B_360) | k1_relset_1(A_362, B_360, C_361)!=A_362 | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_362, B_360))))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.36/2.82  tff(c_8900, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_5926, c_8894])).
% 8.36/2.82  tff(c_8910, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6860, c_8900])).
% 8.36/2.82  tff(c_8911, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5925, c_8910])).
% 8.36/2.82  tff(c_8917, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_8911])).
% 8.36/2.82  tff(c_8920, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_62, c_8917])).
% 8.36/2.82  tff(c_8923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6176, c_108, c_102, c_6643, c_8920])).
% 8.36/2.82  tff(c_8924, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_8911])).
% 8.36/2.82  tff(c_8972, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8924, c_2])).
% 8.36/2.82  tff(c_8977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6304, c_8972])).
% 8.36/2.82  tff(c_8979, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_6299])).
% 8.36/2.82  tff(c_8999, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_8979, c_4])).
% 8.36/2.82  tff(c_80, plain, (![A_40]: (v1_funct_2(k1_xboole_0, A_40, k1_xboole_0) | k1_xboole_0=A_40 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_40, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.36/2.82  tff(c_110, plain, (![A_40]: (v1_funct_2(k1_xboole_0, A_40, k1_xboole_0) | k1_xboole_0=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_80])).
% 8.36/2.82  tff(c_9429, plain, (![A_383]: (v1_funct_2('#skF_1', A_383, '#skF_1') | A_383='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8999, c_8999, c_8999, c_110])).
% 8.36/2.82  tff(c_8978, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6299])).
% 8.36/2.82  tff(c_9205, plain, (![A_372]: (A_372='#skF_1' | ~v1_xboole_0(A_372))), inference(demodulation, [status(thm), theory('equality')], [c_8999, c_4])).
% 8.36/2.82  tff(c_9218, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_8978, c_9205])).
% 8.36/2.82  tff(c_9228, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9218, c_5925])).
% 8.36/2.82  tff(c_9433, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_9429, c_9228])).
% 8.36/2.82  tff(c_6300, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_104, c_6288])).
% 8.36/2.82  tff(c_6303, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_6300])).
% 8.36/2.82  tff(c_9437, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9433, c_6303])).
% 8.36/2.82  tff(c_9440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8979, c_9437])).
% 8.36/2.82  tff(c_9441, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_6300])).
% 8.36/2.82  tff(c_9464, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_9441, c_4])).
% 8.36/2.82  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.36/2.82  tff(c_9506, plain, (![A_4]: (r1_tarski('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_9464, c_12])).
% 8.36/2.82  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.36/2.82  tff(c_9504, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9464, c_9464, c_30])).
% 8.36/2.82  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.36/2.82  tff(c_9505, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9464, c_9464, c_32])).
% 8.36/2.82  tff(c_10090, plain, (![B_419, A_420]: (v1_funct_2(B_419, k1_relat_1(B_419), A_420) | ~r1_tarski(k2_relat_1(B_419), A_420) | ~v1_funct_1(B_419) | ~v1_relat_1(B_419))), inference(cnfTransformation, [status(thm)], [f_201])).
% 8.36/2.82  tff(c_10096, plain, (![A_420]: (v1_funct_2('#skF_3', '#skF_3', A_420) | ~r1_tarski(k2_relat_1('#skF_3'), A_420) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9505, c_10090])).
% 8.36/2.82  tff(c_10101, plain, (![A_420]: (v1_funct_2('#skF_3', '#skF_3', A_420))), inference(demodulation, [status(thm), theory('equality')], [c_6176, c_108, c_9506, c_9504, c_10096])).
% 8.36/2.82  tff(c_9442, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_6300])).
% 8.36/2.82  tff(c_9484, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_9442, c_4])).
% 8.36/2.82  tff(c_9526, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9464, c_9484])).
% 8.36/2.82  tff(c_9481, plain, (k4_relat_1('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_9442, c_178])).
% 8.36/2.82  tff(c_9555, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9526, c_9464, c_9481])).
% 8.36/2.82  tff(c_9592, plain, (![A_389]: (k4_relat_1(A_389)=k2_funct_1(A_389) | ~v2_funct_1(A_389) | ~v1_funct_1(A_389) | ~v1_relat_1(A_389))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.36/2.82  tff(c_9601, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_102, c_9592])).
% 8.36/2.82  tff(c_9608, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6176, c_108, c_9555, c_9601])).
% 8.36/2.82  tff(c_9531, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9526, c_5925])).
% 8.36/2.82  tff(c_9768, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9608, c_9531])).
% 8.36/2.82  tff(c_10106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10101, c_9768])).
% 8.36/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.36/2.82  
% 8.36/2.82  Inference rules
% 8.36/2.82  ----------------------
% 8.36/2.82  #Ref     : 0
% 8.36/2.82  #Sup     : 2312
% 8.36/2.82  #Fact    : 0
% 8.36/2.82  #Define  : 0
% 8.36/2.82  #Split   : 16
% 8.36/2.82  #Chain   : 0
% 8.36/2.82  #Close   : 0
% 8.36/2.82  
% 8.36/2.82  Ordering : KBO
% 8.36/2.82  
% 8.36/2.82  Simplification rules
% 8.36/2.82  ----------------------
% 8.36/2.82  #Subsume      : 314
% 8.36/2.82  #Demod        : 3274
% 8.36/2.82  #Tautology    : 1533
% 8.36/2.82  #SimpNegUnit  : 11
% 8.36/2.82  #BackRed      : 233
% 8.36/2.82  
% 8.36/2.82  #Partial instantiations: 0
% 8.36/2.82  #Strategies tried      : 1
% 8.36/2.82  
% 8.36/2.82  Timing (in seconds)
% 8.36/2.82  ----------------------
% 8.36/2.82  Preprocessing        : 0.39
% 8.36/2.82  Parsing              : 0.21
% 8.36/2.82  CNF conversion       : 0.03
% 8.36/2.82  Main loop            : 1.58
% 8.36/2.82  Inferencing          : 0.49
% 8.36/2.82  Reduction            : 0.59
% 8.36/2.82  Demodulation         : 0.44
% 8.36/2.82  BG Simplification    : 0.06
% 8.36/2.82  Subsumption          : 0.33
% 8.36/2.82  Abstraction          : 0.07
% 8.36/2.82  MUC search           : 0.00
% 8.36/2.82  Cooper               : 0.00
% 8.36/2.82  Total                : 2.03
% 8.36/2.82  Index Insertion      : 0.00
% 8.36/2.82  Index Deletion       : 0.00
% 8.36/2.82  Index Matching       : 0.00
% 8.36/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
