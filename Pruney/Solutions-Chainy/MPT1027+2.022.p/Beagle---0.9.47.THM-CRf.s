%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:45 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   96 (1538 expanded)
%              Number of leaves         :   41 ( 570 expanded)
%              Depth                    :   13
%              Number of atoms          :  126 (4844 expanded)
%              Number of equality atoms :   48 (1638 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_125,axiom,(
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

tff(f_86,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_65,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_30,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_32,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_76,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_565,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_568,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_565])).

tff(c_580,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_568])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_82,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74])).

tff(c_1589,plain,(
    ! [B_146,C_147,A_148] :
      ( k1_xboole_0 = B_146
      | v1_funct_2(C_147,A_148,B_146)
      | k1_relset_1(A_148,B_146,C_147) != A_148
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1598,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_78,c_1589])).

tff(c_1613,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1598])).

tff(c_1614,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1613])).

tff(c_44,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1656,plain,(
    k6_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1614,c_1614,c_44])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1651,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1614,c_1614,c_12])).

tff(c_499,plain,(
    ! [A_76,B_77] :
      ( k9_relat_1(k6_relat_1(A_76),B_77) = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_506,plain,(
    k9_relat_1(k6_relat_1(k2_zfmisc_1('#skF_1','#skF_2')),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_78,c_499])).

tff(c_1877,plain,(
    k9_relat_1(k6_relat_1('#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1651,c_506])).

tff(c_1879,plain,(
    k9_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1656,c_1877])).

tff(c_28,plain,(
    ! [A_19] : k9_relat_1(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1648,plain,(
    ! [A_19] : k9_relat_1('#skF_2',A_19) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1614,c_1614,c_28])).

tff(c_2013,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1879,c_1648])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1654,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1614,c_1614,c_34])).

tff(c_2030,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2013,c_2013,c_1654])).

tff(c_2039,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_2030])).

tff(c_2047,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2039,c_2013])).

tff(c_48,plain,(
    ! [A_28] : v1_relat_1(k6_relat_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_91,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_48])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_352,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_355,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_352])).

tff(c_361,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_355])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_522,plain,(
    ! [B_79,A_80] :
      ( v1_funct_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_532,plain,(
    ! [A_8] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_522])).

tff(c_541,plain,(
    ! [A_84] :
      ( ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(splitLeft,[status(thm)],[c_532])).

tff(c_547,plain,(
    ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_361,c_541])).

tff(c_561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_547])).

tff(c_562,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_532])).

tff(c_239,plain,(
    ! [B_58,A_59] : k2_xboole_0(B_58,A_59) = k2_xboole_0(A_59,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_308,plain,(
    ! [A_62] : k2_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_6])).

tff(c_8,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_320,plain,(
    ! [A_62] : r1_tarski(k1_xboole_0,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_8])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_658,plain,(
    ! [B_95,A_96] :
      ( v1_funct_2(B_95,k1_relat_1(B_95),A_96)
      | ~ r1_tarski(k2_relat_1(B_95),A_96)
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_667,plain,(
    ! [A_96] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,A_96)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),A_96)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_658])).

tff(c_673,plain,(
    ! [A_96] : v1_funct_2(k1_xboole_0,k1_xboole_0,A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_562,c_320,c_32,c_667])).

tff(c_1628,plain,(
    ! [A_96] : v1_funct_2('#skF_2','#skF_2',A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1614,c_1614,c_673])).

tff(c_2320,plain,(
    ! [A_96] : v1_funct_2('#skF_1','#skF_1',A_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2047,c_2047,c_1628])).

tff(c_2037,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2013,c_82])).

tff(c_2314,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2039,c_2039,c_2037])).

tff(c_2323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2320,c_2314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.69  
% 3.92/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.69  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.92/1.69  
% 3.92/1.69  %Foreground sorts:
% 3.92/1.69  
% 3.92/1.69  
% 3.92/1.69  %Background operators:
% 3.92/1.69  
% 3.92/1.69  
% 3.92/1.69  %Foreground operators:
% 3.92/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.92/1.69  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.92/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.92/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.92/1.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.92/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.92/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.92/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.92/1.69  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.92/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.92/1.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.92/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.92/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.92/1.69  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.92/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.92/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.92/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.92/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.69  
% 3.92/1.71  tff(f_150, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 3.92/1.71  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.92/1.71  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.92/1.71  tff(f_86, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.92/1.71  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.92/1.71  tff(f_103, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 3.92/1.71  tff(f_65, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.92/1.71  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.92/1.71  tff(f_99, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.92/1.71  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.92/1.71  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.92/1.71  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.92/1.71  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 3.92/1.71  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.92/1.71  tff(f_30, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.92/1.71  tff(f_32, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.92/1.71  tff(f_137, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.92/1.71  tff(c_76, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.92/1.71  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.92/1.71  tff(c_565, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.92/1.71  tff(c_568, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_565])).
% 3.92/1.71  tff(c_580, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_568])).
% 3.92/1.71  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.92/1.71  tff(c_74, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.92/1.71  tff(c_82, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74])).
% 3.92/1.71  tff(c_1589, plain, (![B_146, C_147, A_148]: (k1_xboole_0=B_146 | v1_funct_2(C_147, A_148, B_146) | k1_relset_1(A_148, B_146, C_147)!=A_148 | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_146))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.92/1.71  tff(c_1598, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_78, c_1589])).
% 3.92/1.71  tff(c_1613, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1598])).
% 3.92/1.71  tff(c_1614, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_82, c_1613])).
% 3.92/1.71  tff(c_44, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.92/1.71  tff(c_1656, plain, (k6_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1614, c_1614, c_44])).
% 3.92/1.71  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.92/1.71  tff(c_1651, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1614, c_1614, c_12])).
% 3.92/1.71  tff(c_499, plain, (![A_76, B_77]: (k9_relat_1(k6_relat_1(A_76), B_77)=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.92/1.71  tff(c_506, plain, (k9_relat_1(k6_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_78, c_499])).
% 3.92/1.71  tff(c_1877, plain, (k9_relat_1(k6_relat_1('#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1651, c_506])).
% 3.92/1.71  tff(c_1879, plain, (k9_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1656, c_1877])).
% 3.92/1.71  tff(c_28, plain, (![A_19]: (k9_relat_1(k1_xboole_0, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.92/1.71  tff(c_1648, plain, (![A_19]: (k9_relat_1('#skF_2', A_19)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1614, c_1614, c_28])).
% 3.92/1.71  tff(c_2013, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1879, c_1648])).
% 3.92/1.71  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.92/1.71  tff(c_1654, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1614, c_1614, c_34])).
% 3.92/1.71  tff(c_2030, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2013, c_2013, c_1654])).
% 3.92/1.71  tff(c_2039, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_580, c_2030])).
% 3.92/1.71  tff(c_2047, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2039, c_2013])).
% 3.92/1.71  tff(c_48, plain, (![A_28]: (v1_relat_1(k6_relat_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.92/1.71  tff(c_91, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_48])).
% 3.92/1.71  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.92/1.71  tff(c_352, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.92/1.71  tff(c_355, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_352])).
% 3.92/1.71  tff(c_361, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_355])).
% 3.92/1.71  tff(c_16, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.92/1.71  tff(c_522, plain, (![B_79, A_80]: (v1_funct_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.92/1.71  tff(c_532, plain, (![A_8]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_16, c_522])).
% 3.92/1.71  tff(c_541, plain, (![A_84]: (~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(splitLeft, [status(thm)], [c_532])).
% 3.92/1.71  tff(c_547, plain, (~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_361, c_541])).
% 3.92/1.71  tff(c_561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_547])).
% 3.92/1.71  tff(c_562, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_532])).
% 3.92/1.71  tff(c_239, plain, (![B_58, A_59]: (k2_xboole_0(B_58, A_59)=k2_xboole_0(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.92/1.71  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.92/1.71  tff(c_308, plain, (![A_62]: (k2_xboole_0(k1_xboole_0, A_62)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_239, c_6])).
% 3.92/1.71  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.71  tff(c_320, plain, (![A_62]: (r1_tarski(k1_xboole_0, A_62))), inference(superposition, [status(thm), theory('equality')], [c_308, c_8])).
% 3.92/1.71  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.92/1.71  tff(c_658, plain, (![B_95, A_96]: (v1_funct_2(B_95, k1_relat_1(B_95), A_96) | ~r1_tarski(k2_relat_1(B_95), A_96) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.92/1.71  tff(c_667, plain, (![A_96]: (v1_funct_2(k1_xboole_0, k1_xboole_0, A_96) | ~r1_tarski(k2_relat_1(k1_xboole_0), A_96) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_658])).
% 3.92/1.71  tff(c_673, plain, (![A_96]: (v1_funct_2(k1_xboole_0, k1_xboole_0, A_96))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_562, c_320, c_32, c_667])).
% 3.92/1.71  tff(c_1628, plain, (![A_96]: (v1_funct_2('#skF_2', '#skF_2', A_96))), inference(demodulation, [status(thm), theory('equality')], [c_1614, c_1614, c_673])).
% 3.92/1.71  tff(c_2320, plain, (![A_96]: (v1_funct_2('#skF_1', '#skF_1', A_96))), inference(demodulation, [status(thm), theory('equality')], [c_2047, c_2047, c_1628])).
% 3.92/1.71  tff(c_2037, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2013, c_82])).
% 3.92/1.71  tff(c_2314, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2039, c_2039, c_2037])).
% 3.92/1.71  tff(c_2323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2320, c_2314])).
% 3.92/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.71  
% 3.92/1.71  Inference rules
% 3.92/1.71  ----------------------
% 3.92/1.71  #Ref     : 0
% 3.92/1.71  #Sup     : 496
% 3.92/1.71  #Fact    : 0
% 3.92/1.71  #Define  : 0
% 3.92/1.71  #Split   : 2
% 3.92/1.71  #Chain   : 0
% 3.92/1.71  #Close   : 0
% 3.92/1.71  
% 3.92/1.71  Ordering : KBO
% 3.92/1.71  
% 3.92/1.71  Simplification rules
% 3.92/1.71  ----------------------
% 3.92/1.71  #Subsume      : 27
% 3.92/1.71  #Demod        : 634
% 3.92/1.71  #Tautology    : 337
% 3.92/1.71  #SimpNegUnit  : 1
% 3.92/1.71  #BackRed      : 83
% 3.92/1.71  
% 3.92/1.71  #Partial instantiations: 0
% 3.92/1.71  #Strategies tried      : 1
% 3.92/1.71  
% 3.92/1.71  Timing (in seconds)
% 3.92/1.71  ----------------------
% 3.92/1.71  Preprocessing        : 0.34
% 3.92/1.71  Parsing              : 0.18
% 3.92/1.71  CNF conversion       : 0.02
% 3.92/1.71  Main loop            : 0.56
% 3.92/1.71  Inferencing          : 0.18
% 3.92/1.71  Reduction            : 0.22
% 3.92/1.71  Demodulation         : 0.17
% 3.92/1.71  BG Simplification    : 0.03
% 3.92/1.71  Subsumption          : 0.09
% 3.92/1.71  Abstraction          : 0.03
% 3.92/1.71  MUC search           : 0.00
% 3.92/1.71  Cooper               : 0.00
% 3.92/1.71  Total                : 0.93
% 3.92/1.71  Index Insertion      : 0.00
% 3.92/1.71  Index Deletion       : 0.00
% 3.92/1.71  Index Matching       : 0.00
% 3.92/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
