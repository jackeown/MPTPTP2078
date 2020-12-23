%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:42 EST 2020

% Result     : Theorem 11.26s
% Output     : CNFRefutation 11.69s
% Verified   : 
% Statistics : Number of formulae       :  425 (11531 expanded)
%              Number of leaves         :   44 (3646 expanded)
%              Depth                    :   21
%              Number of atoms          :  732 (28074 expanded)
%              Number of equality atoms :  213 (6793 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_154,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_137,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_127,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_26352,plain,(
    ! [A_1541,B_1542] :
      ( r2_hidden('#skF_2'(A_1541,B_1542),A_1541)
      | r1_tarski(A_1541,B_1542) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26362,plain,(
    ! [A_1541,B_1542] :
      ( ~ v1_xboole_0(A_1541)
      | r1_tarski(A_1541,B_1542) ) ),
    inference(resolution,[status(thm)],[c_26352,c_2])).

tff(c_84,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_26731,plain,(
    ! [C_1586,A_1587,B_1588] :
      ( v1_xboole_0(C_1586)
      | ~ m1_subset_1(C_1586,k1_zfmisc_1(k2_zfmisc_1(A_1587,B_1588)))
      | ~ v1_xboole_0(A_1587) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26754,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_26731])).

tff(c_26757,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26754])).

tff(c_26380,plain,(
    ! [C_1548,A_1549,B_1550] :
      ( v1_relat_1(C_1548)
      | ~ m1_subset_1(C_1548,k1_zfmisc_1(k2_zfmisc_1(A_1549,B_1550))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26402,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_26380])).

tff(c_88,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_82,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_80,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_27234,plain,(
    ! [A_1629,B_1630,C_1631] :
      ( k2_relset_1(A_1629,B_1630,C_1631) = k2_relat_1(C_1631)
      | ~ m1_subset_1(C_1631,k1_zfmisc_1(k2_zfmisc_1(A_1629,B_1630))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_27253,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_27234])).

tff(c_27264,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_27253])).

tff(c_38,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_141,plain,(
    ! [A_59] :
      ( v1_funct_1(k2_funct_1(A_59))
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_78,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_140,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_144,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_141,c_140])).

tff(c_147,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_144])).

tff(c_220,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_230,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_220])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_230])).

tff(c_242,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_254,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_294,plain,(
    ! [C_92,A_93,B_94] :
      ( v1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_312,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_294])).

tff(c_1316,plain,(
    ! [A_186,B_187,C_188] :
      ( k2_relset_1(A_186,B_187,C_188) = k2_relat_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1335,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_1316])).

tff(c_1346,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1335])).

tff(c_34,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_243,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_86,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1409,plain,(
    ! [A_189,B_190,C_191] :
      ( k1_relset_1(A_189,B_190,C_191) = k1_relat_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1442,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_1409])).

tff(c_1899,plain,(
    ! [B_235,A_236,C_237] :
      ( k1_xboole_0 = B_235
      | k1_relset_1(A_236,B_235,C_237) = A_236
      | ~ v1_funct_2(C_237,A_236,B_235)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_236,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1921,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_1899])).

tff(c_1938,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1442,c_1921])).

tff(c_1940,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1938])).

tff(c_700,plain,(
    ! [A_140] :
      ( k2_relat_1(k2_funct_1(A_140)) = k1_relat_1(A_140)
      | ~ v2_funct_1(A_140)
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,(
    ! [A_38] :
      ( v1_funct_2(A_38,k1_relat_1(A_38),k2_relat_1(A_38))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6099,plain,(
    ! [A_455] :
      ( v1_funct_2(k2_funct_1(A_455),k1_relat_1(k2_funct_1(A_455)),k1_relat_1(A_455))
      | ~ v1_funct_1(k2_funct_1(A_455))
      | ~ v1_relat_1(k2_funct_1(A_455))
      | ~ v2_funct_1(A_455)
      | ~ v1_funct_1(A_455)
      | ~ v1_relat_1(A_455) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_74])).

tff(c_6123,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1940,c_6099])).

tff(c_6148,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_82,c_243,c_6123])).

tff(c_6151,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_6148])).

tff(c_6154,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_6151])).

tff(c_6158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_6154])).

tff(c_6160,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_6148])).

tff(c_36,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1067,plain,(
    ! [A_172] :
      ( m1_subset_1(A_172,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_172),k2_relat_1(A_172))))
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_7080,plain,(
    ! [A_487] :
      ( m1_subset_1(k2_funct_1(A_487),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_487)),k1_relat_1(A_487))))
      | ~ v1_funct_1(k2_funct_1(A_487))
      | ~ v1_relat_1(k2_funct_1(A_487))
      | ~ v2_funct_1(A_487)
      | ~ v1_funct_1(A_487)
      | ~ v1_relat_1(A_487) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1067])).

tff(c_7131,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1940,c_7080])).

tff(c_7167,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_82,c_6160,c_243,c_7131])).

tff(c_7193,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),'#skF_4')))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_7167])).

tff(c_7208,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_82,c_1346,c_7193])).

tff(c_7210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_7208])).

tff(c_7211,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1938])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7262,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7211,c_12])).

tff(c_24,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7260,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7211,c_7211,c_24])).

tff(c_72,plain,(
    ! [A_38] :
      ( m1_subset_1(A_38,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_38),k2_relat_1(A_38))))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1350,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1346,c_72])).

tff(c_1357,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_1350])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1378,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_1357,c_28])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_504,plain,(
    ! [C_114,B_115,A_116] :
      ( r2_hidden(C_114,B_115)
      | ~ r2_hidden(C_114,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_583,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_1'(A_124),B_125)
      | ~ r1_tarski(A_124,B_125)
      | v1_xboole_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_4,c_504])).

tff(c_590,plain,(
    ! [B_125,A_124] :
      ( ~ v1_xboole_0(B_125)
      | ~ r1_tarski(A_124,B_125)
      | v1_xboole_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_583,c_2])).

tff(c_1395,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1378,c_590])).

tff(c_1404,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1395])).

tff(c_7284,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7260,c_1404])).

tff(c_7293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7262,c_7284])).

tff(c_7294,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1395])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7319,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7294,c_14])).

tff(c_7345,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7319,c_7319,c_24])).

tff(c_7674,plain,(
    ! [A_505,B_506,C_507] :
      ( k1_relset_1(A_505,B_506,C_507) = k1_relat_1(C_507)
      | ~ m1_subset_1(C_507,k1_zfmisc_1(k2_zfmisc_1(A_505,B_506))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7695,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_7674])).

tff(c_58,plain,(
    ! [B_33,A_32,C_34] :
      ( k1_xboole_0 = B_33
      | k1_relset_1(A_32,B_33,C_34) = A_32
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_8252,plain,(
    ! [B_526,A_527,C_528] :
      ( B_526 = '#skF_6'
      | k1_relset_1(A_527,B_526,C_528) = A_527
      | ~ v1_funct_2(C_528,A_527,B_526)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(A_527,B_526))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7319,c_58])).

tff(c_8274,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_8252])).

tff(c_8283,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_7695,c_8274])).

tff(c_8325,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8283])).

tff(c_7295,plain,(
    v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1395])).

tff(c_345,plain,(
    ! [A_97,B_98] :
      ( r2_hidden('#skF_2'(A_97,B_98),A_97)
      | r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_355,plain,(
    ! [A_97,B_98] :
      ( ~ v1_xboole_0(A_97)
      | r1_tarski(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_345,c_2])).

tff(c_372,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ r1_tarski(B_102,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_383,plain,(
    ! [B_98,A_97] :
      ( B_98 = A_97
      | ~ r1_tarski(B_98,A_97)
      | ~ v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_355,c_372])).

tff(c_1396,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5') = '#skF_6'
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_1378,c_383])).

tff(c_7356,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1396])).

tff(c_7670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7295,c_7356])).

tff(c_7671,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1396])).

tff(c_8327,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8325,c_7671])).

tff(c_245,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,B_81)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_253,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_84,c_245])).

tff(c_386,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_253,c_372])).

tff(c_574,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_8392,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8327,c_574])).

tff(c_8398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8392])).

tff(c_8399,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8283])).

tff(c_8408,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8399,c_574])).

tff(c_8421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_7345,c_8408])).

tff(c_8422,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_8426,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8422,c_84])).

tff(c_8877,plain,(
    ! [A_573,B_574,C_575] :
      ( k2_relset_1(A_573,B_574,C_575) = k2_relat_1(C_575)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(A_573,B_574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_9204,plain,(
    ! [C_593] :
      ( k2_relset_1('#skF_4','#skF_5',C_593) = k2_relat_1(C_593)
      | ~ m1_subset_1(C_593,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8422,c_8877])).

tff(c_9210,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8426,c_9204])).

tff(c_9217,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9210])).

tff(c_8641,plain,(
    ! [A_546] :
      ( k1_relat_1(k2_funct_1(A_546)) = k2_relat_1(A_546)
      | ~ v2_funct_1(A_546)
      | ~ v1_funct_1(A_546)
      | ~ v1_relat_1(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14800,plain,(
    ! [A_882] :
      ( v1_funct_2(k2_funct_1(A_882),k2_relat_1(A_882),k2_relat_1(k2_funct_1(A_882)))
      | ~ v1_funct_1(k2_funct_1(A_882))
      | ~ v1_relat_1(k2_funct_1(A_882))
      | ~ v2_funct_1(A_882)
      | ~ v1_funct_1(A_882)
      | ~ v1_relat_1(A_882) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8641,c_74])).

tff(c_14809,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9217,c_14800])).

tff(c_14821,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),'#skF_5',k2_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_82,c_243,c_14809])).

tff(c_14822,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_14821])).

tff(c_14825,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_14822])).

tff(c_14829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_14825])).

tff(c_14831,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_14821])).

tff(c_9257,plain,(
    ! [A_594,B_595,C_596] :
      ( k1_relset_1(A_594,B_595,C_596) = k1_relat_1(C_596)
      | ~ m1_subset_1(C_596,k1_zfmisc_1(k2_zfmisc_1(A_594,B_595))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9321,plain,(
    ! [C_597] :
      ( k1_relset_1('#skF_4','#skF_5',C_597) = k1_relat_1(C_597)
      | ~ m1_subset_1(C_597,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8422,c_9257])).

tff(c_9333,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8426,c_9321])).

tff(c_9910,plain,(
    ! [B_643,A_644,C_645] :
      ( k1_xboole_0 = B_643
      | k1_relset_1(A_644,B_643,C_645) = A_644
      | ~ v1_funct_2(C_645,A_644,B_643)
      | ~ m1_subset_1(C_645,k1_zfmisc_1(k2_zfmisc_1(A_644,B_643))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_9925,plain,(
    ! [C_645] :
      ( k1_xboole_0 = '#skF_5'
      | k1_relset_1('#skF_4','#skF_5',C_645) = '#skF_4'
      | ~ v1_funct_2(C_645,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_645,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8422,c_9910])).

tff(c_10024,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_9925])).

tff(c_10076,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10024,c_12])).

tff(c_10074,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10024,c_10024,c_24])).

tff(c_435,plain,(
    ! [B_111,A_112] :
      ( B_111 = A_112
      | ~ r1_tarski(B_111,A_112)
      | ~ v1_xboole_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_355,c_372])).

tff(c_462,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_253,c_435])).

tff(c_512,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_462])).

tff(c_8424,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8422,c_512])).

tff(c_9222,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9217,c_72])).

tff(c_9229,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_9222])).

tff(c_9252,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_9229,c_28])).

tff(c_8674,plain,(
    ! [A_553,B_554] :
      ( r2_hidden('#skF_1'(A_553),B_554)
      | ~ r1_tarski(A_553,B_554)
      | v1_xboole_0(A_553) ) ),
    inference(resolution,[status(thm)],[c_4,c_504])).

tff(c_8681,plain,(
    ! [B_554,A_553] :
      ( ~ v1_xboole_0(B_554)
      | ~ r1_tarski(A_553,B_554)
      | v1_xboole_0(A_553) ) ),
    inference(resolution,[status(thm)],[c_8674,c_2])).

tff(c_9295,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_9252,c_8681])).

tff(c_9308,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_8424,c_9295])).

tff(c_10152,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10074,c_9308])).

tff(c_10157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10076,c_10152])).

tff(c_11081,plain,(
    ! [C_726] :
      ( k1_relset_1('#skF_4','#skF_5',C_726) = '#skF_4'
      | ~ v1_funct_2(C_726,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_726,k1_zfmisc_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_9925])).

tff(c_11087,plain,
    ( k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8426,c_11081])).

tff(c_11097,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_9333,c_11087])).

tff(c_9173,plain,(
    ! [A_591] :
      ( m1_subset_1(A_591,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_591),k2_relat_1(A_591))))
      | ~ v1_funct_1(A_591)
      | ~ v1_relat_1(A_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_15972,plain,(
    ! [A_924] :
      ( m1_subset_1(k2_funct_1(A_924),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_924)),k1_relat_1(A_924))))
      | ~ v1_funct_1(k2_funct_1(A_924))
      | ~ v1_relat_1(k2_funct_1(A_924))
      | ~ v2_funct_1(A_924)
      | ~ v1_funct_1(A_924)
      | ~ v1_relat_1(A_924) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_9173])).

tff(c_16017,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_11097,c_15972])).

tff(c_16058,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_82,c_14831,c_243,c_16017])).

tff(c_16090,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),'#skF_4')))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_16058])).

tff(c_16105,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_82,c_9217,c_16090])).

tff(c_16107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_16105])).

tff(c_16108,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_462])).

tff(c_16163,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_16232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16108,c_16163])).

tff(c_16233,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_16109,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_462])).

tff(c_16265,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16233,c_16109])).

tff(c_16274,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_16265,c_14])).

tff(c_26,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16285,plain,(
    ! [B_14] : k2_zfmisc_1('#skF_6',B_14) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16274,c_16274,c_26])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k1_xboole_0 = B_14
      | k1_xboole_0 = A_13
      | k2_zfmisc_1(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16252,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_16233,c_22])).

tff(c_16558,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16274,c_16274,c_16274,c_16252])).

tff(c_16559,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16558])).

tff(c_16286,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16274,c_16274,c_24])).

tff(c_16565,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_16559,c_16286])).

tff(c_16579,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_254])).

tff(c_16829,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16565,c_16579])).

tff(c_16577,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_312])).

tff(c_16584,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_88])).

tff(c_16583,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_82])).

tff(c_16238,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16233,c_84])).

tff(c_16574,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_16559,c_16238])).

tff(c_260,plain,(
    ! [A_84,B_85] : m1_subset_1('#skF_3'(A_84,B_85),k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_271,plain,(
    ! [B_86] : m1_subset_1('#skF_3'(k1_xboole_0,B_86),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_260])).

tff(c_275,plain,(
    ! [B_86] : r1_tarski('#skF_3'(k1_xboole_0,B_86),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_271,c_28])).

tff(c_447,plain,(
    ! [B_86] :
      ( '#skF_3'(k1_xboole_0,B_86) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_275,c_435])).

tff(c_16124,plain,(
    ! [B_925] : '#skF_3'(k1_xboole_0,B_925) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_447])).

tff(c_60,plain,(
    ! [A_35,B_36] : v1_funct_2('#skF_3'(A_35,B_36),A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_16138,plain,(
    ! [B_925] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_925) ),
    inference(superposition,[status(thm),theory(equality)],[c_16124,c_60])).

tff(c_16308,plain,(
    ! [B_925] : v1_funct_2('#skF_6','#skF_6',B_925) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16274,c_16274,c_16138])).

tff(c_16568,plain,(
    ! [B_925] : v1_funct_2('#skF_4','#skF_4',B_925) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_16559,c_16308])).

tff(c_16572,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_16274])).

tff(c_56,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1(k1_xboole_0,B_33,C_34) = k1_xboole_0
      | ~ v1_funct_2(C_34,k1_xboole_0,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_89,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1(k1_xboole_0,B_33,C_34) = k1_xboole_0
      | ~ v1_funct_2(C_34,k1_xboole_0,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_56])).

tff(c_16994,plain,(
    ! [B_982,C_983] :
      ( k1_relset_1('#skF_4',B_982,C_983) = '#skF_4'
      | ~ v1_funct_2(C_983,'#skF_4',B_982)
      | ~ m1_subset_1(C_983,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16572,c_16572,c_16572,c_16572,c_89])).

tff(c_16999,plain,(
    ! [B_925] :
      ( k1_relset_1('#skF_4',B_925,'#skF_4') = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16568,c_16994])).

tff(c_17008,plain,(
    ! [B_925] : k1_relset_1('#skF_4',B_925,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16574,c_16999])).

tff(c_461,plain,(
    ! [B_86] : '#skF_3'(k1_xboole_0,B_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_447])).

tff(c_16276,plain,(
    ! [B_86] : '#skF_3'('#skF_6',B_86) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16274,c_16274,c_461])).

tff(c_16567,plain,(
    ! [B_86] : '#skF_3'('#skF_4',B_86) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_16559,c_16276])).

tff(c_70,plain,(
    ! [A_35,B_36] : m1_subset_1('#skF_3'(A_35,B_36),k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_16801,plain,(
    ! [A_960,B_961,C_962] :
      ( k1_relset_1(A_960,B_961,C_962) = k1_relat_1(C_962)
      | ~ m1_subset_1(C_962,k1_zfmisc_1(k2_zfmisc_1(A_960,B_961))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_17756,plain,(
    ! [A_1042,B_1043] : k1_relset_1(A_1042,B_1043,'#skF_3'(A_1042,B_1043)) = k1_relat_1('#skF_3'(A_1042,B_1043)) ),
    inference(resolution,[status(thm)],[c_70,c_16801])).

tff(c_17774,plain,(
    ! [B_86] : k1_relat_1('#skF_3'('#skF_4',B_86)) = k1_relset_1('#skF_4',B_86,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16567,c_17756])).

tff(c_17778,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17008,c_16567,c_17774])).

tff(c_16580,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_243])).

tff(c_16615,plain,(
    ! [A_954] :
      ( k2_relat_1(k2_funct_1(A_954)) = k1_relat_1(A_954)
      | ~ v2_funct_1(A_954)
      | ~ v1_funct_1(A_954)
      | ~ v1_relat_1(A_954) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20480,plain,(
    ! [A_1204] :
      ( v1_funct_2(k2_funct_1(A_1204),k1_relat_1(k2_funct_1(A_1204)),k1_relat_1(A_1204))
      | ~ v1_funct_1(k2_funct_1(A_1204))
      | ~ v1_relat_1(k2_funct_1(A_1204))
      | ~ v2_funct_1(A_1204)
      | ~ v1_funct_1(A_1204)
      | ~ v1_relat_1(A_1204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16615,c_74])).

tff(c_20492,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17778,c_20480])).

tff(c_20506,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16577,c_16584,c_16583,c_16580,c_20492])).

tff(c_20507,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20506])).

tff(c_20510,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_20507])).

tff(c_20514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16577,c_16584,c_20510])).

tff(c_20516,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_20506])).

tff(c_16951,plain,(
    ! [A_974,B_975,C_976] :
      ( k2_relset_1(A_974,B_975,C_976) = k2_relat_1(C_976)
      | ~ m1_subset_1(C_976,k1_zfmisc_1(k2_zfmisc_1(A_974,B_975))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_17857,plain,(
    ! [A_1047,B_1048] : k2_relset_1(A_1047,B_1048,'#skF_3'(A_1047,B_1048)) = k2_relat_1('#skF_3'(A_1047,B_1048)) ),
    inference(resolution,[status(thm)],[c_70,c_16951])).

tff(c_17875,plain,(
    ! [B_86] : k2_relat_1('#skF_3'('#skF_4',B_86)) = k2_relset_1('#skF_4',B_86,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16567,c_17857])).

tff(c_17887,plain,(
    ! [B_1050] : k2_relset_1('#skF_4',B_1050,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16567,c_17875])).

tff(c_16581,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16559,c_80])).

tff(c_17894,plain,(
    k2_relat_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_17887,c_16581])).

tff(c_16889,plain,(
    ! [A_969] :
      ( m1_subset_1(A_969,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_969),k2_relat_1(A_969))))
      | ~ v1_funct_1(A_969)
      | ~ v1_relat_1(A_969) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_21142,plain,(
    ! [A_1233] :
      ( m1_subset_1(k2_funct_1(A_1233),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1233),k2_relat_1(k2_funct_1(A_1233)))))
      | ~ v1_funct_1(k2_funct_1(A_1233))
      | ~ v1_relat_1(k2_funct_1(A_1233))
      | ~ v2_funct_1(A_1233)
      | ~ v1_funct_1(A_1233)
      | ~ v1_relat_1(A_1233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_16889])).

tff(c_21178,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17894,c_21142])).

tff(c_21201,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16577,c_16584,c_16583,c_20516,c_16580,c_21178])).

tff(c_21225,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_21201])).

tff(c_21240,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16577,c_16584,c_16583,c_16565,c_17778,c_21225])).

tff(c_21242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16829,c_21240])).

tff(c_21243,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_16558])).

tff(c_21248,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21243,c_254])).

tff(c_21254,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16285,c_21248])).

tff(c_288,plain,(
    ! [A_90] : m1_subset_1('#skF_3'(A_90,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_260])).

tff(c_292,plain,(
    ! [A_90] : r1_tarski('#skF_3'(A_90,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_288,c_28])).

tff(c_444,plain,(
    ! [A_90] :
      ( '#skF_3'(A_90,k1_xboole_0) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_292,c_435])).

tff(c_458,plain,(
    ! [A_90] : '#skF_3'(A_90,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_444])).

tff(c_16280,plain,(
    ! [A_90] : '#skF_3'(A_90,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16274,c_16274,c_458])).

tff(c_21743,plain,(
    ! [A_1275,B_1276,C_1277] :
      ( k1_relset_1(A_1275,B_1276,C_1277) = k1_relat_1(C_1277)
      | ~ m1_subset_1(C_1277,k1_zfmisc_1(k2_zfmisc_1(A_1275,B_1276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22164,plain,(
    ! [A_1307,B_1308] : k1_relset_1(A_1307,B_1308,'#skF_3'(A_1307,B_1308)) = k1_relat_1('#skF_3'(A_1307,B_1308)) ),
    inference(resolution,[status(thm)],[c_70,c_21743])).

tff(c_22179,plain,(
    ! [A_90] : k1_relat_1('#skF_3'(A_90,'#skF_6')) = k1_relset_1(A_90,'#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_16280,c_22164])).

tff(c_22245,plain,(
    ! [A_1315] : k1_relset_1(A_1315,'#skF_6','#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16280,c_22179])).

tff(c_22188,plain,(
    ! [B_1309,C_1310] :
      ( k1_relset_1('#skF_6',B_1309,C_1310) = '#skF_6'
      | ~ v1_funct_2(C_1310,'#skF_6',B_1309)
      | ~ m1_subset_1(C_1310,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16274,c_16274,c_16274,c_16274,c_89])).

tff(c_22190,plain,(
    ! [B_925] :
      ( k1_relset_1('#skF_6',B_925,'#skF_6') = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_16308,c_22188])).

tff(c_22199,plain,(
    ! [B_925] : k1_relset_1('#skF_6',B_925,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16238,c_22190])).

tff(c_22250,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_22245,c_22199])).

tff(c_21273,plain,(
    ! [A_1234] :
      ( k2_relat_1(k2_funct_1(A_1234)) = k1_relat_1(A_1234)
      | ~ v2_funct_1(A_1234)
      | ~ v1_funct_1(A_1234)
      | ~ v1_relat_1(A_1234) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_25279,plain,(
    ! [A_1496] :
      ( v1_funct_2(k2_funct_1(A_1496),k1_relat_1(k2_funct_1(A_1496)),k1_relat_1(A_1496))
      | ~ v1_funct_1(k2_funct_1(A_1496))
      | ~ v1_relat_1(k2_funct_1(A_1496))
      | ~ v2_funct_1(A_1496)
      | ~ v1_funct_1(A_1496)
      | ~ v1_relat_1(A_1496) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21273,c_74])).

tff(c_25291,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_22250,c_25279])).

tff(c_25305,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k1_relat_1(k2_funct_1('#skF_6')),'#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_82,c_243,c_25291])).

tff(c_25306,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_25305])).

tff(c_25309,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_25306])).

tff(c_25313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_25309])).

tff(c_25315,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_25305])).

tff(c_21911,plain,(
    ! [A_1290,B_1291,C_1292] :
      ( k2_relset_1(A_1290,B_1291,C_1292) = k2_relat_1(C_1292)
      | ~ m1_subset_1(C_1292,k1_zfmisc_1(k2_zfmisc_1(A_1290,B_1291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22349,plain,(
    ! [A_1321,B_1322] : k2_relset_1(A_1321,B_1322,'#skF_3'(A_1321,B_1322)) = k2_relat_1('#skF_3'(A_1321,B_1322)) ),
    inference(resolution,[status(thm)],[c_70,c_21911])).

tff(c_22364,plain,(
    ! [A_90] : k2_relat_1('#skF_3'(A_90,'#skF_6')) = k2_relset_1(A_90,'#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_16280,c_22349])).

tff(c_22372,plain,(
    ! [A_1323] : k2_relset_1(A_1323,'#skF_6','#skF_6') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16280,c_22364])).

tff(c_21249,plain,(
    k2_relset_1('#skF_4','#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21243,c_21243,c_80])).

tff(c_22376,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_22372,c_21249])).

tff(c_21985,plain,(
    ! [A_1296] :
      ( m1_subset_1(A_1296,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1296),k2_relat_1(A_1296))))
      | ~ v1_funct_1(A_1296)
      | ~ v1_relat_1(A_1296) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_26262,plain,(
    ! [A_1536] :
      ( m1_subset_1(k2_funct_1(A_1536),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1536),k2_relat_1(k2_funct_1(A_1536)))))
      | ~ v1_funct_1(k2_funct_1(A_1536))
      | ~ v1_relat_1(k2_funct_1(A_1536))
      | ~ v2_funct_1(A_1536)
      | ~ v1_funct_1(A_1536)
      | ~ v1_relat_1(A_1536) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_21985])).

tff(c_26304,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6',k2_relat_1(k2_funct_1('#skF_6')))))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_22376,c_26262])).

tff(c_26331,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_88,c_82,c_25315,c_243,c_16285,c_26304])).

tff(c_26333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21254,c_26331])).

tff(c_26334,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_26335,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_27378,plain,(
    ! [A_1638,B_1639,C_1640] :
      ( k1_relset_1(A_1638,B_1639,C_1640) = k1_relat_1(C_1640)
      | ~ m1_subset_1(C_1640,k1_zfmisc_1(k2_zfmisc_1(A_1638,B_1639))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_27405,plain,(
    k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_26335,c_27378])).

tff(c_27972,plain,(
    ! [B_1675,C_1676,A_1677] :
      ( k1_xboole_0 = B_1675
      | v1_funct_2(C_1676,A_1677,B_1675)
      | k1_relset_1(A_1677,B_1675,C_1676) != A_1677
      | ~ m1_subset_1(C_1676,k1_zfmisc_1(k2_zfmisc_1(A_1677,B_1675))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_27987,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_26335,c_27972])).

tff(c_28005,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27405,c_27987])).

tff(c_28006,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_26334,c_28005])).

tff(c_28027,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_28006])).

tff(c_28030,plain,
    ( k2_relat_1('#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_28027])).

tff(c_28033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26402,c_88,c_82,c_27264,c_28030])).

tff(c_28034,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28006])).

tff(c_28076,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28034,c_12])).

tff(c_28078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26757,c_28076])).

tff(c_28080,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_26754])).

tff(c_28103,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28080,c_14])).

tff(c_28079,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_26754])).

tff(c_28092,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_28079,c_14])).

tff(c_28127,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28103,c_28092])).

tff(c_28116,plain,(
    ! [B_14] : k2_zfmisc_1('#skF_6',B_14) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28092,c_28092,c_26])).

tff(c_28170,plain,(
    ! [B_14] : k2_zfmisc_1('#skF_4',B_14) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28127,c_28127,c_28116])).

tff(c_26404,plain,(
    ! [B_1552,A_1553] :
      ( B_1552 = A_1553
      | ~ r1_tarski(B_1552,A_1553)
      | ~ r1_tarski(A_1553,B_1552) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26418,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_253,c_26404])).

tff(c_26507,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_26418])).

tff(c_26518,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_26362,c_26507])).

tff(c_28171,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28170,c_26518])).

tff(c_28174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28080,c_28171])).

tff(c_28175,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26418])).

tff(c_28250,plain,(
    ! [C_1687,A_1688,B_1689] :
      ( v1_xboole_0(C_1687)
      | ~ m1_subset_1(C_1687,k1_zfmisc_1(k2_zfmisc_1(A_1688,B_1689)))
      | ~ v1_xboole_0(A_1688) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28253,plain,(
    ! [C_1687] :
      ( v1_xboole_0(C_1687)
      | ~ m1_subset_1(C_1687,k1_zfmisc_1('#skF_6'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28175,c_28250])).

tff(c_28368,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28253])).

tff(c_28185,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28175,c_84])).

tff(c_28760,plain,(
    ! [A_1736,B_1737,C_1738] :
      ( k2_relset_1(A_1736,B_1737,C_1738) = k2_relat_1(C_1738)
      | ~ m1_subset_1(C_1738,k1_zfmisc_1(k2_zfmisc_1(A_1736,B_1737))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28924,plain,(
    ! [C_1745] :
      ( k2_relset_1('#skF_4','#skF_5',C_1745) = k2_relat_1(C_1745)
      | ~ m1_subset_1(C_1745,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28175,c_28760])).

tff(c_28930,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_28185,c_28924])).

tff(c_28937,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_28930])).

tff(c_29528,plain,(
    ! [A_1779,B_1780,C_1781] :
      ( k1_relset_1(A_1779,B_1780,C_1781) = k1_relat_1(C_1781)
      | ~ m1_subset_1(C_1781,k1_zfmisc_1(k2_zfmisc_1(A_1779,B_1780))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_29563,plain,(
    k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_26335,c_29528])).

tff(c_29873,plain,(
    ! [B_1811,C_1812,A_1813] :
      ( k1_xboole_0 = B_1811
      | v1_funct_2(C_1812,A_1813,B_1811)
      | k1_relset_1(A_1813,B_1811,C_1812) != A_1813
      | ~ m1_subset_1(C_1812,k1_zfmisc_1(k2_zfmisc_1(A_1813,B_1811))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_29894,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relset_1('#skF_5','#skF_4',k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_26335,c_29873])).

tff(c_29912,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k2_funct_1('#skF_6'),'#skF_5','#skF_4')
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29563,c_29894])).

tff(c_29913,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_26334,c_29912])).

tff(c_29916,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_29913])).

tff(c_29919,plain,
    ( k2_relat_1('#skF_6') != '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_29916])).

tff(c_29922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26402,c_88,c_82,c_28937,c_29919])).

tff(c_29923,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_29913])).

tff(c_29973,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29923,c_12])).

tff(c_29975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28368,c_29973])).

tff(c_29977,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_28253])).

tff(c_29986,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_29977,c_14])).

tff(c_28199,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_28175,c_22])).

tff(c_28286,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_28199])).

tff(c_29993,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29986,c_28286])).

tff(c_26364,plain,(
    ! [A_1545,B_1546] : m1_subset_1('#skF_3'(A_1545,B_1546),k1_zfmisc_1(k2_zfmisc_1(A_1545,B_1546))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_26370,plain,(
    ! [B_14] : m1_subset_1('#skF_3'(k1_xboole_0,B_14),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_26364])).

tff(c_28266,plain,(
    ! [C_1687] :
      ( v1_xboole_0(C_1687)
      | ~ m1_subset_1(C_1687,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_28250])).

tff(c_28287,plain,(
    ! [C_1692] :
      ( v1_xboole_0(C_1692)
      | ~ m1_subset_1(C_1692,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28266])).

tff(c_28311,plain,(
    ! [B_1694] : v1_xboole_0('#skF_3'(k1_xboole_0,B_1694)) ),
    inference(resolution,[status(thm)],[c_26370,c_28287])).

tff(c_28320,plain,(
    ! [B_1694] : '#skF_3'(k1_xboole_0,B_1694) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28311,c_14])).

tff(c_30023,plain,(
    ! [B_1694] : '#skF_3'('#skF_4',B_1694) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29986,c_29986,c_28320])).

tff(c_28196,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28175,c_70])).

tff(c_28225,plain,(
    r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_28196,c_28])).

tff(c_30024,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30023,c_28225])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30061,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_30024,c_16])).

tff(c_30066,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_29993,c_30061])).

tff(c_30072,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_26362,c_30066])).

tff(c_30096,plain,(
    ! [C_1818] :
      ( v1_xboole_0(C_1818)
      | ~ m1_subset_1(C_1818,k1_zfmisc_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_28253])).

tff(c_30102,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_28185,c_30096])).

tff(c_30112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30072,c_30102])).

tff(c_30114,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_28199])).

tff(c_30126,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30114,c_12])).

tff(c_30113,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_28199])).

tff(c_30137,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30114,c_30114,c_30113])).

tff(c_30138,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_30137])).

tff(c_28271,plain,
    ( v1_xboole_0(k2_funct_1('#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_26335,c_28250])).

tff(c_28275,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28271])).

tff(c_30139,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30138,c_28275])).

tff(c_30150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30126,c_30139])).

tff(c_30151,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30137])).

tff(c_30152,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30137])).

tff(c_30196,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30151,c_30152])).

tff(c_30154,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30151,c_30114])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_92,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_48])).

tff(c_30175,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_30186,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30154,c_30154,c_30175])).

tff(c_30189,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_30186])).

tff(c_30193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30189])).

tff(c_30194,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32 ) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_30291,plain,(
    ! [A_32] :
      ( v1_funct_2('#skF_4',A_32,'#skF_4')
      | A_32 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30154,c_30154,c_30154,c_30194])).

tff(c_30124,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30114,c_30114,c_24])).

tff(c_30223,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30151,c_30151,c_30124])).

tff(c_30164,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30151,c_26335])).

tff(c_30315,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30223,c_30164])).

tff(c_28274,plain,(
    ! [C_1687] :
      ( v1_xboole_0(C_1687)
      | ~ m1_subset_1(C_1687,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28266])).

tff(c_30330,plain,(
    ! [C_1826] :
      ( v1_xboole_0(C_1826)
      | ~ m1_subset_1(C_1826,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30154,c_28274])).

tff(c_30341,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30315,c_30330])).

tff(c_30125,plain,(
    ! [A_10] :
      ( A_10 = '#skF_6'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30114,c_14])).

tff(c_30212,plain,(
    ! [A_10] :
      ( A_10 = '#skF_4'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30151,c_30125])).

tff(c_30351,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30341,c_30212])).

tff(c_30165,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30151,c_26334])).

tff(c_30357,plain,(
    ~ v1_funct_2('#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30351,c_30165])).

tff(c_30382,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30291,c_30357])).

tff(c_30386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30196,c_30382])).

tff(c_30388,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_28271])).

tff(c_30396,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_30388,c_14])).

tff(c_30476,plain,(
    ! [A_1831] : k2_zfmisc_1(A_1831,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30396,c_30396,c_24])).

tff(c_30486,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_30476,c_28175])).

tff(c_26375,plain,(
    ! [B_1547] : m1_subset_1('#skF_3'(k1_xboole_0,B_1547),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_26364])).

tff(c_26379,plain,(
    ! [B_1547] : r1_tarski('#skF_3'(k1_xboole_0,B_1547),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26375,c_28])).

tff(c_30402,plain,(
    ! [B_1547] : r1_tarski('#skF_3'('#skF_5',B_1547),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30396,c_30396,c_26379])).

tff(c_30633,plain,(
    ! [B_1547] : r1_tarski('#skF_3'('#skF_6',B_1547),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30486,c_30486,c_30402])).

tff(c_30515,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30486,c_30396])).

tff(c_30696,plain,(
    ! [C_1841] :
      ( v1_xboole_0(C_1841)
      | ~ m1_subset_1(C_1841,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30515,c_28274])).

tff(c_30724,plain,(
    ! [A_1843] :
      ( v1_xboole_0(A_1843)
      | ~ r1_tarski(A_1843,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_30696])).

tff(c_30754,plain,(
    ! [B_1845] : v1_xboole_0('#skF_3'('#skF_6',B_1845)) ),
    inference(resolution,[status(thm)],[c_30633,c_30724])).

tff(c_30407,plain,(
    ! [A_10] :
      ( A_10 = '#skF_5'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30396,c_14])).

tff(c_30513,plain,(
    ! [A_10] :
      ( A_10 = '#skF_6'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30486,c_30407])).

tff(c_30813,plain,(
    ! [B_1848] : '#skF_3'('#skF_6',B_1848) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_30754,c_30513])).

tff(c_30827,plain,(
    ! [B_1848] : v1_funct_2('#skF_6','#skF_6',B_1848) ),
    inference(superposition,[status(thm),theory(equality)],[c_30813,c_60])).

tff(c_30387,plain,(
    v1_xboole_0(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_28271])).

tff(c_30420,plain,(
    ! [A_1828] :
      ( A_1828 = '#skF_5'
      | ~ v1_xboole_0(A_1828) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30396,c_14])).

tff(c_30427,plain,(
    k2_funct_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_30387,c_30420])).

tff(c_30434,plain,(
    ~ v1_funct_2('#skF_5','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30427,c_26334])).

tff(c_30508,plain,(
    ~ v1_funct_2('#skF_6','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30486,c_30486,c_30434])).

tff(c_30886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30827,c_30508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:44:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.26/4.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.43/4.49  
% 11.43/4.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.43/4.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 11.43/4.49  
% 11.43/4.49  %Foreground sorts:
% 11.43/4.49  
% 11.43/4.49  
% 11.43/4.49  %Background operators:
% 11.43/4.49  
% 11.43/4.49  
% 11.43/4.49  %Foreground operators:
% 11.43/4.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.43/4.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.43/4.49  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.43/4.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.43/4.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.43/4.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.43/4.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.43/4.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.43/4.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.43/4.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.43/4.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.43/4.49  tff('#skF_5', type, '#skF_5': $i).
% 11.43/4.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.43/4.49  tff('#skF_6', type, '#skF_6': $i).
% 11.43/4.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.43/4.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.43/4.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.43/4.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.43/4.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.43/4.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.43/4.49  tff('#skF_4', type, '#skF_4': $i).
% 11.43/4.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.43/4.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.43/4.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.43/4.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.43/4.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.43/4.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.43/4.49  
% 11.69/4.53  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.69/4.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.69/4.53  tff(f_154, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 11.69/4.53  tff(f_88, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 11.69/4.53  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.69/4.53  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.69/4.53  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 11.69/4.53  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.69/4.53  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.69/4.53  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.69/4.53  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.69/4.53  tff(f_137, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 11.69/4.53  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.69/4.53  tff(f_55, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.69/4.53  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.69/4.53  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.69/4.53  tff(f_127, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 11.69/4.53  tff(c_26352, plain, (![A_1541, B_1542]: (r2_hidden('#skF_2'(A_1541, B_1542), A_1541) | r1_tarski(A_1541, B_1542))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.69/4.53  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.69/4.53  tff(c_26362, plain, (![A_1541, B_1542]: (~v1_xboole_0(A_1541) | r1_tarski(A_1541, B_1542))), inference(resolution, [status(thm)], [c_26352, c_2])).
% 11.69/4.53  tff(c_84, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.69/4.53  tff(c_26731, plain, (![C_1586, A_1587, B_1588]: (v1_xboole_0(C_1586) | ~m1_subset_1(C_1586, k1_zfmisc_1(k2_zfmisc_1(A_1587, B_1588))) | ~v1_xboole_0(A_1587))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.69/4.53  tff(c_26754, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_84, c_26731])).
% 11.69/4.53  tff(c_26757, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_26754])).
% 11.69/4.53  tff(c_26380, plain, (![C_1548, A_1549, B_1550]: (v1_relat_1(C_1548) | ~m1_subset_1(C_1548, k1_zfmisc_1(k2_zfmisc_1(A_1549, B_1550))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.69/4.53  tff(c_26402, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_26380])).
% 11.69/4.53  tff(c_88, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.69/4.53  tff(c_82, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.69/4.53  tff(c_80, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.69/4.53  tff(c_27234, plain, (![A_1629, B_1630, C_1631]: (k2_relset_1(A_1629, B_1630, C_1631)=k2_relat_1(C_1631) | ~m1_subset_1(C_1631, k1_zfmisc_1(k2_zfmisc_1(A_1629, B_1630))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.69/4.53  tff(c_27253, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_27234])).
% 11.69/4.53  tff(c_27264, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_27253])).
% 11.69/4.53  tff(c_38, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.69/4.53  tff(c_20, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.69/4.53  tff(c_141, plain, (![A_59]: (v1_funct_1(k2_funct_1(A_59)) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.69/4.53  tff(c_78, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.69/4.53  tff(c_140, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_78])).
% 11.69/4.53  tff(c_144, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_141, c_140])).
% 11.69/4.53  tff(c_147, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_144])).
% 11.69/4.53  tff(c_220, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.69/4.53  tff(c_230, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_220])).
% 11.69/4.53  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_230])).
% 11.69/4.53  tff(c_242, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_78])).
% 11.69/4.53  tff(c_254, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_242])).
% 11.69/4.53  tff(c_294, plain, (![C_92, A_93, B_94]: (v1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.69/4.53  tff(c_312, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_294])).
% 11.69/4.53  tff(c_1316, plain, (![A_186, B_187, C_188]: (k2_relset_1(A_186, B_187, C_188)=k2_relat_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.69/4.53  tff(c_1335, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_1316])).
% 11.69/4.53  tff(c_1346, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1335])).
% 11.69/4.53  tff(c_34, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.69/4.53  tff(c_243, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_78])).
% 11.69/4.53  tff(c_86, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.69/4.53  tff(c_1409, plain, (![A_189, B_190, C_191]: (k1_relset_1(A_189, B_190, C_191)=k1_relat_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.69/4.53  tff(c_1442, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_1409])).
% 11.69/4.53  tff(c_1899, plain, (![B_235, A_236, C_237]: (k1_xboole_0=B_235 | k1_relset_1(A_236, B_235, C_237)=A_236 | ~v1_funct_2(C_237, A_236, B_235) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_236, B_235))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.69/4.53  tff(c_1921, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_84, c_1899])).
% 11.69/4.53  tff(c_1938, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1442, c_1921])).
% 11.69/4.53  tff(c_1940, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1938])).
% 11.69/4.53  tff(c_700, plain, (![A_140]: (k2_relat_1(k2_funct_1(A_140))=k1_relat_1(A_140) | ~v2_funct_1(A_140) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.69/4.53  tff(c_74, plain, (![A_38]: (v1_funct_2(A_38, k1_relat_1(A_38), k2_relat_1(A_38)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.69/4.53  tff(c_6099, plain, (![A_455]: (v1_funct_2(k2_funct_1(A_455), k1_relat_1(k2_funct_1(A_455)), k1_relat_1(A_455)) | ~v1_funct_1(k2_funct_1(A_455)) | ~v1_relat_1(k2_funct_1(A_455)) | ~v2_funct_1(A_455) | ~v1_funct_1(A_455) | ~v1_relat_1(A_455))), inference(superposition, [status(thm), theory('equality')], [c_700, c_74])).
% 11.69/4.53  tff(c_6123, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1940, c_6099])).
% 11.69/4.53  tff(c_6148, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_82, c_243, c_6123])).
% 11.69/4.53  tff(c_6151, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_6148])).
% 11.69/4.53  tff(c_6154, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_6151])).
% 11.69/4.53  tff(c_6158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_6154])).
% 11.69/4.53  tff(c_6160, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_6148])).
% 11.69/4.53  tff(c_36, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.69/4.53  tff(c_1067, plain, (![A_172]: (m1_subset_1(A_172, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_172), k2_relat_1(A_172)))) | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.69/4.53  tff(c_7080, plain, (![A_487]: (m1_subset_1(k2_funct_1(A_487), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_487)), k1_relat_1(A_487)))) | ~v1_funct_1(k2_funct_1(A_487)) | ~v1_relat_1(k2_funct_1(A_487)) | ~v2_funct_1(A_487) | ~v1_funct_1(A_487) | ~v1_relat_1(A_487))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1067])).
% 11.69/4.53  tff(c_7131, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1940, c_7080])).
% 11.69/4.53  tff(c_7167, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_82, c_6160, c_243, c_7131])).
% 11.69/4.53  tff(c_7193, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), '#skF_4'))) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_7167])).
% 11.69/4.53  tff(c_7208, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_82, c_1346, c_7193])).
% 11.69/4.53  tff(c_7210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_7208])).
% 11.69/4.53  tff(c_7211, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1938])).
% 11.69/4.53  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.69/4.53  tff(c_7262, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7211, c_12])).
% 11.69/4.53  tff(c_24, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.69/4.53  tff(c_7260, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7211, c_7211, c_24])).
% 11.69/4.53  tff(c_72, plain, (![A_38]: (m1_subset_1(A_38, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_38), k2_relat_1(A_38)))) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.69/4.53  tff(c_1350, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1346, c_72])).
% 11.69/4.53  tff(c_1357, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_1350])).
% 11.69/4.53  tff(c_28, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.69/4.53  tff(c_1378, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_1357, c_28])).
% 11.69/4.53  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.69/4.53  tff(c_504, plain, (![C_114, B_115, A_116]: (r2_hidden(C_114, B_115) | ~r2_hidden(C_114, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.69/4.53  tff(c_583, plain, (![A_124, B_125]: (r2_hidden('#skF_1'(A_124), B_125) | ~r1_tarski(A_124, B_125) | v1_xboole_0(A_124))), inference(resolution, [status(thm)], [c_4, c_504])).
% 11.69/4.53  tff(c_590, plain, (![B_125, A_124]: (~v1_xboole_0(B_125) | ~r1_tarski(A_124, B_125) | v1_xboole_0(A_124))), inference(resolution, [status(thm)], [c_583, c_2])).
% 11.69/4.53  tff(c_1395, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1378, c_590])).
% 11.69/4.53  tff(c_1404, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_1395])).
% 11.69/4.53  tff(c_7284, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7260, c_1404])).
% 11.69/4.53  tff(c_7293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7262, c_7284])).
% 11.69/4.53  tff(c_7294, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_1395])).
% 11.69/4.53  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.69/4.53  tff(c_7319, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_7294, c_14])).
% 11.69/4.53  tff(c_7345, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7319, c_7319, c_24])).
% 11.69/4.53  tff(c_7674, plain, (![A_505, B_506, C_507]: (k1_relset_1(A_505, B_506, C_507)=k1_relat_1(C_507) | ~m1_subset_1(C_507, k1_zfmisc_1(k2_zfmisc_1(A_505, B_506))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.69/4.53  tff(c_7695, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_84, c_7674])).
% 11.69/4.53  tff(c_58, plain, (![B_33, A_32, C_34]: (k1_xboole_0=B_33 | k1_relset_1(A_32, B_33, C_34)=A_32 | ~v1_funct_2(C_34, A_32, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.69/4.53  tff(c_8252, plain, (![B_526, A_527, C_528]: (B_526='#skF_6' | k1_relset_1(A_527, B_526, C_528)=A_527 | ~v1_funct_2(C_528, A_527, B_526) | ~m1_subset_1(C_528, k1_zfmisc_1(k2_zfmisc_1(A_527, B_526))))), inference(demodulation, [status(thm), theory('equality')], [c_7319, c_58])).
% 11.69/4.53  tff(c_8274, plain, ('#skF_5'='#skF_6' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_84, c_8252])).
% 11.69/4.53  tff(c_8283, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_7695, c_8274])).
% 11.69/4.53  tff(c_8325, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_8283])).
% 11.69/4.53  tff(c_7295, plain, (v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(splitRight, [status(thm)], [c_1395])).
% 11.69/4.53  tff(c_345, plain, (![A_97, B_98]: (r2_hidden('#skF_2'(A_97, B_98), A_97) | r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.69/4.53  tff(c_355, plain, (![A_97, B_98]: (~v1_xboole_0(A_97) | r1_tarski(A_97, B_98))), inference(resolution, [status(thm)], [c_345, c_2])).
% 11.69/4.53  tff(c_372, plain, (![B_102, A_103]: (B_102=A_103 | ~r1_tarski(B_102, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.69/4.53  tff(c_383, plain, (![B_98, A_97]: (B_98=A_97 | ~r1_tarski(B_98, A_97) | ~v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_355, c_372])).
% 11.69/4.53  tff(c_1396, plain, (k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')='#skF_6' | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_1378, c_383])).
% 11.69/4.53  tff(c_7356, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_1396])).
% 11.69/4.53  tff(c_7670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7295, c_7356])).
% 11.69/4.53  tff(c_7671, plain, (k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_1396])).
% 11.69/4.53  tff(c_8327, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8325, c_7671])).
% 11.69/4.53  tff(c_245, plain, (![A_80, B_81]: (r1_tarski(A_80, B_81) | ~m1_subset_1(A_80, k1_zfmisc_1(B_81)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.69/4.53  tff(c_253, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_245])).
% 11.69/4.53  tff(c_386, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_253, c_372])).
% 11.69/4.53  tff(c_574, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_386])).
% 11.69/4.53  tff(c_8392, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8327, c_574])).
% 11.69/4.53  tff(c_8398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_8392])).
% 11.69/4.53  tff(c_8399, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_8283])).
% 11.69/4.53  tff(c_8408, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8399, c_574])).
% 11.69/4.53  tff(c_8421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_7345, c_8408])).
% 11.69/4.53  tff(c_8422, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_386])).
% 11.69/4.53  tff(c_8426, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8422, c_84])).
% 11.69/4.53  tff(c_8877, plain, (![A_573, B_574, C_575]: (k2_relset_1(A_573, B_574, C_575)=k2_relat_1(C_575) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1(A_573, B_574))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.69/4.53  tff(c_9204, plain, (![C_593]: (k2_relset_1('#skF_4', '#skF_5', C_593)=k2_relat_1(C_593) | ~m1_subset_1(C_593, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8422, c_8877])).
% 11.69/4.53  tff(c_9210, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8426, c_9204])).
% 11.69/4.53  tff(c_9217, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_9210])).
% 11.69/4.53  tff(c_8641, plain, (![A_546]: (k1_relat_1(k2_funct_1(A_546))=k2_relat_1(A_546) | ~v2_funct_1(A_546) | ~v1_funct_1(A_546) | ~v1_relat_1(A_546))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.69/4.53  tff(c_14800, plain, (![A_882]: (v1_funct_2(k2_funct_1(A_882), k2_relat_1(A_882), k2_relat_1(k2_funct_1(A_882))) | ~v1_funct_1(k2_funct_1(A_882)) | ~v1_relat_1(k2_funct_1(A_882)) | ~v2_funct_1(A_882) | ~v1_funct_1(A_882) | ~v1_relat_1(A_882))), inference(superposition, [status(thm), theory('equality')], [c_8641, c_74])).
% 11.69/4.53  tff(c_14809, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9217, c_14800])).
% 11.69/4.53  tff(c_14821, plain, (v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', k2_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_82, c_243, c_14809])).
% 11.69/4.53  tff(c_14822, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_14821])).
% 11.69/4.53  tff(c_14825, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_14822])).
% 11.69/4.53  tff(c_14829, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_14825])).
% 11.69/4.53  tff(c_14831, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_14821])).
% 11.69/4.53  tff(c_9257, plain, (![A_594, B_595, C_596]: (k1_relset_1(A_594, B_595, C_596)=k1_relat_1(C_596) | ~m1_subset_1(C_596, k1_zfmisc_1(k2_zfmisc_1(A_594, B_595))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.69/4.53  tff(c_9321, plain, (![C_597]: (k1_relset_1('#skF_4', '#skF_5', C_597)=k1_relat_1(C_597) | ~m1_subset_1(C_597, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8422, c_9257])).
% 11.69/4.53  tff(c_9333, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8426, c_9321])).
% 11.69/4.53  tff(c_9910, plain, (![B_643, A_644, C_645]: (k1_xboole_0=B_643 | k1_relset_1(A_644, B_643, C_645)=A_644 | ~v1_funct_2(C_645, A_644, B_643) | ~m1_subset_1(C_645, k1_zfmisc_1(k2_zfmisc_1(A_644, B_643))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.69/4.53  tff(c_9925, plain, (![C_645]: (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', C_645)='#skF_4' | ~v1_funct_2(C_645, '#skF_4', '#skF_5') | ~m1_subset_1(C_645, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8422, c_9910])).
% 11.69/4.53  tff(c_10024, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_9925])).
% 11.69/4.53  tff(c_10076, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10024, c_12])).
% 11.69/4.53  tff(c_10074, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10024, c_10024, c_24])).
% 11.69/4.53  tff(c_435, plain, (![B_111, A_112]: (B_111=A_112 | ~r1_tarski(B_111, A_112) | ~v1_xboole_0(A_112))), inference(resolution, [status(thm)], [c_355, c_372])).
% 11.69/4.53  tff(c_462, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_253, c_435])).
% 11.69/4.53  tff(c_512, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_462])).
% 11.69/4.53  tff(c_8424, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8422, c_512])).
% 11.69/4.53  tff(c_9222, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9217, c_72])).
% 11.69/4.53  tff(c_9229, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_9222])).
% 11.69/4.53  tff(c_9252, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_9229, c_28])).
% 11.69/4.53  tff(c_8674, plain, (![A_553, B_554]: (r2_hidden('#skF_1'(A_553), B_554) | ~r1_tarski(A_553, B_554) | v1_xboole_0(A_553))), inference(resolution, [status(thm)], [c_4, c_504])).
% 11.69/4.53  tff(c_8681, plain, (![B_554, A_553]: (~v1_xboole_0(B_554) | ~r1_tarski(A_553, B_554) | v1_xboole_0(A_553))), inference(resolution, [status(thm)], [c_8674, c_2])).
% 11.69/4.53  tff(c_9295, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_9252, c_8681])).
% 11.69/4.53  tff(c_9308, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_8424, c_9295])).
% 11.69/4.53  tff(c_10152, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10074, c_9308])).
% 11.69/4.53  tff(c_10157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10076, c_10152])).
% 11.69/4.53  tff(c_11081, plain, (![C_726]: (k1_relset_1('#skF_4', '#skF_5', C_726)='#skF_4' | ~v1_funct_2(C_726, '#skF_4', '#skF_5') | ~m1_subset_1(C_726, k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_9925])).
% 11.69/4.53  tff(c_11087, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8426, c_11081])).
% 11.69/4.53  tff(c_11097, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_9333, c_11087])).
% 11.69/4.53  tff(c_9173, plain, (![A_591]: (m1_subset_1(A_591, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_591), k2_relat_1(A_591)))) | ~v1_funct_1(A_591) | ~v1_relat_1(A_591))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.69/4.53  tff(c_15972, plain, (![A_924]: (m1_subset_1(k2_funct_1(A_924), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_924)), k1_relat_1(A_924)))) | ~v1_funct_1(k2_funct_1(A_924)) | ~v1_relat_1(k2_funct_1(A_924)) | ~v2_funct_1(A_924) | ~v1_funct_1(A_924) | ~v1_relat_1(A_924))), inference(superposition, [status(thm), theory('equality')], [c_36, c_9173])).
% 11.69/4.53  tff(c_16017, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_11097, c_15972])).
% 11.69/4.53  tff(c_16058, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_6')), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_82, c_14831, c_243, c_16017])).
% 11.69/4.53  tff(c_16090, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), '#skF_4'))) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_16058])).
% 11.69/4.53  tff(c_16105, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_82, c_9217, c_16090])).
% 11.69/4.53  tff(c_16107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_16105])).
% 11.69/4.53  tff(c_16108, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_462])).
% 11.69/4.53  tff(c_16163, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_386])).
% 11.69/4.53  tff(c_16232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_16108, c_16163])).
% 11.69/4.53  tff(c_16233, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_386])).
% 11.69/4.53  tff(c_16109, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_462])).
% 11.69/4.53  tff(c_16265, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16233, c_16109])).
% 11.69/4.53  tff(c_16274, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_16265, c_14])).
% 11.69/4.53  tff(c_26, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.69/4.53  tff(c_16285, plain, (![B_14]: (k2_zfmisc_1('#skF_6', B_14)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16274, c_16274, c_26])).
% 11.69/4.53  tff(c_22, plain, (![B_14, A_13]: (k1_xboole_0=B_14 | k1_xboole_0=A_13 | k2_zfmisc_1(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.69/4.53  tff(c_16252, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_16233, c_22])).
% 11.69/4.53  tff(c_16558, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16274, c_16274, c_16274, c_16252])).
% 11.69/4.53  tff(c_16559, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_16558])).
% 11.69/4.53  tff(c_16286, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16274, c_16274, c_24])).
% 11.69/4.53  tff(c_16565, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_16559, c_16286])).
% 11.69/4.53  tff(c_16579, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_254])).
% 11.69/4.53  tff(c_16829, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16565, c_16579])).
% 11.69/4.53  tff(c_16577, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_312])).
% 11.69/4.53  tff(c_16584, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_88])).
% 11.69/4.53  tff(c_16583, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_82])).
% 11.69/4.53  tff(c_16238, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_16233, c_84])).
% 11.69/4.53  tff(c_16574, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_16559, c_16238])).
% 11.69/4.53  tff(c_260, plain, (![A_84, B_85]: (m1_subset_1('#skF_3'(A_84, B_85), k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.69/4.53  tff(c_271, plain, (![B_86]: (m1_subset_1('#skF_3'(k1_xboole_0, B_86), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_260])).
% 11.69/4.53  tff(c_275, plain, (![B_86]: (r1_tarski('#skF_3'(k1_xboole_0, B_86), k1_xboole_0))), inference(resolution, [status(thm)], [c_271, c_28])).
% 11.69/4.53  tff(c_447, plain, (![B_86]: ('#skF_3'(k1_xboole_0, B_86)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_275, c_435])).
% 11.69/4.53  tff(c_16124, plain, (![B_925]: ('#skF_3'(k1_xboole_0, B_925)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_447])).
% 11.69/4.53  tff(c_60, plain, (![A_35, B_36]: (v1_funct_2('#skF_3'(A_35, B_36), A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.69/4.53  tff(c_16138, plain, (![B_925]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_925))), inference(superposition, [status(thm), theory('equality')], [c_16124, c_60])).
% 11.69/4.53  tff(c_16308, plain, (![B_925]: (v1_funct_2('#skF_6', '#skF_6', B_925))), inference(demodulation, [status(thm), theory('equality')], [c_16274, c_16274, c_16138])).
% 11.69/4.53  tff(c_16568, plain, (![B_925]: (v1_funct_2('#skF_4', '#skF_4', B_925))), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_16559, c_16308])).
% 11.69/4.53  tff(c_16572, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_16274])).
% 11.69/4.53  tff(c_56, plain, (![B_33, C_34]: (k1_relset_1(k1_xboole_0, B_33, C_34)=k1_xboole_0 | ~v1_funct_2(C_34, k1_xboole_0, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.69/4.53  tff(c_89, plain, (![B_33, C_34]: (k1_relset_1(k1_xboole_0, B_33, C_34)=k1_xboole_0 | ~v1_funct_2(C_34, k1_xboole_0, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_56])).
% 11.69/4.53  tff(c_16994, plain, (![B_982, C_983]: (k1_relset_1('#skF_4', B_982, C_983)='#skF_4' | ~v1_funct_2(C_983, '#skF_4', B_982) | ~m1_subset_1(C_983, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16572, c_16572, c_16572, c_16572, c_89])).
% 11.69/4.53  tff(c_16999, plain, (![B_925]: (k1_relset_1('#skF_4', B_925, '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_16568, c_16994])).
% 11.69/4.53  tff(c_17008, plain, (![B_925]: (k1_relset_1('#skF_4', B_925, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16574, c_16999])).
% 11.69/4.53  tff(c_461, plain, (![B_86]: ('#skF_3'(k1_xboole_0, B_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_447])).
% 11.69/4.53  tff(c_16276, plain, (![B_86]: ('#skF_3'('#skF_6', B_86)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16274, c_16274, c_461])).
% 11.69/4.53  tff(c_16567, plain, (![B_86]: ('#skF_3'('#skF_4', B_86)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_16559, c_16276])).
% 11.69/4.53  tff(c_70, plain, (![A_35, B_36]: (m1_subset_1('#skF_3'(A_35, B_36), k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.69/4.53  tff(c_16801, plain, (![A_960, B_961, C_962]: (k1_relset_1(A_960, B_961, C_962)=k1_relat_1(C_962) | ~m1_subset_1(C_962, k1_zfmisc_1(k2_zfmisc_1(A_960, B_961))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.69/4.53  tff(c_17756, plain, (![A_1042, B_1043]: (k1_relset_1(A_1042, B_1043, '#skF_3'(A_1042, B_1043))=k1_relat_1('#skF_3'(A_1042, B_1043)))), inference(resolution, [status(thm)], [c_70, c_16801])).
% 11.69/4.53  tff(c_17774, plain, (![B_86]: (k1_relat_1('#skF_3'('#skF_4', B_86))=k1_relset_1('#skF_4', B_86, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16567, c_17756])).
% 11.69/4.53  tff(c_17778, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17008, c_16567, c_17774])).
% 11.69/4.53  tff(c_16580, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_243])).
% 11.69/4.53  tff(c_16615, plain, (![A_954]: (k2_relat_1(k2_funct_1(A_954))=k1_relat_1(A_954) | ~v2_funct_1(A_954) | ~v1_funct_1(A_954) | ~v1_relat_1(A_954))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.69/4.53  tff(c_20480, plain, (![A_1204]: (v1_funct_2(k2_funct_1(A_1204), k1_relat_1(k2_funct_1(A_1204)), k1_relat_1(A_1204)) | ~v1_funct_1(k2_funct_1(A_1204)) | ~v1_relat_1(k2_funct_1(A_1204)) | ~v2_funct_1(A_1204) | ~v1_funct_1(A_1204) | ~v1_relat_1(A_1204))), inference(superposition, [status(thm), theory('equality')], [c_16615, c_74])).
% 11.69/4.53  tff(c_20492, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17778, c_20480])).
% 11.69/4.53  tff(c_20506, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16577, c_16584, c_16583, c_16580, c_20492])).
% 11.69/4.53  tff(c_20507, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_20506])).
% 11.69/4.53  tff(c_20510, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_20507])).
% 11.69/4.53  tff(c_20514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16577, c_16584, c_20510])).
% 11.69/4.53  tff(c_20516, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_20506])).
% 11.69/4.53  tff(c_16951, plain, (![A_974, B_975, C_976]: (k2_relset_1(A_974, B_975, C_976)=k2_relat_1(C_976) | ~m1_subset_1(C_976, k1_zfmisc_1(k2_zfmisc_1(A_974, B_975))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.69/4.53  tff(c_17857, plain, (![A_1047, B_1048]: (k2_relset_1(A_1047, B_1048, '#skF_3'(A_1047, B_1048))=k2_relat_1('#skF_3'(A_1047, B_1048)))), inference(resolution, [status(thm)], [c_70, c_16951])).
% 11.69/4.53  tff(c_17875, plain, (![B_86]: (k2_relat_1('#skF_3'('#skF_4', B_86))=k2_relset_1('#skF_4', B_86, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_16567, c_17857])).
% 11.69/4.53  tff(c_17887, plain, (![B_1050]: (k2_relset_1('#skF_4', B_1050, '#skF_4')=k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16567, c_17875])).
% 11.69/4.53  tff(c_16581, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16559, c_80])).
% 11.69/4.53  tff(c_17894, plain, (k2_relat_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_17887, c_16581])).
% 11.69/4.53  tff(c_16889, plain, (![A_969]: (m1_subset_1(A_969, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_969), k2_relat_1(A_969)))) | ~v1_funct_1(A_969) | ~v1_relat_1(A_969))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.69/4.53  tff(c_21142, plain, (![A_1233]: (m1_subset_1(k2_funct_1(A_1233), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1233), k2_relat_1(k2_funct_1(A_1233))))) | ~v1_funct_1(k2_funct_1(A_1233)) | ~v1_relat_1(k2_funct_1(A_1233)) | ~v2_funct_1(A_1233) | ~v1_funct_1(A_1233) | ~v1_relat_1(A_1233))), inference(superposition, [status(thm), theory('equality')], [c_38, c_16889])).
% 11.69/4.53  tff(c_21178, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17894, c_21142])).
% 11.69/4.53  tff(c_21201, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_16577, c_16584, c_16583, c_20516, c_16580, c_21178])).
% 11.69/4.53  tff(c_21225, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_21201])).
% 11.69/4.53  tff(c_21240, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16577, c_16584, c_16583, c_16565, c_17778, c_21225])).
% 11.69/4.53  tff(c_21242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16829, c_21240])).
% 11.69/4.53  tff(c_21243, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_16558])).
% 11.69/4.53  tff(c_21248, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_21243, c_254])).
% 11.69/4.53  tff(c_21254, plain, (~m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_16285, c_21248])).
% 11.69/4.53  tff(c_288, plain, (![A_90]: (m1_subset_1('#skF_3'(A_90, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_260])).
% 11.69/4.53  tff(c_292, plain, (![A_90]: (r1_tarski('#skF_3'(A_90, k1_xboole_0), k1_xboole_0))), inference(resolution, [status(thm)], [c_288, c_28])).
% 11.69/4.53  tff(c_444, plain, (![A_90]: ('#skF_3'(A_90, k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_292, c_435])).
% 11.69/4.53  tff(c_458, plain, (![A_90]: ('#skF_3'(A_90, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_444])).
% 11.69/4.53  tff(c_16280, plain, (![A_90]: ('#skF_3'(A_90, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16274, c_16274, c_458])).
% 11.69/4.53  tff(c_21743, plain, (![A_1275, B_1276, C_1277]: (k1_relset_1(A_1275, B_1276, C_1277)=k1_relat_1(C_1277) | ~m1_subset_1(C_1277, k1_zfmisc_1(k2_zfmisc_1(A_1275, B_1276))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.69/4.53  tff(c_22164, plain, (![A_1307, B_1308]: (k1_relset_1(A_1307, B_1308, '#skF_3'(A_1307, B_1308))=k1_relat_1('#skF_3'(A_1307, B_1308)))), inference(resolution, [status(thm)], [c_70, c_21743])).
% 11.69/4.53  tff(c_22179, plain, (![A_90]: (k1_relat_1('#skF_3'(A_90, '#skF_6'))=k1_relset_1(A_90, '#skF_6', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_16280, c_22164])).
% 11.69/4.53  tff(c_22245, plain, (![A_1315]: (k1_relset_1(A_1315, '#skF_6', '#skF_6')=k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_16280, c_22179])).
% 11.69/4.53  tff(c_22188, plain, (![B_1309, C_1310]: (k1_relset_1('#skF_6', B_1309, C_1310)='#skF_6' | ~v1_funct_2(C_1310, '#skF_6', B_1309) | ~m1_subset_1(C_1310, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_16274, c_16274, c_16274, c_16274, c_89])).
% 11.69/4.53  tff(c_22190, plain, (![B_925]: (k1_relset_1('#skF_6', B_925, '#skF_6')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_16308, c_22188])).
% 11.69/4.53  tff(c_22199, plain, (![B_925]: (k1_relset_1('#skF_6', B_925, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16238, c_22190])).
% 11.69/4.53  tff(c_22250, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_22245, c_22199])).
% 11.69/4.53  tff(c_21273, plain, (![A_1234]: (k2_relat_1(k2_funct_1(A_1234))=k1_relat_1(A_1234) | ~v2_funct_1(A_1234) | ~v1_funct_1(A_1234) | ~v1_relat_1(A_1234))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.69/4.53  tff(c_25279, plain, (![A_1496]: (v1_funct_2(k2_funct_1(A_1496), k1_relat_1(k2_funct_1(A_1496)), k1_relat_1(A_1496)) | ~v1_funct_1(k2_funct_1(A_1496)) | ~v1_relat_1(k2_funct_1(A_1496)) | ~v2_funct_1(A_1496) | ~v1_funct_1(A_1496) | ~v1_relat_1(A_1496))), inference(superposition, [status(thm), theory('equality')], [c_21273, c_74])).
% 11.69/4.53  tff(c_25291, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_22250, c_25279])).
% 11.69/4.53  tff(c_25305, plain, (v1_funct_2(k2_funct_1('#skF_6'), k1_relat_1(k2_funct_1('#skF_6')), '#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_82, c_243, c_25291])).
% 11.69/4.53  tff(c_25306, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_25305])).
% 11.69/4.53  tff(c_25309, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_25306])).
% 11.69/4.53  tff(c_25313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_25309])).
% 11.69/4.53  tff(c_25315, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_25305])).
% 11.69/4.53  tff(c_21911, plain, (![A_1290, B_1291, C_1292]: (k2_relset_1(A_1290, B_1291, C_1292)=k2_relat_1(C_1292) | ~m1_subset_1(C_1292, k1_zfmisc_1(k2_zfmisc_1(A_1290, B_1291))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.69/4.53  tff(c_22349, plain, (![A_1321, B_1322]: (k2_relset_1(A_1321, B_1322, '#skF_3'(A_1321, B_1322))=k2_relat_1('#skF_3'(A_1321, B_1322)))), inference(resolution, [status(thm)], [c_70, c_21911])).
% 11.69/4.53  tff(c_22364, plain, (![A_90]: (k2_relat_1('#skF_3'(A_90, '#skF_6'))=k2_relset_1(A_90, '#skF_6', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_16280, c_22349])).
% 11.69/4.53  tff(c_22372, plain, (![A_1323]: (k2_relset_1(A_1323, '#skF_6', '#skF_6')=k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_16280, c_22364])).
% 11.69/4.53  tff(c_21249, plain, (k2_relset_1('#skF_4', '#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_21243, c_21243, c_80])).
% 11.69/4.53  tff(c_22376, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_22372, c_21249])).
% 11.69/4.53  tff(c_21985, plain, (![A_1296]: (m1_subset_1(A_1296, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1296), k2_relat_1(A_1296)))) | ~v1_funct_1(A_1296) | ~v1_relat_1(A_1296))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.69/4.53  tff(c_26262, plain, (![A_1536]: (m1_subset_1(k2_funct_1(A_1536), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1536), k2_relat_1(k2_funct_1(A_1536))))) | ~v1_funct_1(k2_funct_1(A_1536)) | ~v1_relat_1(k2_funct_1(A_1536)) | ~v2_funct_1(A_1536) | ~v1_funct_1(A_1536) | ~v1_relat_1(A_1536))), inference(superposition, [status(thm), theory('equality')], [c_38, c_21985])).
% 11.69/4.53  tff(c_26304, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', k2_relat_1(k2_funct_1('#skF_6'))))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_22376, c_26262])).
% 11.69/4.53  tff(c_26331, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_88, c_82, c_25315, c_243, c_16285, c_26304])).
% 11.69/4.53  tff(c_26333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21254, c_26331])).
% 11.69/4.53  tff(c_26334, plain, (~v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_242])).
% 11.69/4.53  tff(c_26335, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_242])).
% 11.69/4.53  tff(c_27378, plain, (![A_1638, B_1639, C_1640]: (k1_relset_1(A_1638, B_1639, C_1640)=k1_relat_1(C_1640) | ~m1_subset_1(C_1640, k1_zfmisc_1(k2_zfmisc_1(A_1638, B_1639))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.69/4.53  tff(c_27405, plain, (k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_26335, c_27378])).
% 11.69/4.53  tff(c_27972, plain, (![B_1675, C_1676, A_1677]: (k1_xboole_0=B_1675 | v1_funct_2(C_1676, A_1677, B_1675) | k1_relset_1(A_1677, B_1675, C_1676)!=A_1677 | ~m1_subset_1(C_1676, k1_zfmisc_1(k2_zfmisc_1(A_1677, B_1675))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.69/4.53  tff(c_27987, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))!='#skF_5'), inference(resolution, [status(thm)], [c_26335, c_27972])).
% 11.69/4.53  tff(c_28005, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_27405, c_27987])).
% 11.69/4.53  tff(c_28006, plain, (k1_xboole_0='#skF_4' | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_26334, c_28005])).
% 11.69/4.53  tff(c_28027, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_28006])).
% 11.69/4.53  tff(c_28030, plain, (k2_relat_1('#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_28027])).
% 11.69/4.53  tff(c_28033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26402, c_88, c_82, c_27264, c_28030])).
% 11.69/4.53  tff(c_28034, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_28006])).
% 11.69/4.53  tff(c_28076, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28034, c_12])).
% 11.69/4.53  tff(c_28078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26757, c_28076])).
% 11.69/4.53  tff(c_28080, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_26754])).
% 11.69/4.53  tff(c_28103, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28080, c_14])).
% 11.69/4.54  tff(c_28079, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_26754])).
% 11.69/4.54  tff(c_28092, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_28079, c_14])).
% 11.69/4.54  tff(c_28127, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28103, c_28092])).
% 11.69/4.54  tff(c_28116, plain, (![B_14]: (k2_zfmisc_1('#skF_6', B_14)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28092, c_28092, c_26])).
% 11.69/4.54  tff(c_28170, plain, (![B_14]: (k2_zfmisc_1('#skF_4', B_14)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28127, c_28127, c_28116])).
% 11.69/4.54  tff(c_26404, plain, (![B_1552, A_1553]: (B_1552=A_1553 | ~r1_tarski(B_1552, A_1553) | ~r1_tarski(A_1553, B_1552))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.69/4.54  tff(c_26418, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_253, c_26404])).
% 11.69/4.54  tff(c_26507, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_26418])).
% 11.69/4.54  tff(c_26518, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_26362, c_26507])).
% 11.69/4.54  tff(c_28171, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28170, c_26518])).
% 11.69/4.54  tff(c_28174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28080, c_28171])).
% 11.69/4.54  tff(c_28175, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_26418])).
% 11.69/4.54  tff(c_28250, plain, (![C_1687, A_1688, B_1689]: (v1_xboole_0(C_1687) | ~m1_subset_1(C_1687, k1_zfmisc_1(k2_zfmisc_1(A_1688, B_1689))) | ~v1_xboole_0(A_1688))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.69/4.54  tff(c_28253, plain, (![C_1687]: (v1_xboole_0(C_1687) | ~m1_subset_1(C_1687, k1_zfmisc_1('#skF_6')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_28175, c_28250])).
% 11.69/4.54  tff(c_28368, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_28253])).
% 11.69/4.54  tff(c_28185, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28175, c_84])).
% 11.69/4.54  tff(c_28760, plain, (![A_1736, B_1737, C_1738]: (k2_relset_1(A_1736, B_1737, C_1738)=k2_relat_1(C_1738) | ~m1_subset_1(C_1738, k1_zfmisc_1(k2_zfmisc_1(A_1736, B_1737))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.69/4.54  tff(c_28924, plain, (![C_1745]: (k2_relset_1('#skF_4', '#skF_5', C_1745)=k2_relat_1(C_1745) | ~m1_subset_1(C_1745, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_28175, c_28760])).
% 11.69/4.54  tff(c_28930, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_28185, c_28924])).
% 11.69/4.54  tff(c_28937, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_28930])).
% 11.69/4.54  tff(c_29528, plain, (![A_1779, B_1780, C_1781]: (k1_relset_1(A_1779, B_1780, C_1781)=k1_relat_1(C_1781) | ~m1_subset_1(C_1781, k1_zfmisc_1(k2_zfmisc_1(A_1779, B_1780))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.69/4.54  tff(c_29563, plain, (k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_26335, c_29528])).
% 11.69/4.54  tff(c_29873, plain, (![B_1811, C_1812, A_1813]: (k1_xboole_0=B_1811 | v1_funct_2(C_1812, A_1813, B_1811) | k1_relset_1(A_1813, B_1811, C_1812)!=A_1813 | ~m1_subset_1(C_1812, k1_zfmisc_1(k2_zfmisc_1(A_1813, B_1811))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.69/4.54  tff(c_29894, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relset_1('#skF_5', '#skF_4', k2_funct_1('#skF_6'))!='#skF_5'), inference(resolution, [status(thm)], [c_26335, c_29873])).
% 11.69/4.54  tff(c_29912, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k2_funct_1('#skF_6'), '#skF_5', '#skF_4') | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_29563, c_29894])).
% 11.69/4.54  tff(c_29913, plain, (k1_xboole_0='#skF_4' | k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_26334, c_29912])).
% 11.69/4.54  tff(c_29916, plain, (k1_relat_1(k2_funct_1('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_29913])).
% 11.69/4.54  tff(c_29919, plain, (k2_relat_1('#skF_6')!='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_29916])).
% 11.69/4.54  tff(c_29922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26402, c_88, c_82, c_28937, c_29919])).
% 11.69/4.54  tff(c_29923, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_29913])).
% 11.69/4.54  tff(c_29973, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29923, c_12])).
% 11.69/4.54  tff(c_29975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28368, c_29973])).
% 11.69/4.54  tff(c_29977, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_28253])).
% 11.69/4.54  tff(c_29986, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_29977, c_14])).
% 11.69/4.54  tff(c_28199, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_28175, c_22])).
% 11.69/4.54  tff(c_28286, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_28199])).
% 11.69/4.54  tff(c_29993, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29986, c_28286])).
% 11.69/4.54  tff(c_26364, plain, (![A_1545, B_1546]: (m1_subset_1('#skF_3'(A_1545, B_1546), k1_zfmisc_1(k2_zfmisc_1(A_1545, B_1546))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.69/4.54  tff(c_26370, plain, (![B_14]: (m1_subset_1('#skF_3'(k1_xboole_0, B_14), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_26364])).
% 11.69/4.54  tff(c_28266, plain, (![C_1687]: (v1_xboole_0(C_1687) | ~m1_subset_1(C_1687, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_28250])).
% 11.69/4.54  tff(c_28287, plain, (![C_1692]: (v1_xboole_0(C_1692) | ~m1_subset_1(C_1692, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28266])).
% 11.69/4.54  tff(c_28311, plain, (![B_1694]: (v1_xboole_0('#skF_3'(k1_xboole_0, B_1694)))), inference(resolution, [status(thm)], [c_26370, c_28287])).
% 11.69/4.54  tff(c_28320, plain, (![B_1694]: ('#skF_3'(k1_xboole_0, B_1694)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28311, c_14])).
% 11.69/4.54  tff(c_30023, plain, (![B_1694]: ('#skF_3'('#skF_4', B_1694)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29986, c_29986, c_28320])).
% 11.69/4.54  tff(c_28196, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_28175, c_70])).
% 11.69/4.54  tff(c_28225, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_28196, c_28])).
% 11.69/4.54  tff(c_30024, plain, (r1_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30023, c_28225])).
% 11.69/4.54  tff(c_16, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.69/4.54  tff(c_30061, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_30024, c_16])).
% 11.69/4.54  tff(c_30066, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_29993, c_30061])).
% 11.69/4.54  tff(c_30072, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_26362, c_30066])).
% 11.69/4.54  tff(c_30096, plain, (![C_1818]: (v1_xboole_0(C_1818) | ~m1_subset_1(C_1818, k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_28253])).
% 11.69/4.54  tff(c_30102, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_28185, c_30096])).
% 11.69/4.54  tff(c_30112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30072, c_30102])).
% 11.69/4.54  tff(c_30114, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_28199])).
% 11.69/4.54  tff(c_30126, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30114, c_12])).
% 11.69/4.54  tff(c_30113, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_28199])).
% 11.69/4.54  tff(c_30137, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_30114, c_30114, c_30113])).
% 11.69/4.54  tff(c_30138, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_30137])).
% 11.69/4.54  tff(c_28271, plain, (v1_xboole_0(k2_funct_1('#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_26335, c_28250])).
% 11.69/4.54  tff(c_28275, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_28271])).
% 11.69/4.54  tff(c_30139, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30138, c_28275])).
% 11.69/4.54  tff(c_30150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30126, c_30139])).
% 11.69/4.54  tff(c_30151, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_30137])).
% 11.69/4.54  tff(c_30152, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_30137])).
% 11.69/4.54  tff(c_30196, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30151, c_30152])).
% 11.69/4.54  tff(c_30154, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30151, c_30114])).
% 11.69/4.54  tff(c_30, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.69/4.54  tff(c_48, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.69/4.54  tff(c_92, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_48])).
% 11.69/4.54  tff(c_30175, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_92])).
% 11.69/4.54  tff(c_30186, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30154, c_30154, c_30175])).
% 11.69/4.54  tff(c_30189, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_30186])).
% 11.69/4.54  tff(c_30193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_30189])).
% 11.69/4.54  tff(c_30194, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32)), inference(splitRight, [status(thm)], [c_92])).
% 11.69/4.54  tff(c_30291, plain, (![A_32]: (v1_funct_2('#skF_4', A_32, '#skF_4') | A_32='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30154, c_30154, c_30154, c_30194])).
% 11.69/4.54  tff(c_30124, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30114, c_30114, c_24])).
% 11.69/4.54  tff(c_30223, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30151, c_30151, c_30124])).
% 11.69/4.54  tff(c_30164, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_30151, c_26335])).
% 11.69/4.54  tff(c_30315, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30223, c_30164])).
% 11.69/4.54  tff(c_28274, plain, (![C_1687]: (v1_xboole_0(C_1687) | ~m1_subset_1(C_1687, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28266])).
% 11.69/4.54  tff(c_30330, plain, (![C_1826]: (v1_xboole_0(C_1826) | ~m1_subset_1(C_1826, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_30154, c_28274])).
% 11.69/4.54  tff(c_30341, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30315, c_30330])).
% 11.69/4.54  tff(c_30125, plain, (![A_10]: (A_10='#skF_6' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_30114, c_14])).
% 11.69/4.54  tff(c_30212, plain, (![A_10]: (A_10='#skF_4' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_30151, c_30125])).
% 11.69/4.54  tff(c_30351, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_30341, c_30212])).
% 11.69/4.54  tff(c_30165, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30151, c_26334])).
% 11.69/4.54  tff(c_30357, plain, (~v1_funct_2('#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30351, c_30165])).
% 11.69/4.54  tff(c_30382, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_30291, c_30357])).
% 11.69/4.54  tff(c_30386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30196, c_30382])).
% 11.69/4.54  tff(c_30388, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_28271])).
% 11.69/4.54  tff(c_30396, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_30388, c_14])).
% 11.69/4.54  tff(c_30476, plain, (![A_1831]: (k2_zfmisc_1(A_1831, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30396, c_30396, c_24])).
% 11.69/4.54  tff(c_30486, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_30476, c_28175])).
% 11.69/4.54  tff(c_26375, plain, (![B_1547]: (m1_subset_1('#skF_3'(k1_xboole_0, B_1547), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_26364])).
% 11.69/4.54  tff(c_26379, plain, (![B_1547]: (r1_tarski('#skF_3'(k1_xboole_0, B_1547), k1_xboole_0))), inference(resolution, [status(thm)], [c_26375, c_28])).
% 11.69/4.54  tff(c_30402, plain, (![B_1547]: (r1_tarski('#skF_3'('#skF_5', B_1547), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30396, c_30396, c_26379])).
% 11.69/4.54  tff(c_30633, plain, (![B_1547]: (r1_tarski('#skF_3'('#skF_6', B_1547), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30486, c_30486, c_30402])).
% 11.69/4.54  tff(c_30515, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_30486, c_30396])).
% 11.69/4.54  tff(c_30696, plain, (![C_1841]: (v1_xboole_0(C_1841) | ~m1_subset_1(C_1841, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_30515, c_28274])).
% 11.69/4.54  tff(c_30724, plain, (![A_1843]: (v1_xboole_0(A_1843) | ~r1_tarski(A_1843, '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_30696])).
% 11.69/4.54  tff(c_30754, plain, (![B_1845]: (v1_xboole_0('#skF_3'('#skF_6', B_1845)))), inference(resolution, [status(thm)], [c_30633, c_30724])).
% 11.69/4.54  tff(c_30407, plain, (![A_10]: (A_10='#skF_5' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_30396, c_14])).
% 11.69/4.54  tff(c_30513, plain, (![A_10]: (A_10='#skF_6' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_30486, c_30407])).
% 11.69/4.54  tff(c_30813, plain, (![B_1848]: ('#skF_3'('#skF_6', B_1848)='#skF_6')), inference(resolution, [status(thm)], [c_30754, c_30513])).
% 11.69/4.54  tff(c_30827, plain, (![B_1848]: (v1_funct_2('#skF_6', '#skF_6', B_1848))), inference(superposition, [status(thm), theory('equality')], [c_30813, c_60])).
% 11.69/4.54  tff(c_30387, plain, (v1_xboole_0(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_28271])).
% 11.69/4.54  tff(c_30420, plain, (![A_1828]: (A_1828='#skF_5' | ~v1_xboole_0(A_1828))), inference(demodulation, [status(thm), theory('equality')], [c_30396, c_14])).
% 11.69/4.54  tff(c_30427, plain, (k2_funct_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_30387, c_30420])).
% 11.69/4.54  tff(c_30434, plain, (~v1_funct_2('#skF_5', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30427, c_26334])).
% 11.69/4.54  tff(c_30508, plain, (~v1_funct_2('#skF_6', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30486, c_30486, c_30434])).
% 11.69/4.54  tff(c_30886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30827, c_30508])).
% 11.69/4.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.69/4.54  
% 11.69/4.54  Inference rules
% 11.69/4.54  ----------------------
% 11.69/4.54  #Ref     : 0
% 11.69/4.54  #Sup     : 7306
% 11.69/4.54  #Fact    : 0
% 11.69/4.54  #Define  : 0
% 11.69/4.54  #Split   : 48
% 11.69/4.54  #Chain   : 0
% 11.69/4.54  #Close   : 0
% 11.69/4.54  
% 11.69/4.54  Ordering : KBO
% 11.69/4.54  
% 11.69/4.54  Simplification rules
% 11.69/4.54  ----------------------
% 11.69/4.54  #Subsume      : 1156
% 11.69/4.54  #Demod        : 7379
% 11.69/4.54  #Tautology    : 3949
% 11.69/4.54  #SimpNegUnit  : 34
% 11.69/4.54  #BackRed      : 524
% 11.69/4.54  
% 11.69/4.54  #Partial instantiations: 0
% 11.69/4.54  #Strategies tried      : 1
% 11.69/4.54  
% 11.69/4.54  Timing (in seconds)
% 11.69/4.54  ----------------------
% 11.69/4.54  Preprocessing        : 0.34
% 11.69/4.54  Parsing              : 0.18
% 11.69/4.54  CNF conversion       : 0.02
% 11.69/4.54  Main loop            : 3.34
% 11.69/4.54  Inferencing          : 0.98
% 11.69/4.54  Reduction            : 1.21
% 11.69/4.54  Demodulation         : 0.91
% 11.69/4.54  BG Simplification    : 0.11
% 11.69/4.54  Subsumption          : 0.78
% 11.69/4.54  Abstraction          : 0.16
% 11.69/4.54  MUC search           : 0.00
% 11.69/4.54  Cooper               : 0.00
% 11.69/4.54  Total                : 3.81
% 11.69/4.54  Index Insertion      : 0.00
% 11.69/4.54  Index Deletion       : 0.00
% 11.69/4.54  Index Matching       : 0.00
% 11.69/4.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
