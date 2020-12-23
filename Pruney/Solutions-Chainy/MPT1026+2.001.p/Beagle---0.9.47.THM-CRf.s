%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:38 EST 2020

% Result     : Theorem 9.58s
% Output     : CNFRefutation 9.85s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 264 expanded)
%              Number of leaves         :   49 ( 102 expanded)
%              Depth                    :   12
%              Number of atoms          :  221 ( 597 expanded)
%              Number of equality atoms :   40 (  77 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > o_1_0_funct_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_9 > #skF_10 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_1_0_funct_1,type,(
    o_1_0_funct_1: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_172,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_102,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_156,axiom,(
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

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_110,plain,(
    r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1851,plain,(
    ! [A_342,B_343,D_344] :
      ( '#skF_9'(A_342,B_343,k1_funct_2(A_342,B_343),D_344) = D_344
      | ~ r2_hidden(D_344,k1_funct_2(A_342,B_343)) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1878,plain,(
    '#skF_9'('#skF_10','#skF_11',k1_funct_2('#skF_10','#skF_11'),'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_110,c_1851])).

tff(c_82,plain,(
    ! [A_65,B_66,D_81] :
      ( v1_relat_1('#skF_9'(A_65,B_66,k1_funct_2(A_65,B_66),D_81))
      | ~ r2_hidden(D_81,k1_funct_2(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1886,plain,
    ( v1_relat_1('#skF_12')
    | ~ r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1878,c_82])).

tff(c_1892,plain,(
    v1_relat_1('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1886])).

tff(c_1124,plain,(
    ! [A_246,B_247] :
      ( r2_hidden('#skF_2'(A_246,B_247),A_246)
      | r1_tarski(A_246,B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1135,plain,(
    ! [A_246] : r1_tarski(A_246,A_246) ),
    inference(resolution,[status(thm)],[c_1124,c_8])).

tff(c_2018,plain,(
    ! [A_355,B_356,D_357] :
      ( k1_relat_1('#skF_9'(A_355,B_356,k1_funct_2(A_355,B_356),D_357)) = A_355
      | ~ r2_hidden(D_357,k1_funct_2(A_355,B_356)) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2033,plain,
    ( k1_relat_1('#skF_12') = '#skF_10'
    | ~ r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1878,c_2018])).

tff(c_2037,plain,(
    k1_relat_1('#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2033])).

tff(c_3838,plain,(
    ! [A_484,B_485,D_486] :
      ( r1_tarski(k2_relat_1('#skF_9'(A_484,B_485,k1_funct_2(A_484,B_485),D_486)),B_485)
      | ~ r2_hidden(D_486,k1_funct_2(A_484,B_485)) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_3870,plain,
    ( r1_tarski(k2_relat_1('#skF_12'),'#skF_11')
    | ~ r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1878,c_3838])).

tff(c_3880,plain,(
    r1_tarski(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_3870])).

tff(c_4319,plain,(
    ! [C_522,A_523,B_524] :
      ( m1_subset_1(C_522,k1_zfmisc_1(k2_zfmisc_1(A_523,B_524)))
      | ~ r1_tarski(k2_relat_1(C_522),B_524)
      | ~ r1_tarski(k1_relat_1(C_522),A_523)
      | ~ v1_relat_1(C_522) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_108,plain,
    ( ~ m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11')))
    | ~ v1_funct_2('#skF_12','#skF_10','#skF_11')
    | ~ v1_funct_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_136,plain,(
    ~ v1_funct_1('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_972,plain,(
    ! [A_218,B_219,D_220] :
      ( '#skF_9'(A_218,B_219,k1_funct_2(A_218,B_219),D_220) = D_220
      | ~ r2_hidden(D_220,k1_funct_2(A_218,B_219)) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_999,plain,(
    '#skF_9'('#skF_10','#skF_11',k1_funct_2('#skF_10','#skF_11'),'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_110,c_972])).

tff(c_80,plain,(
    ! [A_65,B_66,D_81] :
      ( v1_funct_1('#skF_9'(A_65,B_66,k1_funct_2(A_65,B_66),D_81))
      | ~ r2_hidden(D_81,k1_funct_2(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1003,plain,
    ( v1_funct_1('#skF_12')
    | ~ r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_80])).

tff(c_1010,plain,(
    v1_funct_1('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1003])).

tff(c_1012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_1010])).

tff(c_1013,plain,
    ( ~ v1_funct_2('#skF_12','#skF_10','#skF_11')
    | ~ m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11'))) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_1045,plain,(
    ~ m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11'))) ),
    inference(splitLeft,[status(thm)],[c_1013])).

tff(c_4359,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_12'),'#skF_11')
    | ~ r1_tarski(k1_relat_1('#skF_12'),'#skF_10')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_4319,c_1045])).

tff(c_4381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1892,c_1135,c_2037,c_3880,c_4359])).

tff(c_4382,plain,(
    ~ v1_funct_2('#skF_12','#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_1013])).

tff(c_1014,plain,(
    v1_funct_1('#skF_12') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_4383,plain,(
    m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11'))) ),
    inference(splitRight,[status(thm)],[c_1013])).

tff(c_10746,plain,(
    ! [C_947,A_948,B_949] :
      ( v1_partfun1(C_947,A_948)
      | ~ m1_subset_1(C_947,k1_zfmisc_1(k2_zfmisc_1(A_948,B_949)))
      | ~ v1_xboole_0(A_948) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_10782,plain,
    ( v1_partfun1('#skF_12','#skF_10')
    | ~ v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4383,c_10746])).

tff(c_10785,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_10782])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ v1_xboole_0(B_11)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4403,plain,(
    ! [A_536,B_537] :
      ( r1_tarski(A_536,B_537)
      | ~ m1_subset_1(A_536,k1_zfmisc_1(B_537)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4423,plain,(
    r1_tarski('#skF_12',k2_zfmisc_1('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_4383,c_4403])).

tff(c_4447,plain,(
    ! [B_540,A_541] :
      ( r2_hidden(B_540,A_541)
      | ~ m1_subset_1(B_540,A_541)
      | v1_xboole_0(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    ! [B_44,A_43] :
      ( ~ r1_tarski(B_44,A_43)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4544,plain,(
    ! [A_555,B_556] :
      ( ~ r1_tarski(A_555,B_556)
      | ~ m1_subset_1(B_556,A_555)
      | v1_xboole_0(A_555) ) ),
    inference(resolution,[status(thm)],[c_4447,c_46])).

tff(c_4567,plain,
    ( ~ m1_subset_1(k2_zfmisc_1('#skF_10','#skF_11'),'#skF_12')
    | v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_4423,c_4544])).

tff(c_4605,plain,(
    ~ m1_subset_1(k2_zfmisc_1('#skF_10','#skF_11'),'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_4567])).

tff(c_4609,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_10','#skF_11'))
    | ~ v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_16,c_4605])).

tff(c_4622,plain,(
    ~ v1_xboole_0('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_4609])).

tff(c_4656,plain,(
    ! [C_567,B_568,A_569] :
      ( v1_xboole_0(C_567)
      | ~ m1_subset_1(C_567,k1_zfmisc_1(k2_zfmisc_1(B_568,A_569)))
      | ~ v1_xboole_0(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4675,plain,
    ( v1_xboole_0('#skF_12')
    | ~ v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_4383,c_4656])).

tff(c_4694,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_4622,c_4675])).

tff(c_5158,plain,(
    ! [A_632,B_633,D_634] :
      ( '#skF_9'(A_632,B_633,k1_funct_2(A_632,B_633),D_634) = D_634
      | ~ r2_hidden(D_634,k1_funct_2(A_632,B_633)) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_5185,plain,(
    '#skF_9'('#skF_10','#skF_11',k1_funct_2('#skF_10','#skF_11'),'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_110,c_5158])).

tff(c_5294,plain,(
    ! [A_644,B_645,D_646] :
      ( k1_relat_1('#skF_9'(A_644,B_645,k1_funct_2(A_644,B_645),D_646)) = A_644
      | ~ r2_hidden(D_646,k1_funct_2(A_644,B_645)) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_5306,plain,
    ( k1_relat_1('#skF_12') = '#skF_10'
    | ~ r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5185,c_5294])).

tff(c_5310,plain,(
    k1_relat_1('#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_5306])).

tff(c_4939,plain,(
    ! [A_602,B_603,C_604] :
      ( k1_relset_1(A_602,B_603,C_604) = k1_relat_1(C_604)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(A_602,B_603))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4975,plain,(
    k1_relset_1('#skF_10','#skF_11','#skF_12') = k1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_4383,c_4939])).

tff(c_5311,plain,(
    k1_relset_1('#skF_10','#skF_11','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5310,c_4975])).

tff(c_10283,plain,(
    ! [B_915,C_916,A_917] :
      ( k1_xboole_0 = B_915
      | v1_funct_2(C_916,A_917,B_915)
      | k1_relset_1(A_917,B_915,C_916) != A_917
      | ~ m1_subset_1(C_916,k1_zfmisc_1(k2_zfmisc_1(A_917,B_915))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_10328,plain,
    ( k1_xboole_0 = '#skF_11'
    | v1_funct_2('#skF_12','#skF_10','#skF_11')
    | k1_relset_1('#skF_10','#skF_11','#skF_12') != '#skF_10' ),
    inference(resolution,[status(thm)],[c_4383,c_10283])).

tff(c_10356,plain,
    ( k1_xboole_0 = '#skF_11'
    | v1_funct_2('#skF_12','#skF_10','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5311,c_10328])).

tff(c_10357,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_4382,c_10356])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4426,plain,(
    ! [A_538] : r1_tarski(k1_xboole_0,A_538) ),
    inference(resolution,[status(thm)],[c_20,c_4403])).

tff(c_1015,plain,(
    ! [A_221] :
      ( v1_xboole_0(A_221)
      | r2_hidden('#skF_1'(A_221),A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1022,plain,(
    ! [A_221] :
      ( ~ r1_tarski(A_221,'#skF_1'(A_221))
      | v1_xboole_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_1015,c_46])).

tff(c_4435,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4426,c_1022])).

tff(c_10416,plain,(
    v1_xboole_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10357,c_4435])).

tff(c_10422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4694,c_10416])).

tff(c_10424,plain,(
    v1_xboole_0('#skF_12') ),
    inference(splitRight,[status(thm)],[c_4609])).

tff(c_121,plain,(
    ! [A_90] :
      ( r2_hidden('#skF_3'(A_90),A_90)
      | v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [A_90] :
      ( ~ v1_xboole_0(A_90)
      | v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_10431,plain,(
    v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_10424,c_125])).

tff(c_11058,plain,(
    ! [A_1000,B_1001,D_1002] :
      ( '#skF_9'(A_1000,B_1001,k1_funct_2(A_1000,B_1001),D_1002) = D_1002
      | ~ r2_hidden(D_1002,k1_funct_2(A_1000,B_1001)) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_11085,plain,(
    '#skF_9'('#skF_10','#skF_11',k1_funct_2('#skF_10','#skF_11'),'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_110,c_11058])).

tff(c_11351,plain,(
    ! [A_1017,B_1018,D_1019] :
      ( k1_relat_1('#skF_9'(A_1017,B_1018,k1_funct_2(A_1017,B_1018),D_1019)) = A_1017
      | ~ r2_hidden(D_1019,k1_funct_2(A_1017,B_1018)) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_11366,plain,
    ( k1_relat_1('#skF_12') = '#skF_10'
    | ~ r2_hidden('#skF_12',k1_funct_2('#skF_10','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11085,c_11351])).

tff(c_11370,plain,(
    k1_relat_1('#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_11366])).

tff(c_11590,plain,(
    ! [B_1031,A_1032] :
      ( r2_hidden(k4_tarski(B_1031,k1_funct_1(A_1032,B_1031)),A_1032)
      | ~ r2_hidden(B_1031,k1_relat_1(A_1032))
      | ~ v1_funct_1(A_1032)
      | ~ v1_relat_1(A_1032) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_11749,plain,(
    ! [A_1043,B_1044] :
      ( ~ v1_xboole_0(A_1043)
      | ~ r2_hidden(B_1044,k1_relat_1(A_1043))
      | ~ v1_funct_1(A_1043)
      | ~ v1_relat_1(A_1043) ) ),
    inference(resolution,[status(thm)],[c_11590,c_2])).

tff(c_11760,plain,(
    ! [B_1044] :
      ( ~ v1_xboole_0('#skF_12')
      | ~ r2_hidden(B_1044,'#skF_10')
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11370,c_11749])).

tff(c_11803,plain,(
    ! [B_1045] : ~ r2_hidden(B_1045,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10431,c_1014,c_10424,c_11760])).

tff(c_11831,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4,c_11803])).

tff(c_11847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10785,c_11831])).

tff(c_11848,plain,(
    v1_partfun1('#skF_12','#skF_10') ),
    inference(splitRight,[status(thm)],[c_10782])).

tff(c_12857,plain,(
    ! [C_1130,A_1131,B_1132] :
      ( v1_funct_2(C_1130,A_1131,B_1132)
      | ~ v1_partfun1(C_1130,A_1131)
      | ~ v1_funct_1(C_1130)
      | ~ m1_subset_1(C_1130,k1_zfmisc_1(k2_zfmisc_1(A_1131,B_1132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_12884,plain,
    ( v1_funct_2('#skF_12','#skF_10','#skF_11')
    | ~ v1_partfun1('#skF_12','#skF_10')
    | ~ v1_funct_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_4383,c_12857])).

tff(c_12905,plain,(
    v1_funct_2('#skF_12','#skF_10','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1014,c_11848,c_12884])).

tff(c_12907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4382,c_12905])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:10:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.58/3.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.58/3.17  
% 9.58/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.58/3.17  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > o_1_0_funct_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_9 > #skF_10 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_5 > #skF_12 > #skF_4
% 9.58/3.17  
% 9.58/3.17  %Foreground sorts:
% 9.58/3.17  
% 9.58/3.17  
% 9.58/3.17  %Background operators:
% 9.58/3.17  
% 9.58/3.17  
% 9.58/3.17  %Foreground operators:
% 9.58/3.17  tff(o_1_0_funct_1, type, o_1_0_funct_1: $i > $i).
% 9.58/3.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.58/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.58/3.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.58/3.17  tff('#skF_11', type, '#skF_11': $i).
% 9.58/3.17  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.58/3.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.58/3.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.58/3.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.58/3.17  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 9.58/3.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.58/3.17  tff('#skF_10', type, '#skF_10': $i).
% 9.58/3.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.58/3.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.58/3.17  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.58/3.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.58/3.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.58/3.17  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.58/3.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.58/3.17  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 9.58/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.58/3.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.58/3.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.58/3.17  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.58/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.58/3.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.58/3.17  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 9.58/3.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.58/3.17  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.58/3.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.58/3.17  tff('#skF_12', type, '#skF_12': $i).
% 9.58/3.17  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.58/3.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.58/3.17  
% 9.85/3.20  tff(f_181, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 9.85/3.20  tff(f_172, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 9.85/3.20  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.85/3.20  tff(f_121, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 9.85/3.20  tff(f_138, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 9.85/3.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.85/3.20  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 9.85/3.20  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.85/3.20  tff(f_102, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.85/3.20  tff(f_109, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 9.85/3.20  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.85/3.20  tff(f_156, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.85/3.20  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.85/3.20  tff(f_73, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 9.85/3.20  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 9.85/3.20  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 9.85/3.20  tff(c_110, plain, (r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.85/3.20  tff(c_1851, plain, (![A_342, B_343, D_344]: ('#skF_9'(A_342, B_343, k1_funct_2(A_342, B_343), D_344)=D_344 | ~r2_hidden(D_344, k1_funct_2(A_342, B_343)))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.85/3.20  tff(c_1878, plain, ('#skF_9'('#skF_10', '#skF_11', k1_funct_2('#skF_10', '#skF_11'), '#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_110, c_1851])).
% 9.85/3.20  tff(c_82, plain, (![A_65, B_66, D_81]: (v1_relat_1('#skF_9'(A_65, B_66, k1_funct_2(A_65, B_66), D_81)) | ~r2_hidden(D_81, k1_funct_2(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.85/3.20  tff(c_1886, plain, (v1_relat_1('#skF_12') | ~r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_1878, c_82])).
% 9.85/3.20  tff(c_1892, plain, (v1_relat_1('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1886])).
% 9.85/3.20  tff(c_1124, plain, (![A_246, B_247]: (r2_hidden('#skF_2'(A_246, B_247), A_246) | r1_tarski(A_246, B_247))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.85/3.20  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.85/3.20  tff(c_1135, plain, (![A_246]: (r1_tarski(A_246, A_246))), inference(resolution, [status(thm)], [c_1124, c_8])).
% 9.85/3.20  tff(c_2018, plain, (![A_355, B_356, D_357]: (k1_relat_1('#skF_9'(A_355, B_356, k1_funct_2(A_355, B_356), D_357))=A_355 | ~r2_hidden(D_357, k1_funct_2(A_355, B_356)))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.85/3.20  tff(c_2033, plain, (k1_relat_1('#skF_12')='#skF_10' | ~r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_1878, c_2018])).
% 9.85/3.20  tff(c_2037, plain, (k1_relat_1('#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2033])).
% 9.85/3.20  tff(c_3838, plain, (![A_484, B_485, D_486]: (r1_tarski(k2_relat_1('#skF_9'(A_484, B_485, k1_funct_2(A_484, B_485), D_486)), B_485) | ~r2_hidden(D_486, k1_funct_2(A_484, B_485)))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.85/3.20  tff(c_3870, plain, (r1_tarski(k2_relat_1('#skF_12'), '#skF_11') | ~r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_1878, c_3838])).
% 9.85/3.20  tff(c_3880, plain, (r1_tarski(k2_relat_1('#skF_12'), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_3870])).
% 9.85/3.20  tff(c_4319, plain, (![C_522, A_523, B_524]: (m1_subset_1(C_522, k1_zfmisc_1(k2_zfmisc_1(A_523, B_524))) | ~r1_tarski(k2_relat_1(C_522), B_524) | ~r1_tarski(k1_relat_1(C_522), A_523) | ~v1_relat_1(C_522))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.85/3.20  tff(c_108, plain, (~m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11'))) | ~v1_funct_2('#skF_12', '#skF_10', '#skF_11') | ~v1_funct_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.85/3.20  tff(c_136, plain, (~v1_funct_1('#skF_12')), inference(splitLeft, [status(thm)], [c_108])).
% 9.85/3.20  tff(c_972, plain, (![A_218, B_219, D_220]: ('#skF_9'(A_218, B_219, k1_funct_2(A_218, B_219), D_220)=D_220 | ~r2_hidden(D_220, k1_funct_2(A_218, B_219)))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.85/3.20  tff(c_999, plain, ('#skF_9'('#skF_10', '#skF_11', k1_funct_2('#skF_10', '#skF_11'), '#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_110, c_972])).
% 9.85/3.20  tff(c_80, plain, (![A_65, B_66, D_81]: (v1_funct_1('#skF_9'(A_65, B_66, k1_funct_2(A_65, B_66), D_81)) | ~r2_hidden(D_81, k1_funct_2(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.85/3.20  tff(c_1003, plain, (v1_funct_1('#skF_12') | ~r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_999, c_80])).
% 9.85/3.20  tff(c_1010, plain, (v1_funct_1('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1003])).
% 9.85/3.20  tff(c_1012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_1010])).
% 9.85/3.20  tff(c_1013, plain, (~v1_funct_2('#skF_12', '#skF_10', '#skF_11') | ~m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11')))), inference(splitRight, [status(thm)], [c_108])).
% 9.85/3.20  tff(c_1045, plain, (~m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11')))), inference(splitLeft, [status(thm)], [c_1013])).
% 9.85/3.20  tff(c_4359, plain, (~r1_tarski(k2_relat_1('#skF_12'), '#skF_11') | ~r1_tarski(k1_relat_1('#skF_12'), '#skF_10') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_4319, c_1045])).
% 9.85/3.20  tff(c_4381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1892, c_1135, c_2037, c_3880, c_4359])).
% 9.85/3.20  tff(c_4382, plain, (~v1_funct_2('#skF_12', '#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_1013])).
% 9.85/3.20  tff(c_1014, plain, (v1_funct_1('#skF_12')), inference(splitRight, [status(thm)], [c_108])).
% 9.85/3.20  tff(c_4383, plain, (m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11')))), inference(splitRight, [status(thm)], [c_1013])).
% 9.85/3.20  tff(c_10746, plain, (![C_947, A_948, B_949]: (v1_partfun1(C_947, A_948) | ~m1_subset_1(C_947, k1_zfmisc_1(k2_zfmisc_1(A_948, B_949))) | ~v1_xboole_0(A_948))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.85/3.20  tff(c_10782, plain, (v1_partfun1('#skF_12', '#skF_10') | ~v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_4383, c_10746])).
% 9.85/3.20  tff(c_10785, plain, (~v1_xboole_0('#skF_10')), inference(splitLeft, [status(thm)], [c_10782])).
% 9.85/3.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.85/3.20  tff(c_16, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~v1_xboole_0(B_11) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.85/3.20  tff(c_4403, plain, (![A_536, B_537]: (r1_tarski(A_536, B_537) | ~m1_subset_1(A_536, k1_zfmisc_1(B_537)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.85/3.20  tff(c_4423, plain, (r1_tarski('#skF_12', k2_zfmisc_1('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_4383, c_4403])).
% 9.85/3.20  tff(c_4447, plain, (![B_540, A_541]: (r2_hidden(B_540, A_541) | ~m1_subset_1(B_540, A_541) | v1_xboole_0(A_541))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.85/3.20  tff(c_46, plain, (![B_44, A_43]: (~r1_tarski(B_44, A_43) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.85/3.20  tff(c_4544, plain, (![A_555, B_556]: (~r1_tarski(A_555, B_556) | ~m1_subset_1(B_556, A_555) | v1_xboole_0(A_555))), inference(resolution, [status(thm)], [c_4447, c_46])).
% 9.85/3.20  tff(c_4567, plain, (~m1_subset_1(k2_zfmisc_1('#skF_10', '#skF_11'), '#skF_12') | v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_4423, c_4544])).
% 9.85/3.20  tff(c_4605, plain, (~m1_subset_1(k2_zfmisc_1('#skF_10', '#skF_11'), '#skF_12')), inference(splitLeft, [status(thm)], [c_4567])).
% 9.85/3.20  tff(c_4609, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_10', '#skF_11')) | ~v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_16, c_4605])).
% 9.85/3.20  tff(c_4622, plain, (~v1_xboole_0('#skF_12')), inference(splitLeft, [status(thm)], [c_4609])).
% 9.85/3.20  tff(c_4656, plain, (![C_567, B_568, A_569]: (v1_xboole_0(C_567) | ~m1_subset_1(C_567, k1_zfmisc_1(k2_zfmisc_1(B_568, A_569))) | ~v1_xboole_0(A_569))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.85/3.20  tff(c_4675, plain, (v1_xboole_0('#skF_12') | ~v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_4383, c_4656])).
% 9.85/3.20  tff(c_4694, plain, (~v1_xboole_0('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_4622, c_4675])).
% 9.85/3.20  tff(c_5158, plain, (![A_632, B_633, D_634]: ('#skF_9'(A_632, B_633, k1_funct_2(A_632, B_633), D_634)=D_634 | ~r2_hidden(D_634, k1_funct_2(A_632, B_633)))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.85/3.20  tff(c_5185, plain, ('#skF_9'('#skF_10', '#skF_11', k1_funct_2('#skF_10', '#skF_11'), '#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_110, c_5158])).
% 9.85/3.20  tff(c_5294, plain, (![A_644, B_645, D_646]: (k1_relat_1('#skF_9'(A_644, B_645, k1_funct_2(A_644, B_645), D_646))=A_644 | ~r2_hidden(D_646, k1_funct_2(A_644, B_645)))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.85/3.20  tff(c_5306, plain, (k1_relat_1('#skF_12')='#skF_10' | ~r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_5185, c_5294])).
% 9.85/3.20  tff(c_5310, plain, (k1_relat_1('#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_5306])).
% 9.85/3.20  tff(c_4939, plain, (![A_602, B_603, C_604]: (k1_relset_1(A_602, B_603, C_604)=k1_relat_1(C_604) | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(A_602, B_603))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.85/3.20  tff(c_4975, plain, (k1_relset_1('#skF_10', '#skF_11', '#skF_12')=k1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_4383, c_4939])).
% 9.85/3.20  tff(c_5311, plain, (k1_relset_1('#skF_10', '#skF_11', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_5310, c_4975])).
% 9.85/3.20  tff(c_10283, plain, (![B_915, C_916, A_917]: (k1_xboole_0=B_915 | v1_funct_2(C_916, A_917, B_915) | k1_relset_1(A_917, B_915, C_916)!=A_917 | ~m1_subset_1(C_916, k1_zfmisc_1(k2_zfmisc_1(A_917, B_915))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.85/3.20  tff(c_10328, plain, (k1_xboole_0='#skF_11' | v1_funct_2('#skF_12', '#skF_10', '#skF_11') | k1_relset_1('#skF_10', '#skF_11', '#skF_12')!='#skF_10'), inference(resolution, [status(thm)], [c_4383, c_10283])).
% 9.85/3.20  tff(c_10356, plain, (k1_xboole_0='#skF_11' | v1_funct_2('#skF_12', '#skF_10', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_5311, c_10328])).
% 9.85/3.20  tff(c_10357, plain, (k1_xboole_0='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_4382, c_10356])).
% 9.85/3.20  tff(c_20, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.85/3.20  tff(c_4426, plain, (![A_538]: (r1_tarski(k1_xboole_0, A_538))), inference(resolution, [status(thm)], [c_20, c_4403])).
% 9.85/3.20  tff(c_1015, plain, (![A_221]: (v1_xboole_0(A_221) | r2_hidden('#skF_1'(A_221), A_221))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.85/3.20  tff(c_1022, plain, (![A_221]: (~r1_tarski(A_221, '#skF_1'(A_221)) | v1_xboole_0(A_221))), inference(resolution, [status(thm)], [c_1015, c_46])).
% 9.85/3.20  tff(c_4435, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4426, c_1022])).
% 9.85/3.20  tff(c_10416, plain, (v1_xboole_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_10357, c_4435])).
% 9.85/3.20  tff(c_10422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4694, c_10416])).
% 9.85/3.20  tff(c_10424, plain, (v1_xboole_0('#skF_12')), inference(splitRight, [status(thm)], [c_4609])).
% 9.85/3.20  tff(c_121, plain, (![A_90]: (r2_hidden('#skF_3'(A_90), A_90) | v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.85/3.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.85/3.20  tff(c_125, plain, (![A_90]: (~v1_xboole_0(A_90) | v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_121, c_2])).
% 9.85/3.20  tff(c_10431, plain, (v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_10424, c_125])).
% 9.85/3.20  tff(c_11058, plain, (![A_1000, B_1001, D_1002]: ('#skF_9'(A_1000, B_1001, k1_funct_2(A_1000, B_1001), D_1002)=D_1002 | ~r2_hidden(D_1002, k1_funct_2(A_1000, B_1001)))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.85/3.20  tff(c_11085, plain, ('#skF_9'('#skF_10', '#skF_11', k1_funct_2('#skF_10', '#skF_11'), '#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_110, c_11058])).
% 9.85/3.20  tff(c_11351, plain, (![A_1017, B_1018, D_1019]: (k1_relat_1('#skF_9'(A_1017, B_1018, k1_funct_2(A_1017, B_1018), D_1019))=A_1017 | ~r2_hidden(D_1019, k1_funct_2(A_1017, B_1018)))), inference(cnfTransformation, [status(thm)], [f_172])).
% 9.85/3.20  tff(c_11366, plain, (k1_relat_1('#skF_12')='#skF_10' | ~r2_hidden('#skF_12', k1_funct_2('#skF_10', '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_11085, c_11351])).
% 9.85/3.20  tff(c_11370, plain, (k1_relat_1('#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_11366])).
% 9.85/3.20  tff(c_11590, plain, (![B_1031, A_1032]: (r2_hidden(k4_tarski(B_1031, k1_funct_1(A_1032, B_1031)), A_1032) | ~r2_hidden(B_1031, k1_relat_1(A_1032)) | ~v1_funct_1(A_1032) | ~v1_relat_1(A_1032))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.85/3.20  tff(c_11749, plain, (![A_1043, B_1044]: (~v1_xboole_0(A_1043) | ~r2_hidden(B_1044, k1_relat_1(A_1043)) | ~v1_funct_1(A_1043) | ~v1_relat_1(A_1043))), inference(resolution, [status(thm)], [c_11590, c_2])).
% 9.85/3.20  tff(c_11760, plain, (![B_1044]: (~v1_xboole_0('#skF_12') | ~r2_hidden(B_1044, '#skF_10') | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_11370, c_11749])).
% 9.85/3.20  tff(c_11803, plain, (![B_1045]: (~r2_hidden(B_1045, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_10431, c_1014, c_10424, c_11760])).
% 9.85/3.20  tff(c_11831, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_4, c_11803])).
% 9.85/3.20  tff(c_11847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10785, c_11831])).
% 9.85/3.20  tff(c_11848, plain, (v1_partfun1('#skF_12', '#skF_10')), inference(splitRight, [status(thm)], [c_10782])).
% 9.85/3.20  tff(c_12857, plain, (![C_1130, A_1131, B_1132]: (v1_funct_2(C_1130, A_1131, B_1132) | ~v1_partfun1(C_1130, A_1131) | ~v1_funct_1(C_1130) | ~m1_subset_1(C_1130, k1_zfmisc_1(k2_zfmisc_1(A_1131, B_1132))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.85/3.20  tff(c_12884, plain, (v1_funct_2('#skF_12', '#skF_10', '#skF_11') | ~v1_partfun1('#skF_12', '#skF_10') | ~v1_funct_1('#skF_12')), inference(resolution, [status(thm)], [c_4383, c_12857])).
% 9.85/3.20  tff(c_12905, plain, (v1_funct_2('#skF_12', '#skF_10', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1014, c_11848, c_12884])).
% 9.85/3.20  tff(c_12907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4382, c_12905])).
% 9.85/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.85/3.20  
% 9.85/3.20  Inference rules
% 9.85/3.20  ----------------------
% 9.85/3.20  #Ref     : 4
% 9.85/3.20  #Sup     : 2613
% 9.85/3.20  #Fact    : 0
% 9.85/3.20  #Define  : 0
% 9.85/3.20  #Split   : 46
% 9.85/3.20  #Chain   : 0
% 9.85/3.20  #Close   : 0
% 9.85/3.20  
% 9.85/3.20  Ordering : KBO
% 9.85/3.20  
% 9.85/3.20  Simplification rules
% 9.85/3.20  ----------------------
% 9.85/3.20  #Subsume      : 507
% 9.85/3.20  #Demod        : 786
% 9.85/3.20  #Tautology    : 476
% 9.85/3.20  #SimpNegUnit  : 230
% 9.85/3.20  #BackRed      : 137
% 9.85/3.20  
% 9.85/3.20  #Partial instantiations: 0
% 9.85/3.20  #Strategies tried      : 1
% 9.85/3.20  
% 9.85/3.20  Timing (in seconds)
% 9.85/3.20  ----------------------
% 9.85/3.20  Preprocessing        : 0.40
% 9.85/3.20  Parsing              : 0.20
% 9.85/3.20  CNF conversion       : 0.03
% 9.85/3.20  Main loop            : 2.02
% 9.85/3.20  Inferencing          : 0.70
% 9.85/3.20  Reduction            : 0.60
% 9.85/3.20  Demodulation         : 0.37
% 9.85/3.20  BG Simplification    : 0.07
% 9.85/3.20  Subsumption          : 0.45
% 9.85/3.20  Abstraction          : 0.08
% 9.85/3.20  MUC search           : 0.00
% 9.85/3.20  Cooper               : 0.00
% 9.85/3.20  Total                : 2.46
% 9.85/3.20  Index Insertion      : 0.00
% 9.85/3.20  Index Deletion       : 0.00
% 9.85/3.20  Index Matching       : 0.00
% 9.85/3.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
