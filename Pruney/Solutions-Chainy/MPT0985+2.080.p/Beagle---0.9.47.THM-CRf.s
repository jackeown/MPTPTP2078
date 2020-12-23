%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:38 EST 2020

% Result     : Theorem 9.19s
% Output     : CNFRefutation 9.46s
% Verified   : 
% Statistics : Number of formulae       :  264 (2341 expanded)
%              Number of leaves         :   39 ( 713 expanded)
%              Depth                    :   17
%              Number of atoms          :  436 (6145 expanded)
%              Number of equality atoms :  176 (2092 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_148,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_121,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_28,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_205,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_222,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_205])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2131,plain,(
    ! [A_283,B_284,C_285] :
      ( k2_relset_1(A_283,B_284,C_285) = k2_relat_1(C_285)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2144,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2131])).

tff(c_2159,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2144])).

tff(c_36,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_862,plain,(
    ! [A_149,B_150,C_151] :
      ( k2_relset_1(A_149,B_150,C_151) = k2_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_872,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_862])).

tff(c_886,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_872])).

tff(c_325,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_344,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_325])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1177,plain,(
    ! [C_181,A_182,B_183] :
      ( m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ r1_tarski(k2_relat_1(C_181),B_183)
      | ~ r1_tarski(k1_relat_1(C_181),A_182)
      | ~ v1_relat_1(C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    ! [A_16] :
      ( v1_funct_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_138,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_141,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_138])).

tff(c_144,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_141])).

tff(c_171,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_178,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_171])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_178])).

tff(c_192,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_225,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_1212,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1177,c_225])).

tff(c_1284,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1212])).

tff(c_1287,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1284])).

tff(c_1291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78,c_1287])).

tff(c_1292,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1212])).

tff(c_1294,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1292])).

tff(c_1297,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1294])).

tff(c_1299,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78,c_72,c_1297])).

tff(c_1302,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1299])).

tff(c_1306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_344,c_1302])).

tff(c_1307,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1292])).

tff(c_1448,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1307])).

tff(c_1454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78,c_72,c_6,c_886,c_1448])).

tff(c_1455,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_1456,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_2003,plain,(
    ! [A_270,B_271,C_272] :
      ( k1_relset_1(A_270,B_271,C_272) = k1_relat_1(C_272)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2024,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1456,c_2003])).

tff(c_2595,plain,(
    ! [B_327,C_328,A_329] :
      ( k1_xboole_0 = B_327
      | v1_funct_2(C_328,A_329,B_327)
      | k1_relset_1(A_329,B_327,C_328) != A_329
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_329,B_327))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2607,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1456,c_2595])).

tff(c_2631,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2024,c_2607])).

tff(c_2632,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1455,c_2631])).

tff(c_2639,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2632])).

tff(c_2642,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2639])).

tff(c_2645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78,c_72,c_2159,c_2642])).

tff(c_2646,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2632])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2687,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2646,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2685,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2646,c_2646,c_14])).

tff(c_123,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_134,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_123])).

tff(c_1517,plain,(
    ! [B_201,A_202] :
      ( B_201 = A_202
      | ~ r1_tarski(B_201,A_202)
      | ~ r1_tarski(A_202,B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1527,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_1517])).

tff(c_1592,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1527])).

tff(c_2884,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_1592])).

tff(c_2889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2687,c_2884])).

tff(c_2890,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1527])).

tff(c_2893,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2890,c_74])).

tff(c_5814,plain,(
    ! [A_591,B_592,C_593] :
      ( k1_relset_1(A_591,B_592,C_593) = k1_relat_1(C_593)
      | ~ m1_subset_1(C_593,k1_zfmisc_1(k2_zfmisc_1(A_591,B_592))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5872,plain,(
    ! [C_599] :
      ( k1_relset_1('#skF_1','#skF_2',C_599) = k1_relat_1(C_599)
      | ~ m1_subset_1(C_599,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2890,c_5814])).

tff(c_5884,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2893,c_5872])).

tff(c_7843,plain,(
    ! [B_727,C_728,A_729] :
      ( k1_xboole_0 = B_727
      | v1_funct_2(C_728,A_729,B_727)
      | k1_relset_1(A_729,B_727,C_728) != A_729
      | ~ m1_subset_1(C_728,k1_zfmisc_1(k2_zfmisc_1(A_729,B_727))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_7858,plain,(
    ! [C_728] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_728,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_728) != '#skF_1'
      | ~ m1_subset_1(C_728,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2890,c_7843])).

tff(c_8157,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7858])).

tff(c_3520,plain,(
    ! [A_416,B_417,C_418] :
      ( k2_relset_1(A_416,B_417,C_418) = k2_relat_1(C_418)
      | ~ m1_subset_1(C_418,k1_zfmisc_1(k2_zfmisc_1(A_416,B_417))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3564,plain,(
    ! [C_422] :
      ( k2_relset_1('#skF_1','#skF_2',C_422) = k2_relat_1(C_422)
      | ~ m1_subset_1(C_422,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2890,c_3520])).

tff(c_3567,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2893,c_3564])).

tff(c_3577,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3567])).

tff(c_3635,plain,(
    ! [A_426,B_427,C_428] :
      ( k1_relset_1(A_426,B_427,C_428) = k1_relat_1(C_428)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_426,B_427))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3656,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1456,c_3635])).

tff(c_4765,plain,(
    ! [B_511,C_512,A_513] :
      ( k1_xboole_0 = B_511
      | v1_funct_2(C_512,A_513,B_511)
      | k1_relset_1(A_513,B_511,C_512) != A_513
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(A_513,B_511))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4780,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1456,c_4765])).

tff(c_4803,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3656,c_4780])).

tff(c_4804,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1455,c_4803])).

tff(c_4809,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4804])).

tff(c_4812,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4809])).

tff(c_4815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78,c_72,c_3577,c_4812])).

tff(c_4816,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4804])).

tff(c_4866,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4816,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4865,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4816,c_4816,c_12])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1489,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1456,c_18])).

tff(c_1526,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1489,c_1517])).

tff(c_3037,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1526])).

tff(c_5101,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4865,c_3037])).

tff(c_5106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4866,c_5101])).

tff(c_5107,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1526])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5141,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5107,c_10])).

tff(c_5254,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5141])).

tff(c_8188,plain,(
    k2_funct_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8157,c_5254])).

tff(c_8204,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8157,c_8157,c_14])).

tff(c_8545,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8204,c_5107])).

tff(c_8547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8188,c_8545])).

tff(c_8549,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7858])).

tff(c_8046,plain,(
    ! [B_741,A_742,C_743] :
      ( k1_xboole_0 = B_741
      | k1_relset_1(A_742,B_741,C_743) = A_742
      | ~ v1_funct_2(C_743,A_742,B_741)
      | ~ m1_subset_1(C_743,k1_zfmisc_1(k2_zfmisc_1(A_742,B_741))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8061,plain,(
    ! [C_743] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_743) = '#skF_1'
      | ~ v1_funct_2(C_743,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_743,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2890,c_8046])).

tff(c_8576,plain,(
    ! [C_759] :
      ( k1_relset_1('#skF_1','#skF_2',C_759) = '#skF_1'
      | ~ v1_funct_2(C_759,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_759,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8549,c_8061])).

tff(c_8579,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2893,c_8576])).

tff(c_8590,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5884,c_8579])).

tff(c_1546,plain,(
    ! [C_204,A_205,B_206] :
      ( v4_relat_1(C_204,A_205)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1569,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_1546])).

tff(c_5688,plain,(
    ! [A_579,B_580,C_581] :
      ( k2_relset_1(A_579,B_580,C_581) = k2_relat_1(C_581)
      | ~ m1_subset_1(C_581,k1_zfmisc_1(k2_zfmisc_1(A_579,B_580))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5732,plain,(
    ! [C_586] :
      ( k2_relset_1('#skF_1','#skF_2',C_586) = k2_relat_1(C_586)
      | ~ m1_subset_1(C_586,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2890,c_5688])).

tff(c_5735,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2893,c_5732])).

tff(c_5745,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5735])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3006,plain,(
    ! [A_347,A_348,B_349] :
      ( v4_relat_1(A_347,A_348)
      | ~ r1_tarski(A_347,k2_zfmisc_1(A_348,B_349)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1546])).

tff(c_3034,plain,(
    ! [A_348,B_349] : v4_relat_1(k2_zfmisc_1(A_348,B_349),A_348) ),
    inference(resolution,[status(thm)],[c_6,c_3006])).

tff(c_2960,plain,(
    ! [B_343,A_344] :
      ( r1_tarski(k1_relat_1(B_343),A_344)
      | ~ v4_relat_1(B_343,A_344)
      | ~ v1_relat_1(B_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1532,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_1517])).

tff(c_5355,plain,(
    ! [B_549] :
      ( k1_relat_1(B_549) = k1_xboole_0
      | ~ v4_relat_1(B_549,k1_xboole_0)
      | ~ v1_relat_1(B_549) ) ),
    inference(resolution,[status(thm)],[c_2960,c_1532])).

tff(c_5359,plain,(
    ! [B_349] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_349)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_349)) ) ),
    inference(resolution,[status(thm)],[c_3034,c_5355])).

tff(c_5370,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14,c_5359])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5828,plain,(
    ! [A_591,B_592] : k1_relset_1(A_591,B_592,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_5814])).

tff(c_5837,plain,(
    ! [A_591,B_592] : k1_relset_1(A_591,B_592,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5370,c_5828])).

tff(c_7866,plain,(
    ! [B_727,A_729] :
      ( k1_xboole_0 = B_727
      | v1_funct_2(k1_xboole_0,A_729,B_727)
      | k1_relset_1(A_729,B_727,k1_xboole_0) != A_729 ) ),
    inference(resolution,[status(thm)],[c_16,c_7843])).

tff(c_7877,plain,(
    ! [B_727,A_729] :
      ( k1_xboole_0 = B_727
      | v1_funct_2(k1_xboole_0,A_729,B_727)
      | k1_xboole_0 != A_729 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5837,c_7866])).

tff(c_8587,plain,
    ( k1_relset_1('#skF_1','#skF_2',k1_xboole_0) = '#skF_1'
    | ~ v1_funct_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_8576])).

tff(c_8593,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v1_funct_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5837,c_8587])).

tff(c_8772,plain,(
    ~ v1_funct_2(k1_xboole_0,'#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_8593])).

tff(c_8775,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_1' ),
    inference(resolution,[status(thm)],[c_7877,c_8772])).

tff(c_8778,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_8549,c_8775])).

tff(c_6310,plain,(
    ! [A_639,B_640,A_641] :
      ( k1_relset_1(A_639,B_640,A_641) = k1_relat_1(A_641)
      | ~ r1_tarski(A_641,k2_zfmisc_1(A_639,B_640)) ) ),
    inference(resolution,[status(thm)],[c_20,c_5814])).

tff(c_6345,plain,(
    ! [A_639,B_640] : k1_relset_1(A_639,B_640,k2_zfmisc_1(A_639,B_640)) = k1_relat_1(k2_zfmisc_1(A_639,B_640)) ),
    inference(resolution,[status(thm)],[c_6,c_6310])).

tff(c_10300,plain,(
    ! [B_832,A_833,A_834] :
      ( k1_xboole_0 = B_832
      | v1_funct_2(A_833,A_834,B_832)
      | k1_relset_1(A_834,B_832,A_833) != A_834
      | ~ r1_tarski(A_833,k2_zfmisc_1(A_834,B_832)) ) ),
    inference(resolution,[status(thm)],[c_20,c_7843])).

tff(c_10332,plain,(
    ! [B_832,A_834] :
      ( k1_xboole_0 = B_832
      | v1_funct_2(k2_zfmisc_1(A_834,B_832),A_834,B_832)
      | k1_relset_1(A_834,B_832,k2_zfmisc_1(A_834,B_832)) != A_834 ) ),
    inference(resolution,[status(thm)],[c_6,c_10300])).

tff(c_11931,plain,(
    ! [B_890,A_891] :
      ( k1_xboole_0 = B_890
      | v1_funct_2(k2_zfmisc_1(A_891,B_890),A_891,B_890)
      | k1_relat_1(k2_zfmisc_1(A_891,B_890)) != A_891 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6345,c_10332])).

tff(c_11947,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_5107,c_11931])).

tff(c_11969,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5107,c_11947])).

tff(c_11970,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1455,c_8778,c_11969])).

tff(c_11979,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_11970])).

tff(c_11982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78,c_72,c_5745,c_11979])).

tff(c_11983,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8593])).

tff(c_1457,plain,(
    ! [C_196] :
      ( v1_relat_1(C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_205])).

tff(c_1466,plain,(
    ! [A_7] :
      ( v1_relat_1(A_7)
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_1457])).

tff(c_2987,plain,(
    ! [B_343] :
      ( v1_relat_1(k1_relat_1(B_343))
      | ~ v4_relat_1(B_343,k1_xboole_0)
      | ~ v1_relat_1(B_343) ) ),
    inference(resolution,[status(thm)],[c_2960,c_1466])).

tff(c_8657,plain,
    ( v1_relat_1('#skF_1')
    | ~ v4_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8590,c_2987])).

tff(c_8702,plain,
    ( v1_relat_1('#skF_1')
    | ~ v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_8657])).

tff(c_8719,plain,(
    ~ v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8702])).

tff(c_11986,plain,(
    ~ v4_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11983,c_8719])).

tff(c_12039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1569,c_11986])).

tff(c_12041,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8702])).

tff(c_2984,plain,(
    ! [B_343] :
      ( k1_relat_1(B_343) = k1_xboole_0
      | ~ v4_relat_1(B_343,k1_xboole_0)
      | ~ v1_relat_1(B_343) ) ),
    inference(resolution,[status(thm)],[c_2960,c_1532])).

tff(c_12086,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12041,c_2984])).

tff(c_12089,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_8590,c_12086])).

tff(c_12122,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12089,c_5254])).

tff(c_12139,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12089,c_12089,c_12])).

tff(c_12461,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12139,c_5107])).

tff(c_12463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12122,c_12461])).

tff(c_12464,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5141])).

tff(c_12493,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12464])).

tff(c_2905,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2890,c_10])).

tff(c_2931,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2905])).

tff(c_12504,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12493,c_2931])).

tff(c_12513,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12493,c_12493,c_14])).

tff(c_12612,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12513,c_2890])).

tff(c_12614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12504,c_12612])).

tff(c_12615,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12464])).

tff(c_12655,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12615,c_2931])).

tff(c_12711,plain,(
    ! [A_912] : k2_zfmisc_1(A_912,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12615,c_12615,c_12])).

tff(c_12724,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_12711,c_2890])).

tff(c_12741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12655,c_12724])).

tff(c_12743,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2905])).

tff(c_12754,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12743,c_12743,c_14])).

tff(c_13077,plain,(
    ! [A_950,A_951,B_952] :
      ( v4_relat_1(A_950,A_951)
      | ~ r1_tarski(A_950,k2_zfmisc_1(A_951,B_952)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1546])).

tff(c_13099,plain,(
    ! [A_951,B_952] : v4_relat_1(k2_zfmisc_1(A_951,B_952),A_951) ),
    inference(resolution,[status(thm)],[c_6,c_13077])).

tff(c_12937,plain,(
    ! [A_925] :
      ( A_925 = '#skF_3'
      | ~ r1_tarski(A_925,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12743,c_12743,c_1532])).

tff(c_13124,plain,(
    ! [B_958] :
      ( k1_relat_1(B_958) = '#skF_3'
      | ~ v4_relat_1(B_958,'#skF_3')
      | ~ v1_relat_1(B_958) ) ),
    inference(resolution,[status(thm)],[c_26,c_12937])).

tff(c_13128,plain,(
    ! [B_952] :
      ( k1_relat_1(k2_zfmisc_1('#skF_3',B_952)) = '#skF_3'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3',B_952)) ) ),
    inference(resolution,[status(thm)],[c_13099,c_13124])).

tff(c_13139,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12754,c_13128])).

tff(c_12753,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12743,c_16])).

tff(c_13586,plain,(
    ! [A_1009,B_1010,C_1011] :
      ( k1_relset_1(A_1009,B_1010,C_1011) = k1_relat_1(C_1011)
      | ~ m1_subset_1(C_1011,k1_zfmisc_1(k2_zfmisc_1(A_1009,B_1010))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_13596,plain,(
    ! [A_1009,B_1010] : k1_relset_1(A_1009,B_1010,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12753,c_13586])).

tff(c_13606,plain,(
    ! [A_1009,B_1010] : k1_relset_1(A_1009,B_1010,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13139,c_13596])).

tff(c_54,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_82,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_54])).

tff(c_13785,plain,(
    ! [C_1031,B_1032] :
      ( v1_funct_2(C_1031,'#skF_3',B_1032)
      | k1_relset_1('#skF_3',B_1032,C_1031) != '#skF_3'
      | ~ m1_subset_1(C_1031,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12743,c_12743,c_12743,c_12743,c_82])).

tff(c_13788,plain,(
    ! [B_1032] :
      ( v1_funct_2('#skF_3','#skF_3',B_1032)
      | k1_relset_1('#skF_3',B_1032,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_12753,c_13785])).

tff(c_13794,plain,(
    ! [B_1032] : v1_funct_2('#skF_3','#skF_3',B_1032) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13606,c_13788])).

tff(c_12756,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12743,c_8])).

tff(c_12742,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2905])).

tff(c_12846,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12743,c_12743,c_12742])).

tff(c_12847,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12846])).

tff(c_12850,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12847,c_1489])).

tff(c_12855,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12754,c_12850])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12909,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12855,c_2])).

tff(c_12914,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12756,c_12909])).

tff(c_12852,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12847,c_1455])).

tff(c_12955,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12914,c_12852])).

tff(c_13799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13794,c_12955])).

tff(c_13800,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12846])).

tff(c_13801,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12846])).

tff(c_13825,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13800,c_13801])).

tff(c_50,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_33,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_80,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_12751,plain,(
    ! [A_33] :
      ( v1_funct_2('#skF_3',A_33,'#skF_3')
      | A_33 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12743,c_12743,c_12743,c_80])).

tff(c_14045,plain,(
    ! [A_1049] :
      ( v1_funct_2('#skF_1',A_1049,'#skF_1')
      | A_1049 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13800,c_13800,c_13800,c_12751])).

tff(c_13805,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13800,c_12756])).

tff(c_12755,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12743,c_12743,c_12])).

tff(c_13864,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13800,c_13800,c_12755])).

tff(c_13813,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13800,c_1456])).

tff(c_13967,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13864,c_13813])).

tff(c_13974,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_13967,c_18])).

tff(c_13979,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_13974,c_2])).

tff(c_13984,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13805,c_13979])).

tff(c_13814,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13800,c_1455])).

tff(c_13987,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13984,c_13814])).

tff(c_14048,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14045,c_13987])).

tff(c_14052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13825,c_14048])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n024.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:31:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.19/3.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.19/3.30  
% 9.19/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.19/3.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.19/3.31  
% 9.19/3.31  %Foreground sorts:
% 9.19/3.31  
% 9.19/3.31  
% 9.19/3.31  %Background operators:
% 9.19/3.31  
% 9.19/3.31  
% 9.19/3.31  %Foreground operators:
% 9.19/3.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.19/3.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.19/3.31  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.19/3.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.19/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.19/3.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.19/3.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.19/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.19/3.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.19/3.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.19/3.31  tff('#skF_2', type, '#skF_2': $i).
% 9.19/3.31  tff('#skF_3', type, '#skF_3': $i).
% 9.19/3.31  tff('#skF_1', type, '#skF_1': $i).
% 9.19/3.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.19/3.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.19/3.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.19/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.19/3.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.19/3.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.19/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.19/3.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.19/3.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.19/3.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.19/3.31  
% 9.46/3.34  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.46/3.34  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 9.46/3.34  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.46/3.34  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.46/3.34  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.46/3.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.46/3.34  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.46/3.34  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.46/3.34  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.46/3.34  tff(f_103, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 9.46/3.34  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.46/3.34  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.46/3.34  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.46/3.34  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.46/3.34  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.46/3.34  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.46/3.34  tff(c_28, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.46/3.34  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.46/3.34  tff(c_205, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.46/3.34  tff(c_222, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_205])).
% 9.46/3.34  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.46/3.34  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.46/3.34  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.46/3.34  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.46/3.34  tff(c_2131, plain, (![A_283, B_284, C_285]: (k2_relset_1(A_283, B_284, C_285)=k2_relat_1(C_285) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.46/3.34  tff(c_2144, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2131])).
% 9.46/3.34  tff(c_2159, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2144])).
% 9.46/3.34  tff(c_36, plain, (![A_17]: (k1_relat_1(k2_funct_1(A_17))=k2_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.46/3.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.46/3.34  tff(c_862, plain, (![A_149, B_150, C_151]: (k2_relset_1(A_149, B_150, C_151)=k2_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.46/3.34  tff(c_872, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_862])).
% 9.46/3.34  tff(c_886, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_872])).
% 9.46/3.34  tff(c_325, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.46/3.34  tff(c_344, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_325])).
% 9.46/3.34  tff(c_26, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.46/3.34  tff(c_34, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.46/3.34  tff(c_32, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.46/3.34  tff(c_1177, plain, (![C_181, A_182, B_183]: (m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~r1_tarski(k2_relat_1(C_181), B_183) | ~r1_tarski(k1_relat_1(C_181), A_182) | ~v1_relat_1(C_181))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.46/3.34  tff(c_30, plain, (![A_16]: (v1_funct_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.46/3.34  tff(c_68, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.46/3.34  tff(c_138, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_68])).
% 9.46/3.34  tff(c_141, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_138])).
% 9.46/3.34  tff(c_144, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_141])).
% 9.46/3.34  tff(c_171, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.46/3.34  tff(c_178, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_171])).
% 9.46/3.34  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_178])).
% 9.46/3.34  tff(c_192, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_68])).
% 9.46/3.34  tff(c_225, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_192])).
% 9.46/3.34  tff(c_1212, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1177, c_225])).
% 9.46/3.34  tff(c_1284, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1212])).
% 9.46/3.34  tff(c_1287, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1284])).
% 9.46/3.34  tff(c_1291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_222, c_78, c_1287])).
% 9.46/3.34  tff(c_1292, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(splitRight, [status(thm)], [c_1212])).
% 9.46/3.34  tff(c_1294, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(splitLeft, [status(thm)], [c_1292])).
% 9.46/3.34  tff(c_1297, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1294])).
% 9.46/3.34  tff(c_1299, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_78, c_72, c_1297])).
% 9.46/3.34  tff(c_1302, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1299])).
% 9.46/3.34  tff(c_1306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_222, c_344, c_1302])).
% 9.46/3.34  tff(c_1307, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_1292])).
% 9.46/3.34  tff(c_1448, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1307])).
% 9.46/3.34  tff(c_1454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_222, c_78, c_72, c_6, c_886, c_1448])).
% 9.46/3.34  tff(c_1455, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_192])).
% 9.46/3.34  tff(c_1456, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_192])).
% 9.46/3.34  tff(c_2003, plain, (![A_270, B_271, C_272]: (k1_relset_1(A_270, B_271, C_272)=k1_relat_1(C_272) | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.46/3.34  tff(c_2024, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1456, c_2003])).
% 9.46/3.34  tff(c_2595, plain, (![B_327, C_328, A_329]: (k1_xboole_0=B_327 | v1_funct_2(C_328, A_329, B_327) | k1_relset_1(A_329, B_327, C_328)!=A_329 | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_329, B_327))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.46/3.34  tff(c_2607, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1456, c_2595])).
% 9.46/3.34  tff(c_2631, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2024, c_2607])).
% 9.46/3.34  tff(c_2632, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1455, c_2631])).
% 9.46/3.34  tff(c_2639, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_2632])).
% 9.46/3.34  tff(c_2642, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_2639])).
% 9.46/3.34  tff(c_2645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_222, c_78, c_72, c_2159, c_2642])).
% 9.46/3.34  tff(c_2646, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2632])).
% 9.46/3.34  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.46/3.34  tff(c_2687, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2646, c_8])).
% 9.46/3.34  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.46/3.34  tff(c_2685, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2646, c_2646, c_14])).
% 9.46/3.34  tff(c_123, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.46/3.34  tff(c_134, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_123])).
% 9.46/3.34  tff(c_1517, plain, (![B_201, A_202]: (B_201=A_202 | ~r1_tarski(B_201, A_202) | ~r1_tarski(A_202, B_201))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.46/3.34  tff(c_1527, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_134, c_1517])).
% 9.46/3.34  tff(c_1592, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1527])).
% 9.46/3.34  tff(c_2884, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_1592])).
% 9.46/3.34  tff(c_2889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2687, c_2884])).
% 9.46/3.34  tff(c_2890, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1527])).
% 9.46/3.34  tff(c_2893, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2890, c_74])).
% 9.46/3.34  tff(c_5814, plain, (![A_591, B_592, C_593]: (k1_relset_1(A_591, B_592, C_593)=k1_relat_1(C_593) | ~m1_subset_1(C_593, k1_zfmisc_1(k2_zfmisc_1(A_591, B_592))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.46/3.34  tff(c_5872, plain, (![C_599]: (k1_relset_1('#skF_1', '#skF_2', C_599)=k1_relat_1(C_599) | ~m1_subset_1(C_599, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2890, c_5814])).
% 9.46/3.34  tff(c_5884, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2893, c_5872])).
% 9.46/3.34  tff(c_7843, plain, (![B_727, C_728, A_729]: (k1_xboole_0=B_727 | v1_funct_2(C_728, A_729, B_727) | k1_relset_1(A_729, B_727, C_728)!=A_729 | ~m1_subset_1(C_728, k1_zfmisc_1(k2_zfmisc_1(A_729, B_727))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.46/3.34  tff(c_7858, plain, (![C_728]: (k1_xboole_0='#skF_2' | v1_funct_2(C_728, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_728)!='#skF_1' | ~m1_subset_1(C_728, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2890, c_7843])).
% 9.46/3.34  tff(c_8157, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_7858])).
% 9.46/3.34  tff(c_3520, plain, (![A_416, B_417, C_418]: (k2_relset_1(A_416, B_417, C_418)=k2_relat_1(C_418) | ~m1_subset_1(C_418, k1_zfmisc_1(k2_zfmisc_1(A_416, B_417))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.46/3.34  tff(c_3564, plain, (![C_422]: (k2_relset_1('#skF_1', '#skF_2', C_422)=k2_relat_1(C_422) | ~m1_subset_1(C_422, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2890, c_3520])).
% 9.46/3.34  tff(c_3567, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2893, c_3564])).
% 9.46/3.34  tff(c_3577, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3567])).
% 9.46/3.34  tff(c_3635, plain, (![A_426, B_427, C_428]: (k1_relset_1(A_426, B_427, C_428)=k1_relat_1(C_428) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_426, B_427))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.46/3.34  tff(c_3656, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1456, c_3635])).
% 9.46/3.34  tff(c_4765, plain, (![B_511, C_512, A_513]: (k1_xboole_0=B_511 | v1_funct_2(C_512, A_513, B_511) | k1_relset_1(A_513, B_511, C_512)!=A_513 | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(A_513, B_511))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.46/3.34  tff(c_4780, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1456, c_4765])).
% 9.46/3.34  tff(c_4803, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3656, c_4780])).
% 9.46/3.34  tff(c_4804, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1455, c_4803])).
% 9.46/3.34  tff(c_4809, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_4804])).
% 9.46/3.34  tff(c_4812, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_4809])).
% 9.46/3.34  tff(c_4815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_222, c_78, c_72, c_3577, c_4812])).
% 9.46/3.34  tff(c_4816, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4804])).
% 9.46/3.34  tff(c_4866, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4816, c_8])).
% 9.46/3.34  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.46/3.34  tff(c_4865, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4816, c_4816, c_12])).
% 9.46/3.34  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.46/3.34  tff(c_1489, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_1456, c_18])).
% 9.46/3.34  tff(c_1526, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1489, c_1517])).
% 9.46/3.34  tff(c_3037, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1526])).
% 9.46/3.34  tff(c_5101, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4865, c_3037])).
% 9.46/3.34  tff(c_5106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4866, c_5101])).
% 9.46/3.34  tff(c_5107, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_1526])).
% 9.46/3.34  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.46/3.34  tff(c_5141, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5107, c_10])).
% 9.46/3.34  tff(c_5254, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5141])).
% 9.46/3.34  tff(c_8188, plain, (k2_funct_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8157, c_5254])).
% 9.46/3.34  tff(c_8204, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8157, c_8157, c_14])).
% 9.46/3.34  tff(c_8545, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8204, c_5107])).
% 9.46/3.34  tff(c_8547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8188, c_8545])).
% 9.46/3.34  tff(c_8549, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_7858])).
% 9.46/3.34  tff(c_8046, plain, (![B_741, A_742, C_743]: (k1_xboole_0=B_741 | k1_relset_1(A_742, B_741, C_743)=A_742 | ~v1_funct_2(C_743, A_742, B_741) | ~m1_subset_1(C_743, k1_zfmisc_1(k2_zfmisc_1(A_742, B_741))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.46/3.34  tff(c_8061, plain, (![C_743]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_743)='#skF_1' | ~v1_funct_2(C_743, '#skF_1', '#skF_2') | ~m1_subset_1(C_743, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2890, c_8046])).
% 9.46/3.34  tff(c_8576, plain, (![C_759]: (k1_relset_1('#skF_1', '#skF_2', C_759)='#skF_1' | ~v1_funct_2(C_759, '#skF_1', '#skF_2') | ~m1_subset_1(C_759, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_8549, c_8061])).
% 9.46/3.34  tff(c_8579, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2893, c_8576])).
% 9.46/3.34  tff(c_8590, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5884, c_8579])).
% 9.46/3.34  tff(c_1546, plain, (![C_204, A_205, B_206]: (v4_relat_1(C_204, A_205) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.46/3.34  tff(c_1569, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_1546])).
% 9.46/3.34  tff(c_5688, plain, (![A_579, B_580, C_581]: (k2_relset_1(A_579, B_580, C_581)=k2_relat_1(C_581) | ~m1_subset_1(C_581, k1_zfmisc_1(k2_zfmisc_1(A_579, B_580))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.46/3.34  tff(c_5732, plain, (![C_586]: (k2_relset_1('#skF_1', '#skF_2', C_586)=k2_relat_1(C_586) | ~m1_subset_1(C_586, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2890, c_5688])).
% 9.46/3.34  tff(c_5735, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2893, c_5732])).
% 9.46/3.34  tff(c_5745, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5735])).
% 9.46/3.34  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.46/3.34  tff(c_3006, plain, (![A_347, A_348, B_349]: (v4_relat_1(A_347, A_348) | ~r1_tarski(A_347, k2_zfmisc_1(A_348, B_349)))), inference(resolution, [status(thm)], [c_20, c_1546])).
% 9.46/3.34  tff(c_3034, plain, (![A_348, B_349]: (v4_relat_1(k2_zfmisc_1(A_348, B_349), A_348))), inference(resolution, [status(thm)], [c_6, c_3006])).
% 9.46/3.34  tff(c_2960, plain, (![B_343, A_344]: (r1_tarski(k1_relat_1(B_343), A_344) | ~v4_relat_1(B_343, A_344) | ~v1_relat_1(B_343))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.46/3.34  tff(c_1532, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1517])).
% 9.46/3.34  tff(c_5355, plain, (![B_549]: (k1_relat_1(B_549)=k1_xboole_0 | ~v4_relat_1(B_549, k1_xboole_0) | ~v1_relat_1(B_549))), inference(resolution, [status(thm)], [c_2960, c_1532])).
% 9.46/3.34  tff(c_5359, plain, (![B_349]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_349))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_349)))), inference(resolution, [status(thm)], [c_3034, c_5355])).
% 9.46/3.34  tff(c_5370, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14, c_5359])).
% 9.46/3.34  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.46/3.34  tff(c_5828, plain, (![A_591, B_592]: (k1_relset_1(A_591, B_592, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_5814])).
% 9.46/3.34  tff(c_5837, plain, (![A_591, B_592]: (k1_relset_1(A_591, B_592, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5370, c_5828])).
% 9.46/3.34  tff(c_7866, plain, (![B_727, A_729]: (k1_xboole_0=B_727 | v1_funct_2(k1_xboole_0, A_729, B_727) | k1_relset_1(A_729, B_727, k1_xboole_0)!=A_729)), inference(resolution, [status(thm)], [c_16, c_7843])).
% 9.46/3.34  tff(c_7877, plain, (![B_727, A_729]: (k1_xboole_0=B_727 | v1_funct_2(k1_xboole_0, A_729, B_727) | k1_xboole_0!=A_729)), inference(demodulation, [status(thm), theory('equality')], [c_5837, c_7866])).
% 9.46/3.34  tff(c_8587, plain, (k1_relset_1('#skF_1', '#skF_2', k1_xboole_0)='#skF_1' | ~v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_8576])).
% 9.46/3.34  tff(c_8593, plain, (k1_xboole_0='#skF_1' | ~v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5837, c_8587])).
% 9.46/3.34  tff(c_8772, plain, (~v1_funct_2(k1_xboole_0, '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_8593])).
% 9.46/3.34  tff(c_8775, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_1'), inference(resolution, [status(thm)], [c_7877, c_8772])).
% 9.46/3.34  tff(c_8778, plain, (k1_xboole_0!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_8549, c_8775])).
% 9.46/3.34  tff(c_6310, plain, (![A_639, B_640, A_641]: (k1_relset_1(A_639, B_640, A_641)=k1_relat_1(A_641) | ~r1_tarski(A_641, k2_zfmisc_1(A_639, B_640)))), inference(resolution, [status(thm)], [c_20, c_5814])).
% 9.46/3.34  tff(c_6345, plain, (![A_639, B_640]: (k1_relset_1(A_639, B_640, k2_zfmisc_1(A_639, B_640))=k1_relat_1(k2_zfmisc_1(A_639, B_640)))), inference(resolution, [status(thm)], [c_6, c_6310])).
% 9.46/3.34  tff(c_10300, plain, (![B_832, A_833, A_834]: (k1_xboole_0=B_832 | v1_funct_2(A_833, A_834, B_832) | k1_relset_1(A_834, B_832, A_833)!=A_834 | ~r1_tarski(A_833, k2_zfmisc_1(A_834, B_832)))), inference(resolution, [status(thm)], [c_20, c_7843])).
% 9.46/3.34  tff(c_10332, plain, (![B_832, A_834]: (k1_xboole_0=B_832 | v1_funct_2(k2_zfmisc_1(A_834, B_832), A_834, B_832) | k1_relset_1(A_834, B_832, k2_zfmisc_1(A_834, B_832))!=A_834)), inference(resolution, [status(thm)], [c_6, c_10300])).
% 9.46/3.34  tff(c_11931, plain, (![B_890, A_891]: (k1_xboole_0=B_890 | v1_funct_2(k2_zfmisc_1(A_891, B_890), A_891, B_890) | k1_relat_1(k2_zfmisc_1(A_891, B_890))!=A_891)), inference(demodulation, [status(thm), theory('equality')], [c_6345, c_10332])).
% 9.46/3.34  tff(c_11947, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_5107, c_11931])).
% 9.46/3.34  tff(c_11969, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5107, c_11947])).
% 9.46/3.34  tff(c_11970, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1455, c_8778, c_11969])).
% 9.46/3.34  tff(c_11979, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_11970])).
% 9.46/3.34  tff(c_11982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_222, c_78, c_72, c_5745, c_11979])).
% 9.46/3.34  tff(c_11983, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_8593])).
% 9.46/3.34  tff(c_1457, plain, (![C_196]: (v1_relat_1(C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_205])).
% 9.46/3.34  tff(c_1466, plain, (![A_7]: (v1_relat_1(A_7) | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_1457])).
% 9.46/3.34  tff(c_2987, plain, (![B_343]: (v1_relat_1(k1_relat_1(B_343)) | ~v4_relat_1(B_343, k1_xboole_0) | ~v1_relat_1(B_343))), inference(resolution, [status(thm)], [c_2960, c_1466])).
% 9.46/3.34  tff(c_8657, plain, (v1_relat_1('#skF_1') | ~v4_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8590, c_2987])).
% 9.46/3.34  tff(c_8702, plain, (v1_relat_1('#skF_1') | ~v4_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_222, c_8657])).
% 9.46/3.34  tff(c_8719, plain, (~v4_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8702])).
% 9.46/3.34  tff(c_11986, plain, (~v4_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11983, c_8719])).
% 9.46/3.34  tff(c_12039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1569, c_11986])).
% 9.46/3.34  tff(c_12041, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8702])).
% 9.46/3.34  tff(c_2984, plain, (![B_343]: (k1_relat_1(B_343)=k1_xboole_0 | ~v4_relat_1(B_343, k1_xboole_0) | ~v1_relat_1(B_343))), inference(resolution, [status(thm)], [c_2960, c_1532])).
% 9.46/3.34  tff(c_12086, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12041, c_2984])).
% 9.46/3.34  tff(c_12089, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_222, c_8590, c_12086])).
% 9.46/3.34  tff(c_12122, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12089, c_5254])).
% 9.46/3.34  tff(c_12139, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12089, c_12089, c_12])).
% 9.46/3.34  tff(c_12461, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12139, c_5107])).
% 9.46/3.34  tff(c_12463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12122, c_12461])).
% 9.46/3.34  tff(c_12464, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5141])).
% 9.46/3.34  tff(c_12493, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_12464])).
% 9.46/3.34  tff(c_2905, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2890, c_10])).
% 9.46/3.34  tff(c_2931, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_2905])).
% 9.46/3.34  tff(c_12504, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12493, c_2931])).
% 9.46/3.34  tff(c_12513, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12493, c_12493, c_14])).
% 9.46/3.34  tff(c_12612, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12513, c_2890])).
% 9.46/3.34  tff(c_12614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12504, c_12612])).
% 9.46/3.34  tff(c_12615, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_12464])).
% 9.46/3.34  tff(c_12655, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12615, c_2931])).
% 9.46/3.34  tff(c_12711, plain, (![A_912]: (k2_zfmisc_1(A_912, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12615, c_12615, c_12])).
% 9.46/3.34  tff(c_12724, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_12711, c_2890])).
% 9.46/3.34  tff(c_12741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12655, c_12724])).
% 9.46/3.34  tff(c_12743, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2905])).
% 9.46/3.34  tff(c_12754, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12743, c_12743, c_14])).
% 9.46/3.34  tff(c_13077, plain, (![A_950, A_951, B_952]: (v4_relat_1(A_950, A_951) | ~r1_tarski(A_950, k2_zfmisc_1(A_951, B_952)))), inference(resolution, [status(thm)], [c_20, c_1546])).
% 9.46/3.34  tff(c_13099, plain, (![A_951, B_952]: (v4_relat_1(k2_zfmisc_1(A_951, B_952), A_951))), inference(resolution, [status(thm)], [c_6, c_13077])).
% 9.46/3.34  tff(c_12937, plain, (![A_925]: (A_925='#skF_3' | ~r1_tarski(A_925, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12743, c_12743, c_1532])).
% 9.46/3.34  tff(c_13124, plain, (![B_958]: (k1_relat_1(B_958)='#skF_3' | ~v4_relat_1(B_958, '#skF_3') | ~v1_relat_1(B_958))), inference(resolution, [status(thm)], [c_26, c_12937])).
% 9.46/3.34  tff(c_13128, plain, (![B_952]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_952))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_3', B_952)))), inference(resolution, [status(thm)], [c_13099, c_13124])).
% 9.46/3.34  tff(c_13139, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12754, c_13128])).
% 9.46/3.34  tff(c_12753, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_12743, c_16])).
% 9.46/3.34  tff(c_13586, plain, (![A_1009, B_1010, C_1011]: (k1_relset_1(A_1009, B_1010, C_1011)=k1_relat_1(C_1011) | ~m1_subset_1(C_1011, k1_zfmisc_1(k2_zfmisc_1(A_1009, B_1010))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.46/3.34  tff(c_13596, plain, (![A_1009, B_1010]: (k1_relset_1(A_1009, B_1010, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_12753, c_13586])).
% 9.46/3.34  tff(c_13606, plain, (![A_1009, B_1010]: (k1_relset_1(A_1009, B_1010, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13139, c_13596])).
% 9.46/3.34  tff(c_54, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.46/3.34  tff(c_82, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_54])).
% 9.46/3.34  tff(c_13785, plain, (![C_1031, B_1032]: (v1_funct_2(C_1031, '#skF_3', B_1032) | k1_relset_1('#skF_3', B_1032, C_1031)!='#skF_3' | ~m1_subset_1(C_1031, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12743, c_12743, c_12743, c_12743, c_82])).
% 9.46/3.34  tff(c_13788, plain, (![B_1032]: (v1_funct_2('#skF_3', '#skF_3', B_1032) | k1_relset_1('#skF_3', B_1032, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_12753, c_13785])).
% 9.46/3.34  tff(c_13794, plain, (![B_1032]: (v1_funct_2('#skF_3', '#skF_3', B_1032))), inference(demodulation, [status(thm), theory('equality')], [c_13606, c_13788])).
% 9.46/3.34  tff(c_12756, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_12743, c_8])).
% 9.46/3.34  tff(c_12742, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2905])).
% 9.46/3.34  tff(c_12846, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12743, c_12743, c_12742])).
% 9.46/3.34  tff(c_12847, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_12846])).
% 9.46/3.34  tff(c_12850, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12847, c_1489])).
% 9.46/3.34  tff(c_12855, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12754, c_12850])).
% 9.46/3.34  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.46/3.34  tff(c_12909, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_12855, c_2])).
% 9.46/3.34  tff(c_12914, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12756, c_12909])).
% 9.46/3.34  tff(c_12852, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12847, c_1455])).
% 9.46/3.34  tff(c_12955, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12914, c_12852])).
% 9.46/3.34  tff(c_13799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13794, c_12955])).
% 9.46/3.34  tff(c_13800, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_12846])).
% 9.46/3.34  tff(c_13801, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_12846])).
% 9.46/3.34  tff(c_13825, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13800, c_13801])).
% 9.46/3.34  tff(c_50, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_33, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.46/3.34  tff(c_80, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_50])).
% 9.46/3.34  tff(c_12751, plain, (![A_33]: (v1_funct_2('#skF_3', A_33, '#skF_3') | A_33='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12743, c_12743, c_12743, c_80])).
% 9.46/3.34  tff(c_14045, plain, (![A_1049]: (v1_funct_2('#skF_1', A_1049, '#skF_1') | A_1049='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13800, c_13800, c_13800, c_12751])).
% 9.46/3.34  tff(c_13805, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_13800, c_12756])).
% 9.46/3.34  tff(c_12755, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12743, c_12743, c_12])).
% 9.46/3.34  tff(c_13864, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13800, c_13800, c_12755])).
% 9.46/3.34  tff(c_13813, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_13800, c_1456])).
% 9.46/3.34  tff(c_13967, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13864, c_13813])).
% 9.46/3.34  tff(c_13974, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_13967, c_18])).
% 9.46/3.34  tff(c_13979, plain, (k2_funct_1('#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_13974, c_2])).
% 9.46/3.34  tff(c_13984, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13805, c_13979])).
% 9.46/3.34  tff(c_13814, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13800, c_1455])).
% 9.46/3.34  tff(c_13987, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13984, c_13814])).
% 9.46/3.34  tff(c_14048, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_14045, c_13987])).
% 9.46/3.34  tff(c_14052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13825, c_14048])).
% 9.46/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.46/3.34  
% 9.46/3.34  Inference rules
% 9.46/3.34  ----------------------
% 9.46/3.34  #Ref     : 0
% 9.46/3.34  #Sup     : 2890
% 9.46/3.34  #Fact    : 0
% 9.46/3.34  #Define  : 0
% 9.46/3.34  #Split   : 41
% 9.46/3.34  #Chain   : 0
% 9.46/3.34  #Close   : 0
% 9.46/3.34  
% 9.46/3.34  Ordering : KBO
% 9.46/3.34  
% 9.46/3.34  Simplification rules
% 9.46/3.34  ----------------------
% 9.46/3.34  #Subsume      : 408
% 9.46/3.34  #Demod        : 3773
% 9.46/3.34  #Tautology    : 1363
% 9.46/3.34  #SimpNegUnit  : 40
% 9.46/3.34  #BackRed      : 510
% 9.46/3.34  
% 9.46/3.34  #Partial instantiations: 0
% 9.46/3.34  #Strategies tried      : 1
% 9.46/3.34  
% 9.46/3.34  Timing (in seconds)
% 9.46/3.34  ----------------------
% 9.46/3.34  Preprocessing        : 0.35
% 9.46/3.34  Parsing              : 0.19
% 9.46/3.34  CNF conversion       : 0.02
% 9.46/3.35  Main loop            : 2.20
% 9.46/3.35  Inferencing          : 0.68
% 9.46/3.35  Reduction            : 0.85
% 9.46/3.35  Demodulation         : 0.63
% 9.46/3.35  BG Simplification    : 0.07
% 9.46/3.35  Subsumption          : 0.43
% 9.46/3.35  Abstraction          : 0.08
% 9.46/3.35  MUC search           : 0.00
% 9.46/3.35  Cooper               : 0.00
% 9.46/3.35  Total                : 2.64
% 9.46/3.35  Index Insertion      : 0.00
% 9.46/3.35  Index Deletion       : 0.00
% 9.46/3.35  Index Matching       : 0.00
% 9.46/3.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
