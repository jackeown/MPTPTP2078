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
% DateTime   : Thu Dec  3 10:12:27 EST 2020

% Result     : Theorem 48.33s
% Output     : CNFRefutation 48.59s
% Verified   : 
% Statistics : Number of formulae       :  254 (1503 expanded)
%              Number of leaves         :   51 ( 518 expanded)
%              Depth                    :   16
%              Number of atoms          :  479 (4032 expanded)
%              Number of equality atoms :  179 (1271 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_210,negated_conjecture,(
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

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_153,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_149,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_171,axiom,(
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

tff(f_181,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_145,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(c_94,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_179246,plain,(
    ! [C_1455,A_1456,B_1457] :
      ( v1_relat_1(C_1455)
      | ~ m1_subset_1(C_1455,k1_zfmisc_1(k2_zfmisc_1(A_1456,B_1457))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_179258,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_179246])).

tff(c_24,plain,(
    ! [A_14] :
      ( k2_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_179267,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_179258,c_24])).

tff(c_179277,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_179267])).

tff(c_98,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_92,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_90,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_179898,plain,(
    ! [A_1529,B_1530,C_1531] :
      ( k2_relset_1(A_1529,B_1530,C_1531) = k2_relat_1(C_1531)
      | ~ m1_subset_1(C_1531,k1_zfmisc_1(k2_zfmisc_1(A_1529,B_1530))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_179907,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_179898])).

tff(c_179915,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_179907])).

tff(c_50,plain,(
    ! [A_25] :
      ( k1_relat_1(k2_funct_1(A_25)) = k2_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_245,plain,(
    ! [A_69] :
      ( v1_funct_1(k2_funct_1(A_69))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_88,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_244,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_248,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_245,c_244])).

tff(c_251,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_248])).

tff(c_433,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_436,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_433])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_436])).

tff(c_445,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_574,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_445])).

tff(c_822,plain,(
    ! [C_112,A_113,B_114] :
      ( v1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_830,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_822])).

tff(c_36,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1651,plain,(
    ! [B_198,A_199] :
      ( k9_relat_1(k2_funct_1(B_198),A_199) = k10_relat_1(B_198,A_199)
      | ~ v2_funct_1(B_198)
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_10250,plain,(
    ! [B_403] :
      ( k10_relat_1(B_403,k1_relat_1(k2_funct_1(B_403))) = k2_relat_1(k2_funct_1(B_403))
      | ~ v2_funct_1(B_403)
      | ~ v1_funct_1(B_403)
      | ~ v1_relat_1(B_403)
      | ~ v1_relat_1(k2_funct_1(B_403)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1651])).

tff(c_1427,plain,(
    ! [A_184,B_185,C_186] :
      ( k2_relset_1(A_184,B_185,C_186) = k2_relat_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1433,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_1427])).

tff(c_1440,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1433])).

tff(c_2113,plain,(
    ! [B_218,A_219] :
      ( k9_relat_1(B_218,k10_relat_1(B_218,A_219)) = A_219
      | ~ r1_tarski(A_219,k2_relat_1(B_218))
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2119,plain,(
    ! [A_219] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_219)) = A_219
      | ~ r1_tarski(A_219,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1440,c_2113])).

tff(c_2142,plain,(
    ! [A_219] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_219)) = A_219
      | ~ r1_tarski(A_219,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_98,c_2119])).

tff(c_10261,plain,
    ( k9_relat_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10250,c_2142])).

tff(c_10288,plain,
    ( k9_relat_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_98,c_92,c_10261])).

tff(c_10294,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10288])).

tff(c_10297,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_10294])).

tff(c_10307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_98,c_10297])).

tff(c_10309,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10288])).

tff(c_446,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_839,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_830,c_24])).

tff(c_841,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_839])).

tff(c_1443,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_841])).

tff(c_96,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_1521,plain,(
    ! [A_187,B_188,C_189] :
      ( k1_relset_1(A_187,B_188,C_189) = k1_relat_1(C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1533,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_1521])).

tff(c_2818,plain,(
    ! [B_254,A_255,C_256] :
      ( k1_xboole_0 = B_254
      | k1_relset_1(A_255,B_254,C_256) = A_255
      | ~ v1_funct_2(C_256,A_255,B_254)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2830,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_2818])).

tff(c_2843,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1533,c_2830])).

tff(c_2844,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1443,c_2843])).

tff(c_2885,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2844,c_20])).

tff(c_2902,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_1440,c_2885])).

tff(c_48,plain,(
    ! [A_25] :
      ( k2_relat_1(k2_funct_1(A_25)) = k1_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1329,plain,(
    ! [A_180] :
      ( m1_subset_1(A_180,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_180),k2_relat_1(A_180))))
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54,plain,(
    ! [C_31,B_30,A_29] :
      ( v5_relat_1(C_31,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1370,plain,(
    ! [A_180] :
      ( v5_relat_1(A_180,k2_relat_1(A_180))
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(resolution,[status(thm)],[c_1329,c_54])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1465,plain,(
    ! [A_9] :
      ( r1_tarski('#skF_2',A_9)
      | ~ v5_relat_1('#skF_3',A_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1440,c_16])).

tff(c_1568,plain,(
    ! [A_197] :
      ( r1_tarski('#skF_2',A_197)
      | ~ v5_relat_1('#skF_3',A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_1465])).

tff(c_1575,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1370,c_1568])).

tff(c_1590,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_98,c_1440,c_1575])).

tff(c_10308,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | k9_relat_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10288])).

tff(c_10361,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_10308])).

tff(c_10364,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_10361])).

tff(c_10373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_98,c_92,c_1590,c_1440,c_10364])).

tff(c_10374,plain,(
    k9_relat_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10308])).

tff(c_10391,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_10374])).

tff(c_10410,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_98,c_92,c_2902,c_2844,c_10391])).

tff(c_22,plain,(
    ! [A_13] :
      ( k10_relat_1(A_13,k2_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1468,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1440,c_22])).

tff(c_1506,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_1468])).

tff(c_2858,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2844,c_1506])).

tff(c_1665,plain,(
    ! [B_198] :
      ( k10_relat_1(B_198,k1_relat_1(k2_funct_1(B_198))) = k2_relat_1(k2_funct_1(B_198))
      | ~ v2_funct_1(B_198)
      | ~ v1_funct_1(B_198)
      | ~ v1_relat_1(B_198)
      | ~ v1_relat_1(k2_funct_1(B_198)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1651])).

tff(c_10421,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10410,c_1665])).

tff(c_10469,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10309,c_830,c_98,c_92,c_2858,c_10421])).

tff(c_76,plain,(
    ! [A_45] :
      ( m1_subset_1(A_45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_45),k2_relat_1(A_45))))
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_10623,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10469,c_76])).

tff(c_10701,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10309,c_446,c_10410,c_10623])).

tff(c_10703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_10701])).

tff(c_10704,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_839])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10752,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10704,c_8])).

tff(c_28,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_447,plain,(
    ! [A_82] :
      ( k1_relat_1(A_82) != k1_xboole_0
      | k1_xboole_0 = A_82
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_456,plain,(
    ! [A_18] :
      ( k1_relat_1(k6_relat_1(A_18)) != k1_xboole_0
      | k6_relat_1(A_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_447])).

tff(c_461,plain,(
    ! [A_18] :
      ( k1_xboole_0 != A_18
      | k6_relat_1(A_18) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_456])).

tff(c_10745,plain,(
    ! [A_18] :
      ( A_18 != '#skF_3'
      | k6_relat_1(A_18) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10704,c_10704,c_461])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_463,plain,(
    ! [A_83] :
      ( k1_xboole_0 != A_83
      | k6_relat_1(A_83) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_456])).

tff(c_30,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_133,plain,(
    ! [A_56] :
      ( v1_xboole_0(k2_relat_1(A_56))
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ! [A_16] :
      ( v1_funct_1(A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_154,plain,(
    ! [A_59] :
      ( v1_funct_1(k2_relat_1(A_59))
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_133,c_32])).

tff(c_157,plain,(
    ! [A_15] :
      ( v1_funct_1(A_15)
      | ~ v1_xboole_0(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_154])).

tff(c_472,plain,(
    ! [A_83] :
      ( v1_funct_1(A_83)
      | ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 != A_83 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_157])).

tff(c_496,plain,(
    ! [A_83] :
      ( v1_funct_1(A_83)
      | k1_xboole_0 != A_83 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_472])).

tff(c_10827,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10704,c_496])).

tff(c_40,plain,(
    ! [A_18] : v2_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10706,plain,(
    ! [A_407] :
      ( k10_relat_1(A_407,k2_relat_1(A_407)) = k1_relat_1(A_407)
      | ~ v1_relat_1(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10721,plain,(
    ! [A_15] :
      ( k10_relat_1(k6_relat_1(A_15),A_15) = k1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_10706])).

tff(c_10725,plain,(
    ! [A_15] : k10_relat_1(k6_relat_1(A_15),A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_10721])).

tff(c_11166,plain,(
    ! [A_450] :
      ( k1_relat_1(k2_funct_1(A_450)) = k2_relat_1(A_450)
      | ~ v2_funct_1(A_450)
      | ~ v1_funct_1(A_450)
      | ~ v1_relat_1(A_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_20805,plain,(
    ! [A_726] :
      ( k9_relat_1(k2_funct_1(A_726),k2_relat_1(A_726)) = k2_relat_1(k2_funct_1(A_726))
      | ~ v1_relat_1(k2_funct_1(A_726))
      | ~ v2_funct_1(A_726)
      | ~ v1_funct_1(A_726)
      | ~ v1_relat_1(A_726) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11166,c_20])).

tff(c_20896,plain,(
    ! [A_15] :
      ( k9_relat_1(k2_funct_1(k6_relat_1(A_15)),A_15) = k2_relat_1(k2_funct_1(k6_relat_1(A_15)))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_15)))
      | ~ v2_funct_1(k6_relat_1(A_15))
      | ~ v1_funct_1(k6_relat_1(A_15))
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_20805])).

tff(c_52847,plain,(
    ! [A_992] :
      ( k9_relat_1(k2_funct_1(k6_relat_1(A_992)),A_992) = k2_relat_1(k2_funct_1(k6_relat_1(A_992)))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(A_992)))
      | ~ v1_funct_1(k6_relat_1(A_992)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_20896])).

tff(c_52874,plain,(
    ! [A_992] :
      ( k9_relat_1(k2_funct_1(k6_relat_1(A_992)),A_992) = k2_relat_1(k2_funct_1(k6_relat_1(A_992)))
      | ~ v1_funct_1(k6_relat_1(A_992))
      | ~ v1_relat_1(k6_relat_1(A_992)) ) ),
    inference(resolution,[status(thm)],[c_36,c_52847])).

tff(c_175861,plain,(
    ! [A_1408] :
      ( k9_relat_1(k2_funct_1(k6_relat_1(A_1408)),A_1408) = k2_relat_1(k2_funct_1(k6_relat_1(A_1408)))
      | ~ v1_funct_1(k6_relat_1(A_1408)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_52874])).

tff(c_46,plain,(
    ! [B_24,A_23] :
      ( k9_relat_1(k2_funct_1(B_24),A_23) = k10_relat_1(B_24,A_23)
      | ~ v2_funct_1(B_24)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_175884,plain,(
    ! [A_1408] :
      ( k2_relat_1(k2_funct_1(k6_relat_1(A_1408))) = k10_relat_1(k6_relat_1(A_1408),A_1408)
      | ~ v2_funct_1(k6_relat_1(A_1408))
      | ~ v1_funct_1(k6_relat_1(A_1408))
      | ~ v1_relat_1(k6_relat_1(A_1408))
      | ~ v1_funct_1(k6_relat_1(A_1408)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175861,c_46])).

tff(c_175962,plain,(
    ! [A_1409] :
      ( k2_relat_1(k2_funct_1(k6_relat_1(A_1409))) = A_1409
      | ~ v1_funct_1(k6_relat_1(A_1409)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_10725,c_175884])).

tff(c_705,plain,(
    ! [A_97] :
      ( v1_relat_1(k2_funct_1(A_97))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_712,plain,(
    ! [A_97] :
      ( k2_relat_1(k2_funct_1(A_97)) != k1_xboole_0
      | k2_funct_1(A_97) = k1_xboole_0
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_705,c_24])).

tff(c_13098,plain,(
    ! [A_97] :
      ( k2_relat_1(k2_funct_1(A_97)) != '#skF_3'
      | k2_funct_1(A_97) = '#skF_3'
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10704,c_10704,c_712])).

tff(c_176535,plain,(
    ! [A_1409] :
      ( A_1409 != '#skF_3'
      | k2_funct_1(k6_relat_1(A_1409)) = '#skF_3'
      | ~ v1_funct_1(k6_relat_1(A_1409))
      | ~ v1_relat_1(k6_relat_1(A_1409))
      | ~ v1_funct_1(k6_relat_1(A_1409)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175962,c_13098])).

tff(c_178063,plain,(
    ! [A_1421] :
      ( A_1421 != '#skF_3'
      | k2_funct_1(k6_relat_1(A_1421)) = '#skF_3'
      | ~ v1_funct_1(k6_relat_1(A_1421)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_176535])).

tff(c_178117,plain,(
    ! [A_18] :
      ( A_18 != '#skF_3'
      | k2_funct_1(k6_relat_1(A_18)) = '#skF_3'
      | ~ v1_funct_1('#skF_3')
      | A_18 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10745,c_178063])).

tff(c_178127,plain,(
    ! [A_1422] :
      ( k2_funct_1(k6_relat_1(A_1422)) = '#skF_3'
      | A_1422 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10827,c_178117])).

tff(c_178450,plain,(
    ! [A_18] :
      ( k2_funct_1('#skF_3') = '#skF_3'
      | A_18 != '#skF_3'
      | A_18 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10745,c_178127])).

tff(c_178886,plain,(
    ! [A_18] :
      ( A_18 != '#skF_3'
      | A_18 != '#skF_3' ) ),
    inference(splitLeft,[status(thm)],[c_178450])).

tff(c_178892,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_178886])).

tff(c_178893,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_178450])).

tff(c_142,plain,(
    ! [A_15] :
      ( v1_xboole_0(A_15)
      | ~ v1_xboole_0(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_133])).

tff(c_478,plain,(
    ! [A_83] :
      ( v1_xboole_0(A_83)
      | ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 != A_83 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_142])).

tff(c_500,plain,(
    ! [A_83] :
      ( v1_xboole_0(A_83)
      | k1_xboole_0 != A_83 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_478])).

tff(c_10744,plain,(
    ! [A_83] :
      ( v1_xboole_0(A_83)
      | A_83 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10704,c_500])).

tff(c_18,plain,(
    ! [A_11] :
      ( v1_xboole_0(k2_relat_1(A_11))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_160,plain,(
    ! [B_62,A_63] :
      ( ~ v1_xboole_0(B_62)
      | B_62 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_167,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_2,c_160])).

tff(c_174,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) = k1_xboole_0
      | ~ v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_167])).

tff(c_10897,plain,(
    ! [A_420] :
      ( k2_relat_1(A_420) = '#skF_3'
      | ~ v1_xboole_0(A_420) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10704,c_174])).

tff(c_10925,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10744,c_10897])).

tff(c_11288,plain,(
    ! [A_464,B_465,C_466] :
      ( k2_relset_1(A_464,B_465,C_466) = k2_relat_1(C_466)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_464,B_465))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_11292,plain,(
    ! [A_464,B_465] : k2_relset_1(A_464,B_465,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10752,c_11288])).

tff(c_11294,plain,(
    ! [A_464,B_465] : k2_relset_1(A_464,B_465,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10925,c_11292])).

tff(c_11295,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11294,c_90])).

tff(c_11303,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11295,c_574])).

tff(c_178942,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178893,c_11303])).

tff(c_178948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10752,c_178942])).

tff(c_178949,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_179467,plain,(
    ! [C_1501,A_1502,B_1503] :
      ( v1_xboole_0(C_1501)
      | ~ m1_subset_1(C_1501,k1_zfmisc_1(k2_zfmisc_1(A_1502,B_1503)))
      | ~ v1_xboole_0(A_1502) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_179479,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_179467])).

tff(c_179482,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_179479])).

tff(c_179490,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(resolution,[status(thm)],[c_500,c_179482])).

tff(c_178950,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_180002,plain,(
    ! [A_1532,B_1533,C_1534] :
      ( k1_relset_1(A_1532,B_1533,C_1534) = k1_relat_1(C_1534)
      | ~ m1_subset_1(C_1534,k1_zfmisc_1(k2_zfmisc_1(A_1532,B_1533))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_180017,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_178950,c_180002])).

tff(c_181564,plain,(
    ! [B_1609,C_1610,A_1611] :
      ( k1_xboole_0 = B_1609
      | v1_funct_2(C_1610,A_1611,B_1609)
      | k1_relset_1(A_1611,B_1609,C_1610) != A_1611
      | ~ m1_subset_1(C_1610,k1_zfmisc_1(k2_zfmisc_1(A_1611,B_1609))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_181573,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_178950,c_181564])).

tff(c_181584,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180017,c_181573])).

tff(c_181585,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_178949,c_179490,c_181584])).

tff(c_181594,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_181585])).

tff(c_181597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179258,c_98,c_92,c_179915,c_181594])).

tff(c_181598,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_179479])).

tff(c_181614,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_181598,c_174])).

tff(c_181635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179277,c_181614])).

tff(c_181636,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_179267])).

tff(c_481,plain,(
    ! [A_83] :
      ( k1_relat_1(k1_xboole_0) = A_83
      | k1_xboole_0 != A_83 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_28])).

tff(c_181824,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181636,c_181636,c_481])).

tff(c_181665,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181636,c_8])).

tff(c_182542,plain,(
    ! [A_1698,B_1699,C_1700] :
      ( k1_relset_1(A_1698,B_1699,C_1700) = k1_relat_1(C_1700)
      | ~ m1_subset_1(C_1700,k1_zfmisc_1(k2_zfmisc_1(A_1698,B_1699))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_182546,plain,(
    ! [A_1698,B_1699] : k1_relset_1(A_1698,B_1699,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_181665,c_182542])).

tff(c_182548,plain,(
    ! [A_1698,B_1699] : k1_relset_1(A_1698,B_1699,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181824,c_182546])).

tff(c_68,plain,(
    ! [C_44,B_43] :
      ( v1_funct_2(C_44,k1_xboole_0,B_43)
      | k1_relset_1(k1_xboole_0,B_43,C_44) != k1_xboole_0
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_182881,plain,(
    ! [C_1740,B_1741] :
      ( v1_funct_2(C_1740,'#skF_3',B_1741)
      | k1_relset_1('#skF_3',B_1741,C_1740) != '#skF_3'
      | ~ m1_subset_1(C_1740,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1741))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181636,c_181636,c_181636,c_181636,c_68])).

tff(c_182885,plain,(
    ! [B_1741] :
      ( v1_funct_2('#skF_3','#skF_3',B_1741)
      | k1_relset_1('#skF_3',B_1741,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_181665,c_182881])).

tff(c_182888,plain,(
    ! [B_1741] : v1_funct_2('#skF_3','#skF_3',B_1741) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182548,c_182885])).

tff(c_181657,plain,(
    ! [A_83] :
      ( v1_xboole_0(A_83)
      | A_83 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181636,c_500])).

tff(c_182106,plain,(
    ! [A_1654] :
      ( k2_relat_1(A_1654) = '#skF_3'
      | ~ v1_xboole_0(A_1654) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181636,c_174])).

tff(c_182170,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_181657,c_182106])).

tff(c_182521,plain,(
    ! [A_1693,B_1694,C_1695] :
      ( k2_relset_1(A_1693,B_1694,C_1695) = k2_relat_1(C_1695)
      | ~ m1_subset_1(C_1695,k1_zfmisc_1(k2_zfmisc_1(A_1693,B_1694))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_182525,plain,(
    ! [A_1693,B_1694] : k2_relset_1(A_1693,B_1694,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_181665,c_182521])).

tff(c_182527,plain,(
    ! [A_1693,B_1694] : k2_relset_1(A_1693,B_1694,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182170,c_182525])).

tff(c_182528,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182527,c_90])).

tff(c_181637,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_179267])).

tff(c_181673,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181636,c_181637])).

tff(c_506,plain,(
    ! [A_84] :
      ( v1_xboole_0(A_84)
      | k1_xboole_0 != A_84 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_478])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_relat_1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_541,plain,(
    ! [A_84] :
      ( v1_relat_1(A_84)
      | k1_xboole_0 != A_84 ) ),
    inference(resolution,[status(thm)],[c_506,c_12])).

tff(c_181755,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181636,c_541])).

tff(c_181752,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181636,c_496])).

tff(c_181760,plain,(
    ! [A_1621] :
      ( k2_relat_1(A_1621) = '#skF_3'
      | ~ v1_xboole_0(A_1621) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181636,c_174])).

tff(c_181838,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_181657,c_181760])).

tff(c_182050,plain,(
    ! [A_1653] :
      ( k1_relat_1(k2_funct_1(A_1653)) = k2_relat_1(A_1653)
      | ~ v2_funct_1(A_1653)
      | ~ v1_funct_1(A_1653)
      | ~ v1_relat_1(A_1653) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_179257,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_178950,c_179246])).

tff(c_26,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_179276,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0
    | k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_179257,c_26])).

tff(c_181831,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181636,c_181636,c_179276])).

tff(c_181832,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_181831])).

tff(c_182059,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_182050,c_181832])).

tff(c_182069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181755,c_181752,c_92,c_181838,c_182059])).

tff(c_182070,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_181831])).

tff(c_179275,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0
    | k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_179257,c_24])).

tff(c_181758,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181636,c_181636,c_179275])).

tff(c_181759,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_181758])).

tff(c_182073,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182070,c_181759])).

tff(c_182081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181673,c_182073])).

tff(c_182082,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_181758])).

tff(c_182086,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182082,c_178949])).

tff(c_182536,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182528,c_182086])).

tff(c_182891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182888,c_182536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:49:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.33/37.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.33/37.40  
% 48.33/37.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.33/37.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 48.33/37.40  
% 48.33/37.40  %Foreground sorts:
% 48.33/37.40  
% 48.33/37.40  
% 48.33/37.40  %Background operators:
% 48.33/37.40  
% 48.33/37.40  
% 48.33/37.40  %Foreground operators:
% 48.33/37.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 48.33/37.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 48.33/37.40  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 48.33/37.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 48.33/37.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.33/37.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 48.33/37.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 48.33/37.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 48.33/37.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 48.33/37.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 48.33/37.40  tff('#skF_2', type, '#skF_2': $i).
% 48.33/37.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 48.33/37.40  tff('#skF_3', type, '#skF_3': $i).
% 48.33/37.40  tff('#skF_1', type, '#skF_1': $i).
% 48.33/37.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 48.33/37.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 48.33/37.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 48.33/37.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.33/37.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 48.33/37.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 48.33/37.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 48.33/37.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 48.33/37.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.33/37.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 48.33/37.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 48.33/37.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 48.33/37.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 48.33/37.40  
% 48.59/37.44  tff(f_210, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 48.59/37.44  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 48.59/37.44  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 48.59/37.44  tff(f_153, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 48.59/37.44  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 48.59/37.44  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 48.59/37.44  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 48.59/37.44  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 48.59/37.44  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 48.59/37.44  tff(f_149, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 48.59/37.44  tff(f_171, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 48.59/37.44  tff(f_181, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 48.59/37.44  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 48.59/37.44  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 48.59/37.44  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 48.59/37.44  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 48.59/37.44  tff(f_78, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 48.59/37.44  tff(f_94, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 48.59/37.44  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 48.59/37.44  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 48.59/37.44  tff(f_82, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 48.59/37.44  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 48.59/37.44  tff(f_145, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 48.59/37.44  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 48.59/37.44  tff(c_94, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 48.59/37.44  tff(c_179246, plain, (![C_1455, A_1456, B_1457]: (v1_relat_1(C_1455) | ~m1_subset_1(C_1455, k1_zfmisc_1(k2_zfmisc_1(A_1456, B_1457))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 48.59/37.44  tff(c_179258, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_179246])).
% 48.59/37.44  tff(c_24, plain, (![A_14]: (k2_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 48.59/37.44  tff(c_179267, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_179258, c_24])).
% 48.59/37.44  tff(c_179277, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_179267])).
% 48.59/37.44  tff(c_98, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 48.59/37.44  tff(c_92, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 48.59/37.44  tff(c_90, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_210])).
% 48.59/37.44  tff(c_179898, plain, (![A_1529, B_1530, C_1531]: (k2_relset_1(A_1529, B_1530, C_1531)=k2_relat_1(C_1531) | ~m1_subset_1(C_1531, k1_zfmisc_1(k2_zfmisc_1(A_1529, B_1530))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 48.59/37.44  tff(c_179907, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_179898])).
% 48.59/37.44  tff(c_179915, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_179907])).
% 48.59/37.44  tff(c_50, plain, (![A_25]: (k1_relat_1(k2_funct_1(A_25))=k2_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_128])).
% 48.59/37.44  tff(c_245, plain, (![A_69]: (v1_funct_1(k2_funct_1(A_69)) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_90])).
% 48.59/37.44  tff(c_88, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 48.59/37.44  tff(c_244, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_88])).
% 48.59/37.44  tff(c_248, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_245, c_244])).
% 48.59/37.44  tff(c_251, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_248])).
% 48.59/37.44  tff(c_433, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 48.59/37.44  tff(c_436, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_433])).
% 48.59/37.44  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_251, c_436])).
% 48.59/37.44  tff(c_445, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_88])).
% 48.59/37.44  tff(c_574, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_445])).
% 48.59/37.44  tff(c_822, plain, (![C_112, A_113, B_114]: (v1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 48.59/37.44  tff(c_830, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_822])).
% 48.59/37.44  tff(c_36, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_90])).
% 48.59/37.44  tff(c_20, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 48.59/37.44  tff(c_1651, plain, (![B_198, A_199]: (k9_relat_1(k2_funct_1(B_198), A_199)=k10_relat_1(B_198, A_199) | ~v2_funct_1(B_198) | ~v1_funct_1(B_198) | ~v1_relat_1(B_198))), inference(cnfTransformation, [status(thm)], [f_118])).
% 48.59/37.44  tff(c_10250, plain, (![B_403]: (k10_relat_1(B_403, k1_relat_1(k2_funct_1(B_403)))=k2_relat_1(k2_funct_1(B_403)) | ~v2_funct_1(B_403) | ~v1_funct_1(B_403) | ~v1_relat_1(B_403) | ~v1_relat_1(k2_funct_1(B_403)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1651])).
% 48.59/37.44  tff(c_1427, plain, (![A_184, B_185, C_186]: (k2_relset_1(A_184, B_185, C_186)=k2_relat_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 48.59/37.44  tff(c_1433, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_1427])).
% 48.59/37.44  tff(c_1440, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1433])).
% 48.59/37.44  tff(c_2113, plain, (![B_218, A_219]: (k9_relat_1(B_218, k10_relat_1(B_218, A_219))=A_219 | ~r1_tarski(A_219, k2_relat_1(B_218)) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218))), inference(cnfTransformation, [status(thm)], [f_102])).
% 48.59/37.44  tff(c_2119, plain, (![A_219]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_219))=A_219 | ~r1_tarski(A_219, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1440, c_2113])).
% 48.59/37.44  tff(c_2142, plain, (![A_219]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_219))=A_219 | ~r1_tarski(A_219, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_98, c_2119])).
% 48.59/37.44  tff(c_10261, plain, (k9_relat_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10250, c_2142])).
% 48.59/37.44  tff(c_10288, plain, (k9_relat_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_98, c_92, c_10261])).
% 48.59/37.44  tff(c_10294, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10288])).
% 48.59/37.44  tff(c_10297, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_10294])).
% 48.59/37.44  tff(c_10307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_830, c_98, c_10297])).
% 48.59/37.44  tff(c_10309, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10288])).
% 48.59/37.44  tff(c_446, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_88])).
% 48.59/37.44  tff(c_839, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_830, c_24])).
% 48.59/37.44  tff(c_841, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_839])).
% 48.59/37.44  tff(c_1443, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_841])).
% 48.59/37.44  tff(c_96, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 48.59/37.44  tff(c_1521, plain, (![A_187, B_188, C_189]: (k1_relset_1(A_187, B_188, C_189)=k1_relat_1(C_189) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 48.59/37.44  tff(c_1533, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_1521])).
% 48.59/37.44  tff(c_2818, plain, (![B_254, A_255, C_256]: (k1_xboole_0=B_254 | k1_relset_1(A_255, B_254, C_256)=A_255 | ~v1_funct_2(C_256, A_255, B_254) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_254))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 48.59/37.44  tff(c_2830, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_94, c_2818])).
% 48.59/37.44  tff(c_2843, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1533, c_2830])).
% 48.59/37.44  tff(c_2844, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1443, c_2843])).
% 48.59/37.44  tff(c_2885, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2844, c_20])).
% 48.59/37.44  tff(c_2902, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_830, c_1440, c_2885])).
% 48.59/37.44  tff(c_48, plain, (![A_25]: (k2_relat_1(k2_funct_1(A_25))=k1_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_128])).
% 48.59/37.44  tff(c_1329, plain, (![A_180]: (m1_subset_1(A_180, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_180), k2_relat_1(A_180)))) | ~v1_funct_1(A_180) | ~v1_relat_1(A_180))), inference(cnfTransformation, [status(thm)], [f_181])).
% 48.59/37.44  tff(c_54, plain, (![C_31, B_30, A_29]: (v5_relat_1(C_31, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 48.59/37.44  tff(c_1370, plain, (![A_180]: (v5_relat_1(A_180, k2_relat_1(A_180)) | ~v1_funct_1(A_180) | ~v1_relat_1(A_180))), inference(resolution, [status(thm)], [c_1329, c_54])).
% 48.59/37.44  tff(c_16, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 48.59/37.44  tff(c_1465, plain, (![A_9]: (r1_tarski('#skF_2', A_9) | ~v5_relat_1('#skF_3', A_9) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1440, c_16])).
% 48.59/37.44  tff(c_1568, plain, (![A_197]: (r1_tarski('#skF_2', A_197) | ~v5_relat_1('#skF_3', A_197))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_1465])).
% 48.59/37.44  tff(c_1575, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1370, c_1568])).
% 48.59/37.44  tff(c_1590, plain, (r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_830, c_98, c_1440, c_1575])).
% 48.59/37.44  tff(c_10308, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | k9_relat_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10288])).
% 48.59/37.44  tff(c_10361, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_10308])).
% 48.59/37.44  tff(c_10364, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_50, c_10361])).
% 48.59/37.44  tff(c_10373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_830, c_98, c_92, c_1590, c_1440, c_10364])).
% 48.59/37.44  tff(c_10374, plain, (k9_relat_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10308])).
% 48.59/37.44  tff(c_10391, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_10374])).
% 48.59/37.44  tff(c_10410, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_830, c_98, c_92, c_2902, c_2844, c_10391])).
% 48.59/37.44  tff(c_22, plain, (![A_13]: (k10_relat_1(A_13, k2_relat_1(A_13))=k1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 48.59/37.44  tff(c_1468, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1440, c_22])).
% 48.59/37.44  tff(c_1506, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_830, c_1468])).
% 48.59/37.44  tff(c_2858, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2844, c_1506])).
% 48.59/37.44  tff(c_1665, plain, (![B_198]: (k10_relat_1(B_198, k1_relat_1(k2_funct_1(B_198)))=k2_relat_1(k2_funct_1(B_198)) | ~v2_funct_1(B_198) | ~v1_funct_1(B_198) | ~v1_relat_1(B_198) | ~v1_relat_1(k2_funct_1(B_198)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1651])).
% 48.59/37.44  tff(c_10421, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10410, c_1665])).
% 48.59/37.44  tff(c_10469, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10309, c_830, c_98, c_92, c_2858, c_10421])).
% 48.59/37.44  tff(c_76, plain, (![A_45]: (m1_subset_1(A_45, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_45), k2_relat_1(A_45)))) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_181])).
% 48.59/37.44  tff(c_10623, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10469, c_76])).
% 48.59/37.44  tff(c_10701, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10309, c_446, c_10410, c_10623])).
% 48.59/37.44  tff(c_10703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_574, c_10701])).
% 48.59/37.44  tff(c_10704, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_839])).
% 48.59/37.44  tff(c_8, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 48.59/37.44  tff(c_10752, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_10704, c_8])).
% 48.59/37.44  tff(c_28, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_78])).
% 48.59/37.44  tff(c_38, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 48.59/37.44  tff(c_447, plain, (![A_82]: (k1_relat_1(A_82)!=k1_xboole_0 | k1_xboole_0=A_82 | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_74])).
% 48.59/37.44  tff(c_456, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))!=k1_xboole_0 | k6_relat_1(A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_447])).
% 48.59/37.44  tff(c_461, plain, (![A_18]: (k1_xboole_0!=A_18 | k6_relat_1(A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_456])).
% 48.59/37.44  tff(c_10745, plain, (![A_18]: (A_18!='#skF_3' | k6_relat_1(A_18)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10704, c_10704, c_461])).
% 48.59/37.44  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 48.59/37.44  tff(c_463, plain, (![A_83]: (k1_xboole_0!=A_83 | k6_relat_1(A_83)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_456])).
% 48.59/37.44  tff(c_30, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_78])).
% 48.59/37.44  tff(c_133, plain, (![A_56]: (v1_xboole_0(k2_relat_1(A_56)) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_58])).
% 48.59/37.44  tff(c_32, plain, (![A_16]: (v1_funct_1(A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 48.59/37.44  tff(c_154, plain, (![A_59]: (v1_funct_1(k2_relat_1(A_59)) | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_133, c_32])).
% 48.59/37.44  tff(c_157, plain, (![A_15]: (v1_funct_1(A_15) | ~v1_xboole_0(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_154])).
% 48.59/37.44  tff(c_472, plain, (![A_83]: (v1_funct_1(A_83) | ~v1_xboole_0(k1_xboole_0) | k1_xboole_0!=A_83)), inference(superposition, [status(thm), theory('equality')], [c_463, c_157])).
% 48.59/37.44  tff(c_496, plain, (![A_83]: (v1_funct_1(A_83) | k1_xboole_0!=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_472])).
% 48.59/37.44  tff(c_10827, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10704, c_496])).
% 48.59/37.44  tff(c_40, plain, (![A_18]: (v2_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 48.59/37.44  tff(c_10706, plain, (![A_407]: (k10_relat_1(A_407, k2_relat_1(A_407))=k1_relat_1(A_407) | ~v1_relat_1(A_407))), inference(cnfTransformation, [status(thm)], [f_66])).
% 48.59/37.44  tff(c_10721, plain, (![A_15]: (k10_relat_1(k6_relat_1(A_15), A_15)=k1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_10706])).
% 48.59/37.44  tff(c_10725, plain, (![A_15]: (k10_relat_1(k6_relat_1(A_15), A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28, c_10721])).
% 48.59/37.44  tff(c_11166, plain, (![A_450]: (k1_relat_1(k2_funct_1(A_450))=k2_relat_1(A_450) | ~v2_funct_1(A_450) | ~v1_funct_1(A_450) | ~v1_relat_1(A_450))), inference(cnfTransformation, [status(thm)], [f_128])).
% 48.59/37.44  tff(c_20805, plain, (![A_726]: (k9_relat_1(k2_funct_1(A_726), k2_relat_1(A_726))=k2_relat_1(k2_funct_1(A_726)) | ~v1_relat_1(k2_funct_1(A_726)) | ~v2_funct_1(A_726) | ~v1_funct_1(A_726) | ~v1_relat_1(A_726))), inference(superposition, [status(thm), theory('equality')], [c_11166, c_20])).
% 48.59/37.44  tff(c_20896, plain, (![A_15]: (k9_relat_1(k2_funct_1(k6_relat_1(A_15)), A_15)=k2_relat_1(k2_funct_1(k6_relat_1(A_15))) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_15))) | ~v2_funct_1(k6_relat_1(A_15)) | ~v1_funct_1(k6_relat_1(A_15)) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_20805])).
% 48.59/37.44  tff(c_52847, plain, (![A_992]: (k9_relat_1(k2_funct_1(k6_relat_1(A_992)), A_992)=k2_relat_1(k2_funct_1(k6_relat_1(A_992))) | ~v1_relat_1(k2_funct_1(k6_relat_1(A_992))) | ~v1_funct_1(k6_relat_1(A_992)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_20896])).
% 48.59/37.44  tff(c_52874, plain, (![A_992]: (k9_relat_1(k2_funct_1(k6_relat_1(A_992)), A_992)=k2_relat_1(k2_funct_1(k6_relat_1(A_992))) | ~v1_funct_1(k6_relat_1(A_992)) | ~v1_relat_1(k6_relat_1(A_992)))), inference(resolution, [status(thm)], [c_36, c_52847])).
% 48.59/37.44  tff(c_175861, plain, (![A_1408]: (k9_relat_1(k2_funct_1(k6_relat_1(A_1408)), A_1408)=k2_relat_1(k2_funct_1(k6_relat_1(A_1408))) | ~v1_funct_1(k6_relat_1(A_1408)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_52874])).
% 48.59/37.44  tff(c_46, plain, (![B_24, A_23]: (k9_relat_1(k2_funct_1(B_24), A_23)=k10_relat_1(B_24, A_23) | ~v2_funct_1(B_24) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_118])).
% 48.59/37.44  tff(c_175884, plain, (![A_1408]: (k2_relat_1(k2_funct_1(k6_relat_1(A_1408)))=k10_relat_1(k6_relat_1(A_1408), A_1408) | ~v2_funct_1(k6_relat_1(A_1408)) | ~v1_funct_1(k6_relat_1(A_1408)) | ~v1_relat_1(k6_relat_1(A_1408)) | ~v1_funct_1(k6_relat_1(A_1408)))), inference(superposition, [status(thm), theory('equality')], [c_175861, c_46])).
% 48.59/37.44  tff(c_175962, plain, (![A_1409]: (k2_relat_1(k2_funct_1(k6_relat_1(A_1409)))=A_1409 | ~v1_funct_1(k6_relat_1(A_1409)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_10725, c_175884])).
% 48.59/37.44  tff(c_705, plain, (![A_97]: (v1_relat_1(k2_funct_1(A_97)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_90])).
% 48.59/37.44  tff(c_712, plain, (![A_97]: (k2_relat_1(k2_funct_1(A_97))!=k1_xboole_0 | k2_funct_1(A_97)=k1_xboole_0 | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_705, c_24])).
% 48.59/37.44  tff(c_13098, plain, (![A_97]: (k2_relat_1(k2_funct_1(A_97))!='#skF_3' | k2_funct_1(A_97)='#skF_3' | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_10704, c_10704, c_712])).
% 48.59/37.44  tff(c_176535, plain, (![A_1409]: (A_1409!='#skF_3' | k2_funct_1(k6_relat_1(A_1409))='#skF_3' | ~v1_funct_1(k6_relat_1(A_1409)) | ~v1_relat_1(k6_relat_1(A_1409)) | ~v1_funct_1(k6_relat_1(A_1409)))), inference(superposition, [status(thm), theory('equality')], [c_175962, c_13098])).
% 48.59/37.44  tff(c_178063, plain, (![A_1421]: (A_1421!='#skF_3' | k2_funct_1(k6_relat_1(A_1421))='#skF_3' | ~v1_funct_1(k6_relat_1(A_1421)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_176535])).
% 48.59/37.44  tff(c_178117, plain, (![A_18]: (A_18!='#skF_3' | k2_funct_1(k6_relat_1(A_18))='#skF_3' | ~v1_funct_1('#skF_3') | A_18!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10745, c_178063])).
% 48.59/37.44  tff(c_178127, plain, (![A_1422]: (k2_funct_1(k6_relat_1(A_1422))='#skF_3' | A_1422!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10827, c_178117])).
% 48.59/37.44  tff(c_178450, plain, (![A_18]: (k2_funct_1('#skF_3')='#skF_3' | A_18!='#skF_3' | A_18!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10745, c_178127])).
% 48.59/37.44  tff(c_178886, plain, (![A_18]: (A_18!='#skF_3' | A_18!='#skF_3')), inference(splitLeft, [status(thm)], [c_178450])).
% 48.59/37.44  tff(c_178892, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_178886])).
% 48.59/37.44  tff(c_178893, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_178450])).
% 48.59/37.44  tff(c_142, plain, (![A_15]: (v1_xboole_0(A_15) | ~v1_xboole_0(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_133])).
% 48.59/37.44  tff(c_478, plain, (![A_83]: (v1_xboole_0(A_83) | ~v1_xboole_0(k1_xboole_0) | k1_xboole_0!=A_83)), inference(superposition, [status(thm), theory('equality')], [c_463, c_142])).
% 48.59/37.44  tff(c_500, plain, (![A_83]: (v1_xboole_0(A_83) | k1_xboole_0!=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_478])).
% 48.59/37.44  tff(c_10744, plain, (![A_83]: (v1_xboole_0(A_83) | A_83!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10704, c_500])).
% 48.59/37.44  tff(c_18, plain, (![A_11]: (v1_xboole_0(k2_relat_1(A_11)) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 48.59/37.44  tff(c_160, plain, (![B_62, A_63]: (~v1_xboole_0(B_62) | B_62=A_63 | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_36])).
% 48.59/37.44  tff(c_167, plain, (![A_64]: (k1_xboole_0=A_64 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_2, c_160])).
% 48.59/37.44  tff(c_174, plain, (![A_11]: (k2_relat_1(A_11)=k1_xboole_0 | ~v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_18, c_167])).
% 48.59/37.44  tff(c_10897, plain, (![A_420]: (k2_relat_1(A_420)='#skF_3' | ~v1_xboole_0(A_420))), inference(demodulation, [status(thm), theory('equality')], [c_10704, c_174])).
% 48.59/37.44  tff(c_10925, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_10744, c_10897])).
% 48.59/37.44  tff(c_11288, plain, (![A_464, B_465, C_466]: (k2_relset_1(A_464, B_465, C_466)=k2_relat_1(C_466) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_464, B_465))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 48.59/37.44  tff(c_11292, plain, (![A_464, B_465]: (k2_relset_1(A_464, B_465, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10752, c_11288])).
% 48.59/37.44  tff(c_11294, plain, (![A_464, B_465]: (k2_relset_1(A_464, B_465, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10925, c_11292])).
% 48.59/37.44  tff(c_11295, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11294, c_90])).
% 48.59/37.44  tff(c_11303, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11295, c_574])).
% 48.59/37.44  tff(c_178942, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_178893, c_11303])).
% 48.59/37.44  tff(c_178948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10752, c_178942])).
% 48.59/37.44  tff(c_178949, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_445])).
% 48.59/37.44  tff(c_179467, plain, (![C_1501, A_1502, B_1503]: (v1_xboole_0(C_1501) | ~m1_subset_1(C_1501, k1_zfmisc_1(k2_zfmisc_1(A_1502, B_1503))) | ~v1_xboole_0(A_1502))), inference(cnfTransformation, [status(thm)], [f_145])).
% 48.59/37.44  tff(c_179479, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_94, c_179467])).
% 48.59/37.44  tff(c_179482, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_179479])).
% 48.59/37.44  tff(c_179490, plain, (k1_xboole_0!='#skF_1'), inference(resolution, [status(thm)], [c_500, c_179482])).
% 48.59/37.44  tff(c_178950, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_445])).
% 48.59/37.44  tff(c_180002, plain, (![A_1532, B_1533, C_1534]: (k1_relset_1(A_1532, B_1533, C_1534)=k1_relat_1(C_1534) | ~m1_subset_1(C_1534, k1_zfmisc_1(k2_zfmisc_1(A_1532, B_1533))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 48.59/37.44  tff(c_180017, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_178950, c_180002])).
% 48.59/37.44  tff(c_181564, plain, (![B_1609, C_1610, A_1611]: (k1_xboole_0=B_1609 | v1_funct_2(C_1610, A_1611, B_1609) | k1_relset_1(A_1611, B_1609, C_1610)!=A_1611 | ~m1_subset_1(C_1610, k1_zfmisc_1(k2_zfmisc_1(A_1611, B_1609))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 48.59/37.44  tff(c_181573, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_178950, c_181564])).
% 48.59/37.44  tff(c_181584, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_180017, c_181573])).
% 48.59/37.44  tff(c_181585, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_178949, c_179490, c_181584])).
% 48.59/37.44  tff(c_181594, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_50, c_181585])).
% 48.59/37.44  tff(c_181597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179258, c_98, c_92, c_179915, c_181594])).
% 48.59/37.44  tff(c_181598, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_179479])).
% 48.59/37.44  tff(c_181614, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_181598, c_174])).
% 48.59/37.44  tff(c_181635, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179277, c_181614])).
% 48.59/37.44  tff(c_181636, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_179267])).
% 48.59/37.44  tff(c_481, plain, (![A_83]: (k1_relat_1(k1_xboole_0)=A_83 | k1_xboole_0!=A_83)), inference(superposition, [status(thm), theory('equality')], [c_463, c_28])).
% 48.59/37.44  tff(c_181824, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_181636, c_181636, c_481])).
% 48.59/37.44  tff(c_181665, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_181636, c_8])).
% 48.59/37.44  tff(c_182542, plain, (![A_1698, B_1699, C_1700]: (k1_relset_1(A_1698, B_1699, C_1700)=k1_relat_1(C_1700) | ~m1_subset_1(C_1700, k1_zfmisc_1(k2_zfmisc_1(A_1698, B_1699))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 48.59/37.44  tff(c_182546, plain, (![A_1698, B_1699]: (k1_relset_1(A_1698, B_1699, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_181665, c_182542])).
% 48.59/37.44  tff(c_182548, plain, (![A_1698, B_1699]: (k1_relset_1(A_1698, B_1699, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181824, c_182546])).
% 48.59/37.44  tff(c_68, plain, (![C_44, B_43]: (v1_funct_2(C_44, k1_xboole_0, B_43) | k1_relset_1(k1_xboole_0, B_43, C_44)!=k1_xboole_0 | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_43))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 48.59/37.44  tff(c_182881, plain, (![C_1740, B_1741]: (v1_funct_2(C_1740, '#skF_3', B_1741) | k1_relset_1('#skF_3', B_1741, C_1740)!='#skF_3' | ~m1_subset_1(C_1740, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1741))))), inference(demodulation, [status(thm), theory('equality')], [c_181636, c_181636, c_181636, c_181636, c_68])).
% 48.59/37.44  tff(c_182885, plain, (![B_1741]: (v1_funct_2('#skF_3', '#skF_3', B_1741) | k1_relset_1('#skF_3', B_1741, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_181665, c_182881])).
% 48.59/37.44  tff(c_182888, plain, (![B_1741]: (v1_funct_2('#skF_3', '#skF_3', B_1741))), inference(demodulation, [status(thm), theory('equality')], [c_182548, c_182885])).
% 48.59/37.44  tff(c_181657, plain, (![A_83]: (v1_xboole_0(A_83) | A_83!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181636, c_500])).
% 48.59/37.44  tff(c_182106, plain, (![A_1654]: (k2_relat_1(A_1654)='#skF_3' | ~v1_xboole_0(A_1654))), inference(demodulation, [status(thm), theory('equality')], [c_181636, c_174])).
% 48.59/37.44  tff(c_182170, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_181657, c_182106])).
% 48.59/37.44  tff(c_182521, plain, (![A_1693, B_1694, C_1695]: (k2_relset_1(A_1693, B_1694, C_1695)=k2_relat_1(C_1695) | ~m1_subset_1(C_1695, k1_zfmisc_1(k2_zfmisc_1(A_1693, B_1694))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 48.59/37.44  tff(c_182525, plain, (![A_1693, B_1694]: (k2_relset_1(A_1693, B_1694, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_181665, c_182521])).
% 48.59/37.44  tff(c_182527, plain, (![A_1693, B_1694]: (k2_relset_1(A_1693, B_1694, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_182170, c_182525])).
% 48.59/37.44  tff(c_182528, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_182527, c_90])).
% 48.59/37.44  tff(c_181637, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_179267])).
% 48.59/37.44  tff(c_181673, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_181636, c_181637])).
% 48.59/37.44  tff(c_506, plain, (![A_84]: (v1_xboole_0(A_84) | k1_xboole_0!=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_478])).
% 48.59/37.44  tff(c_12, plain, (![A_8]: (v1_relat_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 48.59/37.44  tff(c_541, plain, (![A_84]: (v1_relat_1(A_84) | k1_xboole_0!=A_84)), inference(resolution, [status(thm)], [c_506, c_12])).
% 48.59/37.44  tff(c_181755, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181636, c_541])).
% 48.59/37.44  tff(c_181752, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181636, c_496])).
% 48.59/37.44  tff(c_181760, plain, (![A_1621]: (k2_relat_1(A_1621)='#skF_3' | ~v1_xboole_0(A_1621))), inference(demodulation, [status(thm), theory('equality')], [c_181636, c_174])).
% 48.59/37.44  tff(c_181838, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_181657, c_181760])).
% 48.59/37.44  tff(c_182050, plain, (![A_1653]: (k1_relat_1(k2_funct_1(A_1653))=k2_relat_1(A_1653) | ~v2_funct_1(A_1653) | ~v1_funct_1(A_1653) | ~v1_relat_1(A_1653))), inference(cnfTransformation, [status(thm)], [f_128])).
% 48.59/37.44  tff(c_179257, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_178950, c_179246])).
% 48.59/37.44  tff(c_26, plain, (![A_14]: (k1_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 48.59/37.44  tff(c_179276, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0 | k2_funct_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_179257, c_26])).
% 48.59/37.44  tff(c_181831, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_181636, c_181636, c_179276])).
% 48.59/37.44  tff(c_181832, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_181831])).
% 48.59/37.44  tff(c_182059, plain, (k2_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_182050, c_181832])).
% 48.59/37.44  tff(c_182069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181755, c_181752, c_92, c_181838, c_182059])).
% 48.59/37.44  tff(c_182070, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_181831])).
% 48.59/37.44  tff(c_179275, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0 | k2_funct_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_179257, c_24])).
% 48.59/37.44  tff(c_181758, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_181636, c_181636, c_179275])).
% 48.59/37.44  tff(c_181759, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_181758])).
% 48.59/37.44  tff(c_182073, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_182070, c_181759])).
% 48.59/37.44  tff(c_182081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181673, c_182073])).
% 48.59/37.44  tff(c_182082, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_181758])).
% 48.59/37.44  tff(c_182086, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_182082, c_178949])).
% 48.59/37.44  tff(c_182536, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_182528, c_182086])).
% 48.59/37.44  tff(c_182891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182888, c_182536])).
% 48.59/37.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.59/37.44  
% 48.59/37.44  Inference rules
% 48.59/37.44  ----------------------
% 48.59/37.44  #Ref     : 73
% 48.59/37.44  #Sup     : 54938
% 48.59/37.44  #Fact    : 0
% 48.59/37.44  #Define  : 0
% 48.59/37.44  #Split   : 77
% 48.59/37.44  #Chain   : 0
% 48.59/37.44  #Close   : 0
% 48.59/37.44  
% 48.59/37.44  Ordering : KBO
% 48.59/37.44  
% 48.59/37.44  Simplification rules
% 48.59/37.44  ----------------------
% 48.59/37.44  #Subsume      : 36238
% 48.59/37.44  #Demod        : 16990
% 48.59/37.44  #Tautology    : 7679
% 48.59/37.44  #SimpNegUnit  : 1987
% 48.59/37.44  #BackRed      : 1053
% 48.59/37.44  
% 48.59/37.44  #Partial instantiations: 0
% 48.59/37.44  #Strategies tried      : 1
% 48.59/37.44  
% 48.59/37.44  Timing (in seconds)
% 48.59/37.44  ----------------------
% 48.59/37.44  Preprocessing        : 0.45
% 48.59/37.44  Parsing              : 0.25
% 48.59/37.44  CNF conversion       : 0.02
% 48.59/37.44  Main loop            : 36.05
% 48.59/37.44  Inferencing          : 3.18
% 48.59/37.44  Reduction            : 10.84
% 48.59/37.44  Demodulation         : 8.90
% 48.59/37.44  BG Simplification    : 0.44
% 48.59/37.44  Subsumption          : 19.83
% 48.59/37.44  Abstraction          : 0.62
% 48.59/37.44  MUC search           : 0.00
% 48.59/37.44  Cooper               : 0.00
% 48.59/37.44  Total                : 36.57
% 48.59/37.44  Index Insertion      : 0.00
% 48.59/37.44  Index Deletion       : 0.00
% 48.59/37.44  Index Matching       : 0.00
% 48.59/37.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
