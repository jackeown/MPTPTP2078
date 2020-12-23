%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:31 EST 2020

% Result     : Theorem 13.83s
% Output     : CNFRefutation 14.13s
% Verified   : 
% Statistics : Number of formulae       :  460 (2979 expanded)
%              Number of leaves         :   52 ( 950 expanded)
%              Depth                    :   17
%              Number of atoms          :  791 (7389 expanded)
%              Number of equality atoms :  247 (2310 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_201,negated_conjecture,(
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

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_120,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_174,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_184,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_131,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_90,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_250,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_263,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_250])).

tff(c_104,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    ! [A_26] :
      ( v1_funct_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_94,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_156,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_159,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_156])).

tff(c_162,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_159])).

tff(c_226,plain,(
    ! [C_74,A_75,B_76] :
      ( v1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_233,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_226])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_233])).

tff(c_243,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_270,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_281,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_270])).

tff(c_98,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_96,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1396,plain,(
    ! [A_210,B_211,C_212] :
      ( k2_relset_1(A_210,B_211,C_212) = k2_relat_1(C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1403,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_1396])).

tff(c_1412,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1403])).

tff(c_60,plain,(
    ! [A_30] :
      ( k1_relat_1(k2_funct_1(A_30)) = k2_relat_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    ! [A_26] :
      ( v1_relat_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_313,plain,(
    ! [A_90] :
      ( k1_relat_1(A_90) = k1_xboole_0
      | k2_relat_1(A_90) != k1_xboole_0
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_330,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_263,c_313])).

tff(c_334,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_1413,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1412,c_334])).

tff(c_102,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1463,plain,(
    ! [A_213,B_214,C_215] :
      ( k1_relset_1(A_213,B_214,C_215) = k1_relat_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1478,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_1463])).

tff(c_2376,plain,(
    ! [B_297,A_298,C_299] :
      ( k1_xboole_0 = B_297
      | k1_relset_1(A_298,B_297,C_299) = A_298
      | ~ v1_funct_2(C_299,A_298,B_297)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_298,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_2392,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_2376])).

tff(c_2407,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1478,c_2392])).

tff(c_2408,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1413,c_2407])).

tff(c_1324,plain,(
    ! [A_204] :
      ( k2_relat_1(k2_funct_1(A_204)) = k1_relat_1(A_204)
      | ~ v2_funct_1(A_204)
      | ~ v1_funct_1(A_204)
      | ~ v1_relat_1(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,(
    ! [A_24] :
      ( k10_relat_1(A_24,k2_relat_1(A_24)) = k1_relat_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12834,plain,(
    ! [A_616] :
      ( k10_relat_1(k2_funct_1(A_616),k1_relat_1(A_616)) = k1_relat_1(k2_funct_1(A_616))
      | ~ v1_relat_1(k2_funct_1(A_616))
      | ~ v2_funct_1(A_616)
      | ~ v1_funct_1(A_616)
      | ~ v1_relat_1(A_616) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1324,c_40])).

tff(c_12864,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2408,c_12834])).

tff(c_12888,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_104,c_98,c_12864])).

tff(c_12891,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_12888])).

tff(c_12894,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_12891])).

tff(c_12898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_104,c_12894])).

tff(c_12900,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_12888])).

tff(c_244,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_1437,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1412,c_40])).

tff(c_1455,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_1437])).

tff(c_2424,plain,(
    k10_relat_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_1455])).

tff(c_1256,plain,(
    ! [A_199] :
      ( k1_relat_1(k2_funct_1(A_199)) = k2_relat_1(A_199)
      | ~ v2_funct_1(A_199)
      | ~ v1_funct_1(A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    ! [A_23] :
      ( k9_relat_1(A_23,k1_relat_1(A_23)) = k2_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_13705,plain,(
    ! [A_629] :
      ( k9_relat_1(k2_funct_1(A_629),k2_relat_1(A_629)) = k2_relat_1(k2_funct_1(A_629))
      | ~ v1_relat_1(k2_funct_1(A_629))
      | ~ v2_funct_1(A_629)
      | ~ v1_funct_1(A_629)
      | ~ v1_relat_1(A_629) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1256,c_38])).

tff(c_13748,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1412,c_13705])).

tff(c_13777,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_104,c_98,c_12900,c_13748])).

tff(c_56,plain,(
    ! [B_29,A_28] :
      ( k9_relat_1(k2_funct_1(B_29),A_28) = k10_relat_1(B_29,A_28)
      | ~ v2_funct_1(B_29)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_13785,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k10_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13777,c_56])).

tff(c_13792,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_104,c_98,c_2424,c_13785])).

tff(c_1532,plain,(
    ! [A_221] :
      ( m1_subset_1(A_221,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_221),k2_relat_1(A_221))))
      | ~ v1_funct_1(A_221)
      | ~ v1_relat_1(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1577,plain,(
    ! [A_221] :
      ( r1_tarski(A_221,k2_zfmisc_1(k1_relat_1(A_221),k2_relat_1(A_221)))
      | ~ v1_funct_1(A_221)
      | ~ v1_relat_1(A_221) ) ),
    inference(resolution,[status(thm)],[c_1532,c_22])).

tff(c_13922,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13792,c_1577])).

tff(c_14047,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12900,c_244,c_13922])).

tff(c_14527,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k2_relat_1('#skF_4'),'#skF_2'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_14047])).

tff(c_14562,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_104,c_98,c_1412,c_14527])).

tff(c_14564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_14562])).

tff(c_14565,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_14566,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_16439,plain,(
    ! [A_816] :
      ( m1_subset_1(A_816,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_816),k2_relat_1(A_816))))
      | ~ v1_funct_1(A_816)
      | ~ v1_relat_1(A_816) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_16476,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0)))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14566,c_16439])).

tff(c_16496,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_104,c_18,c_14565,c_16476])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_15959,plain,(
    ! [C_766,A_767,B_768] :
      ( v1_xboole_0(C_766)
      | ~ m1_subset_1(C_766,k1_zfmisc_1(k2_zfmisc_1(A_767,B_768)))
      | ~ v1_xboole_0(A_767) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_15972,plain,(
    ! [C_766] :
      ( v1_xboole_0(C_766)
      | ~ m1_subset_1(C_766,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_15959])).

tff(c_15976,plain,(
    ! [C_766] :
      ( v1_xboole_0(C_766)
      | ~ m1_subset_1(C_766,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_15972])).

tff(c_16522,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_16496,c_15976])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_15390,plain,(
    ! [C_717,B_718,A_719] :
      ( ~ v1_xboole_0(C_717)
      | ~ m1_subset_1(B_718,k1_zfmisc_1(C_717))
      | ~ r2_hidden(A_719,B_718) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_15398,plain,(
    ! [B_720,A_721,A_722] :
      ( ~ v1_xboole_0(B_720)
      | ~ r2_hidden(A_721,A_722)
      | ~ r1_tarski(A_722,B_720) ) ),
    inference(resolution,[status(thm)],[c_24,c_15390])).

tff(c_15406,plain,(
    ! [B_726,A_727,B_728] :
      ( ~ v1_xboole_0(B_726)
      | ~ r1_tarski(A_727,B_726)
      | r1_tarski(A_727,B_728) ) ),
    inference(resolution,[status(thm)],[c_6,c_15398])).

tff(c_15420,plain,(
    ! [B_729,B_730] :
      ( ~ v1_xboole_0(B_729)
      | r1_tarski(B_729,B_730) ) ),
    inference(resolution,[status(thm)],[c_14,c_15406])).

tff(c_46,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_117,plain,(
    ! [A_58] : v1_relat_1(k6_relat_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_119,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_117])).

tff(c_36,plain,(
    ! [B_22] : v5_relat_1(k1_xboole_0,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_332,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_119,c_313])).

tff(c_14585,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    ! [A_51] :
      ( v1_funct_2(k1_xboole_0,A_51,k1_xboole_0)
      | k1_xboole_0 = A_51
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_51,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_108,plain,(
    ! [A_51] :
      ( v1_funct_2(k1_xboole_0,A_51,k1_xboole_0)
      | k1_xboole_0 = A_51
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_76])).

tff(c_14848,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_14851,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_14848])).

tff(c_14855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14851])).

tff(c_14857,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_26,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14862,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14857,c_26])).

tff(c_14878,plain,(
    ! [A_673] : ~ r2_hidden(A_673,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14862])).

tff(c_14903,plain,(
    ! [B_675] : r1_tarski(k1_xboole_0,B_675) ),
    inference(resolution,[status(thm)],[c_6,c_14878])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14992,plain,(
    ! [B_684] :
      ( k1_xboole_0 = B_684
      | ~ r1_tarski(B_684,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14903,c_10])).

tff(c_15125,plain,(
    ! [B_695] :
      ( k2_relat_1(B_695) = k1_xboole_0
      | ~ v5_relat_1(B_695,k1_xboole_0)
      | ~ v1_relat_1(B_695) ) ),
    inference(resolution,[status(thm)],[c_32,c_14992])).

tff(c_15136,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_15125])).

tff(c_15145,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_15136])).

tff(c_15147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14585,c_15145])).

tff(c_15149,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_15284,plain,(
    ! [B_711,A_712] :
      ( r1_tarski(k2_relat_1(B_711),A_712)
      | ~ v5_relat_1(B_711,A_712)
      | ~ v1_relat_1(B_711) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_15300,plain,(
    ! [A_712] :
      ( r1_tarski(k1_xboole_0,A_712)
      | ~ v5_relat_1(k1_xboole_0,A_712)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15149,c_15284])).

tff(c_15314,plain,(
    ! [A_713] : r1_tarski(k1_xboole_0,A_713) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_36,c_15300])).

tff(c_15325,plain,(
    ! [A_713] :
      ( k1_xboole_0 = A_713
      | ~ r1_tarski(A_713,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_15314,c_10])).

tff(c_15448,plain,(
    ! [B_729] :
      ( k1_xboole_0 = B_729
      | ~ v1_xboole_0(B_729) ) ),
    inference(resolution,[status(thm)],[c_15420,c_15325])).

tff(c_16544,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16522,c_15448])).

tff(c_16588,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16544,c_16544,c_18])).

tff(c_16583,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16544,c_14566])).

tff(c_16612,plain,(
    ! [A_818,B_819,C_820] :
      ( k2_relset_1(A_818,B_819,C_820) = k2_relat_1(C_820)
      | ~ m1_subset_1(C_820,k1_zfmisc_1(k2_zfmisc_1(A_818,B_819))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_16622,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_16612])).

tff(c_16626,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16622])).

tff(c_16745,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16583,c_16626])).

tff(c_15396,plain,(
    ! [A_719] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_719,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_15390])).

tff(c_15397,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15396])).

tff(c_16787,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16745,c_15397])).

tff(c_17005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16522,c_16588,c_16787])).

tff(c_17007,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_15396])).

tff(c_17379,plain,(
    ! [B_855,A_856,A_857] :
      ( ~ v1_xboole_0(B_855)
      | ~ r2_hidden(A_856,A_857)
      | ~ r1_tarski(A_857,B_855) ) ),
    inference(resolution,[status(thm)],[c_24,c_15390])).

tff(c_17396,plain,(
    ! [B_859,A_860,B_861] :
      ( ~ v1_xboole_0(B_859)
      | ~ r1_tarski(A_860,B_859)
      | r1_tarski(A_860,B_861) ) ),
    inference(resolution,[status(thm)],[c_6,c_17379])).

tff(c_17407,plain,(
    ! [B_862,B_863] :
      ( ~ v1_xboole_0(B_862)
      | r1_tarski(B_862,B_863) ) ),
    inference(resolution,[status(thm)],[c_14,c_17396])).

tff(c_151,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_155,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_100,c_151])).

tff(c_15194,plain,(
    ! [B_699,A_700] :
      ( B_699 = A_700
      | ~ r1_tarski(B_699,A_700)
      | ~ r1_tarski(A_700,B_699) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_15199,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_15194])).

tff(c_15227,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_15199])).

tff(c_17428,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_17407,c_15227])).

tff(c_17446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17007,c_17428])).

tff(c_17447,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15199])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_17466,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_17447,c_16])).

tff(c_17505,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_17466])).

tff(c_17513,plain,(
    ! [C_870,B_871,A_872] :
      ( ~ v1_xboole_0(C_870)
      | ~ m1_subset_1(B_871,k1_zfmisc_1(C_870))
      | ~ r2_hidden(A_872,B_871) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18885,plain,(
    ! [B_979,A_980,A_981] :
      ( ~ v1_xboole_0(B_979)
      | ~ r2_hidden(A_980,A_981)
      | ~ r1_tarski(A_981,B_979) ) ),
    inference(resolution,[status(thm)],[c_24,c_17513])).

tff(c_18899,plain,(
    ! [B_983,A_984,B_985] :
      ( ~ v1_xboole_0(B_983)
      | ~ r1_tarski(A_984,B_983)
      | r1_tarski(A_984,B_985) ) ),
    inference(resolution,[status(thm)],[c_6,c_18885])).

tff(c_18928,plain,(
    ! [B_988,B_989] :
      ( ~ v1_xboole_0(B_988)
      | r1_tarski(B_988,B_989) ) ),
    inference(resolution,[status(thm)],[c_14,c_18899])).

tff(c_17461,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17447,c_100])).

tff(c_17518,plain,(
    ! [A_872] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_872,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_17461,c_17513])).

tff(c_17520,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_17518])).

tff(c_18736,plain,(
    ! [A_974] :
      ( m1_subset_1(A_974,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_974),k2_relat_1(A_974))))
      | ~ v1_funct_1(A_974)
      | ~ v1_relat_1(A_974) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_18777,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0)))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14566,c_18736])).

tff(c_18798,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_104,c_18,c_14565,c_18777])).

tff(c_17932,plain,(
    ! [C_913,A_914,B_915] :
      ( v1_xboole_0(C_913)
      | ~ m1_subset_1(C_913,k1_zfmisc_1(k2_zfmisc_1(A_914,B_915)))
      | ~ v1_xboole_0(A_914) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_17945,plain,(
    ! [C_913] :
      ( v1_xboole_0(C_913)
      | ~ m1_subset_1(C_913,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_17932])).

tff(c_17948,plain,(
    ! [C_913] :
      ( v1_xboole_0(C_913)
      | ~ m1_subset_1(C_913,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_17945])).

tff(c_18808,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18798,c_17948])).

tff(c_18822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17520,c_18808])).

tff(c_18825,plain,(
    ! [A_975] : ~ r2_hidden(A_975,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_17518])).

tff(c_18831,plain,(
    ! [B_976] : r1_tarski('#skF_4',B_976) ),
    inference(resolution,[status(thm)],[c_6,c_18825])).

tff(c_18848,plain,(
    ! [B_976] :
      ( B_976 = '#skF_4'
      | ~ r1_tarski(B_976,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18831,c_10])).

tff(c_18975,plain,(
    ! [B_991] :
      ( B_991 = '#skF_4'
      | ~ v1_xboole_0(B_991) ) ),
    inference(resolution,[status(thm)],[c_18928,c_18848])).

tff(c_18981,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_18975])).

tff(c_18987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17505,c_18981])).

tff(c_18989,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_17466])).

tff(c_19004,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18989,c_18989,c_20])).

tff(c_18988,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17466])).

tff(c_19076,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18989,c_18989,c_18988])).

tff(c_19077,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_19076])).

tff(c_19080,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19077,c_270])).

tff(c_19162,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19004,c_19080])).

tff(c_19166,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_19162])).

tff(c_18995,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18989,c_18989,c_15149])).

tff(c_19920,plain,(
    ! [A_1085] :
      ( k1_relat_1(k2_funct_1(A_1085)) = k2_relat_1(A_1085)
      | ~ v2_funct_1(A_1085)
      | ~ v1_funct_1(A_1085)
      | ~ v1_relat_1(A_1085) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_29584,plain,(
    ! [A_1406] :
      ( k9_relat_1(k2_funct_1(A_1406),k2_relat_1(A_1406)) = k2_relat_1(k2_funct_1(A_1406))
      | ~ v1_relat_1(k2_funct_1(A_1406))
      | ~ v2_funct_1(A_1406)
      | ~ v1_funct_1(A_1406)
      | ~ v1_relat_1(A_1406) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19920,c_38])).

tff(c_29639,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18995,c_29584])).

tff(c_29661,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_104,c_98,c_29639])).

tff(c_29662,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_29661])).

tff(c_29665,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_29662])).

tff(c_29669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_104,c_29665])).

tff(c_29671,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_29661])).

tff(c_19003,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18989,c_18989,c_18])).

tff(c_15148,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_15204,plain,(
    ! [A_701] :
      ( k10_relat_1(A_701,k2_relat_1(A_701)) = k1_relat_1(A_701)
      | ~ v1_relat_1(A_701) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_15213,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_15149,c_15204])).

tff(c_15220,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_15148,c_15213])).

tff(c_18992,plain,(
    k10_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18989,c_18989,c_18989,c_15220])).

tff(c_29670,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_29661])).

tff(c_29773,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k10_relat_1('#skF_4','#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_29670,c_56])).

tff(c_29780,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_104,c_98,c_18992,c_29773])).

tff(c_20932,plain,(
    ! [A_1179] :
      ( m1_subset_1(A_1179,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1179),k2_relat_1(A_1179))))
      | ~ v1_funct_1(A_1179)
      | ~ v1_relat_1(A_1179) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_20983,plain,(
    ! [A_1179] :
      ( r1_tarski(A_1179,k2_zfmisc_1(k1_relat_1(A_1179),k2_relat_1(A_1179)))
      | ~ v1_funct_1(A_1179)
      | ~ v1_relat_1(A_1179) ) ),
    inference(resolution,[status(thm)],[c_20932,c_22])).

tff(c_29894,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29780,c_20983])).

tff(c_30019,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29671,c_244,c_19003,c_29894])).

tff(c_30021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19166,c_30019])).

tff(c_30023,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_19076])).

tff(c_31969,plain,(
    ! [A_1569,B_1570,C_1571] :
      ( k2_relset_1(A_1569,B_1570,C_1571) = k2_relat_1(C_1571)
      | ~ m1_subset_1(C_1571,k1_zfmisc_1(k2_zfmisc_1(A_1569,B_1570))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_32067,plain,(
    ! [B_1578,C_1579] :
      ( k2_relset_1('#skF_4',B_1578,C_1579) = k2_relat_1(C_1579)
      | ~ m1_subset_1(C_1579,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19004,c_31969])).

tff(c_32069,plain,(
    ! [B_1578] : k2_relset_1('#skF_4',B_1578,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_17461,c_32067])).

tff(c_32074,plain,(
    ! [B_1578] : k2_relset_1('#skF_4',B_1578,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18995,c_32069])).

tff(c_30022,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_19076])).

tff(c_30027,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30022,c_96])).

tff(c_32076,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32074,c_30027])).

tff(c_32078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30023,c_32076])).

tff(c_32080,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_39802,plain,(
    ! [C_2201,A_2202,B_2203] :
      ( v1_xboole_0(C_2201)
      | ~ m1_subset_1(C_2201,k1_zfmisc_1(k2_zfmisc_1(A_2202,B_2203)))
      | ~ v1_xboole_0(A_2202) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_39819,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32080,c_39802])).

tff(c_39829,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_39819])).

tff(c_33461,plain,(
    ! [A_1729,B_1730,C_1731] :
      ( k2_relset_1(A_1729,B_1730,C_1731) = k2_relat_1(C_1731)
      | ~ m1_subset_1(C_1731,k1_zfmisc_1(k2_zfmisc_1(A_1729,B_1730))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_33474,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_33461])).

tff(c_33484,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_33474])).

tff(c_32079,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_32173,plain,(
    ! [A_1596] :
      ( k1_relat_1(A_1596) = k1_xboole_0
      | k2_relat_1(A_1596) != k1_xboole_0
      | ~ v1_relat_1(A_1596) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32194,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_263,c_32173])).

tff(c_32198,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32194])).

tff(c_33485,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33484,c_32198])).

tff(c_33345,plain,(
    ! [A_1715,B_1716,C_1717] :
      ( k1_relset_1(A_1715,B_1716,C_1717) = k1_relat_1(C_1717)
      | ~ m1_subset_1(C_1717,k1_zfmisc_1(k2_zfmisc_1(A_1715,B_1716))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_33364,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_33345])).

tff(c_34259,plain,(
    ! [B_1788,A_1789,C_1790] :
      ( k1_xboole_0 = B_1788
      | k1_relset_1(A_1789,B_1788,C_1790) = A_1789
      | ~ v1_funct_2(C_1790,A_1789,B_1788)
      | ~ m1_subset_1(C_1790,k1_zfmisc_1(k2_zfmisc_1(A_1789,B_1788))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_34278,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_34259])).

tff(c_34295,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_33364,c_34278])).

tff(c_34296,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_33485,c_34295])).

tff(c_32641,plain,(
    ! [A_1646] :
      ( k2_relat_1(A_1646) = k1_xboole_0
      | k1_relat_1(A_1646) != k1_xboole_0
      | ~ v1_relat_1(A_1646) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32650,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_263,c_32641])).

tff(c_32664,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_32198,c_32650])).

tff(c_34313,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34296,c_32664])).

tff(c_33362,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32080,c_33345])).

tff(c_34359,plain,(
    ! [B_1791,C_1792,A_1793] :
      ( k1_xboole_0 = B_1791
      | v1_funct_2(C_1792,A_1793,B_1791)
      | k1_relset_1(A_1793,B_1791,C_1792) != A_1793
      | ~ m1_subset_1(C_1792,k1_zfmisc_1(k2_zfmisc_1(A_1793,B_1791))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_34368,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_32080,c_34359])).

tff(c_34384,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33362,c_34368])).

tff(c_34385,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_32079,c_34313,c_34384])).

tff(c_34394,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_34385])).

tff(c_34397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_104,c_98,c_33484,c_34394])).

tff(c_34399,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32194])).

tff(c_36426,plain,(
    ! [C_1970,A_1971,B_1972] :
      ( v1_xboole_0(C_1970)
      | ~ m1_subset_1(C_1970,k1_zfmisc_1(k2_zfmisc_1(A_1971,B_1972)))
      | ~ v1_xboole_0(A_1971) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36443,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32080,c_36426])).

tff(c_36449,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36443])).

tff(c_36837,plain,(
    ! [A_2003,B_2004,C_2005] :
      ( k2_relset_1(A_2003,B_2004,C_2005) = k2_relat_1(C_2005)
      | ~ m1_subset_1(C_2005,k1_zfmisc_1(k2_zfmisc_1(A_2003,B_2004))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36847,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_36837])).

tff(c_36858,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_34399,c_36847])).

tff(c_36906,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36858,c_8])).

tff(c_36908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36449,c_36906])).

tff(c_36910,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_36443])).

tff(c_36393,plain,(
    ! [C_1961,B_1962,A_1963] :
      ( ~ v1_xboole_0(C_1961)
      | ~ m1_subset_1(B_1962,k1_zfmisc_1(C_1961))
      | ~ r2_hidden(A_1963,B_1962) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36404,plain,(
    ! [B_1964,A_1965,A_1966] :
      ( ~ v1_xboole_0(B_1964)
      | ~ r2_hidden(A_1965,A_1966)
      | ~ r1_tarski(A_1966,B_1964) ) ),
    inference(resolution,[status(thm)],[c_24,c_36393])).

tff(c_36409,plain,(
    ! [B_1967,A_1968,B_1969] :
      ( ~ v1_xboole_0(B_1967)
      | ~ r1_tarski(A_1968,B_1967)
      | r1_tarski(A_1968,B_1969) ) ),
    inference(resolution,[status(thm)],[c_6,c_36404])).

tff(c_36948,plain,(
    ! [B_2007,B_2008] :
      ( ~ v1_xboole_0(B_2007)
      | r1_tarski(B_2007,B_2008) ) ),
    inference(resolution,[status(thm)],[c_14,c_36409])).

tff(c_32196,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_119,c_32173])).

tff(c_34428,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32196])).

tff(c_35118,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_35121,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_35118])).

tff(c_35125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_35121])).

tff(c_35127,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_35129,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_35127,c_26])).

tff(c_35143,plain,(
    ! [A_1864] : ~ r2_hidden(A_1864,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_35129])).

tff(c_35177,plain,(
    ! [B_1868] : r1_tarski(k1_xboole_0,B_1868) ),
    inference(resolution,[status(thm)],[c_6,c_35143])).

tff(c_35204,plain,(
    ! [B_1872] :
      ( k1_xboole_0 = B_1872
      | ~ r1_tarski(B_1872,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_35177,c_10])).

tff(c_35468,plain,(
    ! [B_1891] :
      ( k2_relat_1(B_1891) = k1_xboole_0
      | ~ v5_relat_1(B_1891,k1_xboole_0)
      | ~ v1_relat_1(B_1891) ) ),
    inference(resolution,[status(thm)],[c_32,c_35204])).

tff(c_35483,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_35468])).

tff(c_35495,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_35483])).

tff(c_35497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34428,c_35495])).

tff(c_35499,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32196])).

tff(c_36243,plain,(
    ! [B_1949,A_1950] :
      ( r1_tarski(k2_relat_1(B_1949),A_1950)
      | ~ v5_relat_1(B_1949,A_1950)
      | ~ v1_relat_1(B_1949) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36265,plain,(
    ! [A_1950] :
      ( r1_tarski(k1_xboole_0,A_1950)
      | ~ v5_relat_1(k1_xboole_0,A_1950)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35499,c_36243])).

tff(c_36281,plain,(
    ! [A_1951] : r1_tarski(k1_xboole_0,A_1951) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_36,c_36265])).

tff(c_36292,plain,(
    ! [A_1951] :
      ( k1_xboole_0 = A_1951
      | ~ r1_tarski(A_1951,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36281,c_10])).

tff(c_37322,plain,(
    ! [B_2022] :
      ( k1_xboole_0 = B_2022
      | ~ v1_xboole_0(B_2022) ) ),
    inference(resolution,[status(thm)],[c_36948,c_36292])).

tff(c_37333,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36910,c_37322])).

tff(c_37367,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37333,c_37333,c_18])).

tff(c_36402,plain,(
    ! [A_1963] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_1963,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_36393])).

tff(c_36403,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36402])).

tff(c_37641,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37367,c_36403])).

tff(c_37647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36910,c_37641])).

tff(c_37649,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_36402])).

tff(c_38179,plain,(
    ! [B_2058,A_2059,A_2060] :
      ( ~ v1_xboole_0(B_2058)
      | ~ r2_hidden(A_2059,A_2060)
      | ~ r1_tarski(A_2060,B_2058) ) ),
    inference(resolution,[status(thm)],[c_24,c_36393])).

tff(c_38183,plain,(
    ! [B_2061,A_2062,B_2063] :
      ( ~ v1_xboole_0(B_2061)
      | ~ r1_tarski(A_2062,B_2061)
      | r1_tarski(A_2062,B_2063) ) ),
    inference(resolution,[status(thm)],[c_6,c_38179])).

tff(c_38197,plain,(
    ! [B_2064,B_2065] :
      ( ~ v1_xboole_0(B_2064)
      | r1_tarski(B_2064,B_2065) ) ),
    inference(resolution,[status(thm)],[c_14,c_38183])).

tff(c_32132,plain,(
    ! [B_1587,A_1588] :
      ( B_1587 = A_1588
      | ~ r1_tarski(B_1587,A_1588)
      | ~ r1_tarski(A_1588,B_1587) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32140,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_32132])).

tff(c_34418,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32140])).

tff(c_38221,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38197,c_34418])).

tff(c_38237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37649,c_38221])).

tff(c_38238,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32140])).

tff(c_38268,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38238,c_100])).

tff(c_41208,plain,(
    ! [A_2303,B_2304,C_2305] :
      ( k2_relset_1(A_2303,B_2304,C_2305) = k2_relat_1(C_2305)
      | ~ m1_subset_1(C_2305,k1_zfmisc_1(k2_zfmisc_1(A_2303,B_2304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_41261,plain,(
    ! [C_2309] :
      ( k2_relset_1('#skF_2','#skF_3',C_2309) = k2_relat_1(C_2309)
      | ~ m1_subset_1(C_2309,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38238,c_41208])).

tff(c_41264,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38268,c_41261])).

tff(c_41270,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_34399,c_41264])).

tff(c_41345,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41270,c_8])).

tff(c_41347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39829,c_41345])).

tff(c_41349,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_39819])).

tff(c_39730,plain,(
    ! [C_2189,B_2190,A_2191] :
      ( ~ v1_xboole_0(C_2189)
      | ~ m1_subset_1(B_2190,k1_zfmisc_1(C_2189))
      | ~ r2_hidden(A_2191,B_2190) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_39742,plain,(
    ! [B_2192,A_2193,A_2194] :
      ( ~ v1_xboole_0(B_2192)
      | ~ r2_hidden(A_2193,A_2194)
      | ~ r1_tarski(A_2194,B_2192) ) ),
    inference(resolution,[status(thm)],[c_24,c_39730])).

tff(c_39746,plain,(
    ! [B_2195,A_2196,B_2197] :
      ( ~ v1_xboole_0(B_2195)
      | ~ r1_tarski(A_2196,B_2195)
      | r1_tarski(A_2196,B_2197) ) ),
    inference(resolution,[status(thm)],[c_6,c_39742])).

tff(c_39760,plain,(
    ! [B_2198,B_2199] :
      ( ~ v1_xboole_0(B_2198)
      | r1_tarski(B_2198,B_2199) ) ),
    inference(resolution,[status(thm)],[c_14,c_39746])).

tff(c_38306,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32196])).

tff(c_38477,plain,(
    ! [C_2084,B_2085,A_2086] :
      ( ~ v1_xboole_0(C_2084)
      | ~ m1_subset_1(B_2085,k1_zfmisc_1(C_2084))
      | ~ r2_hidden(A_2086,B_2085) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38489,plain,(
    ! [B_2087,A_2088,A_2089] :
      ( ~ v1_xboole_0(B_2087)
      | ~ r2_hidden(A_2088,A_2089)
      | ~ r1_tarski(A_2089,B_2087) ) ),
    inference(resolution,[status(thm)],[c_24,c_38477])).

tff(c_38493,plain,(
    ! [B_2090,A_2091,B_2092] :
      ( ~ v1_xboole_0(B_2090)
      | ~ r1_tarski(A_2091,B_2090)
      | r1_tarski(A_2091,B_2092) ) ),
    inference(resolution,[status(thm)],[c_6,c_38489])).

tff(c_38503,plain,(
    ! [B_2093,B_2094] :
      ( ~ v1_xboole_0(B_2093)
      | r1_tarski(B_2093,B_2094) ) ),
    inference(resolution,[status(thm)],[c_14,c_38493])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( v5_relat_1(B_20,A_19)
      | ~ r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38597,plain,(
    ! [B_2103,B_2104] :
      ( v5_relat_1(B_2103,B_2104)
      | ~ v1_relat_1(B_2103)
      | ~ v1_xboole_0(k2_relat_1(B_2103)) ) ),
    inference(resolution,[status(thm)],[c_38503,c_30])).

tff(c_38601,plain,(
    ! [B_2104] :
      ( v5_relat_1('#skF_4',B_2104)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34399,c_38597])).

tff(c_38605,plain,(
    ! [B_2104] : v5_relat_1('#skF_4',B_2104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_263,c_38601])).

tff(c_38371,plain,(
    ! [B_2076,A_2077] :
      ( r1_tarski(k2_relat_1(B_2076),A_2077)
      | ~ v5_relat_1(B_2076,A_2077)
      | ~ v1_relat_1(B_2076) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38394,plain,(
    ! [A_2077] :
      ( r1_tarski(k1_xboole_0,A_2077)
      | ~ v5_relat_1('#skF_4',A_2077)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34399,c_38371])).

tff(c_38403,plain,(
    ! [A_2077] :
      ( r1_tarski(k1_xboole_0,A_2077)
      | ~ v5_relat_1('#skF_4',A_2077) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_38394])).

tff(c_38632,plain,(
    ! [A_2109] : r1_tarski(k1_xboole_0,A_2109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38605,c_38403])).

tff(c_38664,plain,(
    ! [A_2110] :
      ( k1_xboole_0 = A_2110
      | ~ r1_tarski(A_2110,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38632,c_10])).

tff(c_38873,plain,(
    ! [B_2121] :
      ( k2_relat_1(B_2121) = k1_xboole_0
      | ~ v5_relat_1(B_2121,k1_xboole_0)
      | ~ v1_relat_1(B_2121) ) ),
    inference(resolution,[status(thm)],[c_32,c_38664])).

tff(c_38885,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_38873])).

tff(c_38894,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_38885])).

tff(c_38896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38306,c_38894])).

tff(c_38898,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32196])).

tff(c_39605,plain,(
    ! [B_2182,A_2183] :
      ( r1_tarski(k2_relat_1(B_2182),A_2183)
      | ~ v5_relat_1(B_2182,A_2183)
      | ~ v1_relat_1(B_2182) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_39631,plain,(
    ! [A_2183] :
      ( r1_tarski(k1_xboole_0,A_2183)
      | ~ v5_relat_1(k1_xboole_0,A_2183)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38898,c_39605])).

tff(c_39652,plain,(
    ! [A_2184] : r1_tarski(k1_xboole_0,A_2184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_36,c_39631])).

tff(c_39669,plain,(
    ! [A_2184] :
      ( k1_xboole_0 = A_2184
      | ~ r1_tarski(A_2184,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_39652,c_10])).

tff(c_39790,plain,(
    ! [B_2198] :
      ( k1_xboole_0 = B_2198
      | ~ v1_xboole_0(B_2198) ) ),
    inference(resolution,[status(thm)],[c_39760,c_39669])).

tff(c_41356,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_41349,c_39790])).

tff(c_41392,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41356,c_41356,c_20])).

tff(c_39738,plain,(
    ! [A_2191] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_2191,k2_funct_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_32080,c_39730])).

tff(c_39741,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_39738])).

tff(c_41546,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41392,c_39741])).

tff(c_41552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41349,c_41546])).

tff(c_41554,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_39738])).

tff(c_41696,plain,(
    ! [B_2319,A_2320,A_2321] :
      ( ~ v1_xboole_0(B_2319)
      | ~ r2_hidden(A_2320,A_2321)
      | ~ r1_tarski(A_2321,B_2319) ) ),
    inference(resolution,[status(thm)],[c_24,c_39730])).

tff(c_41700,plain,(
    ! [B_2322,A_2323,B_2324] :
      ( ~ v1_xboole_0(B_2322)
      | ~ r1_tarski(A_2323,B_2322)
      | r1_tarski(A_2323,B_2324) ) ),
    inference(resolution,[status(thm)],[c_6,c_41696])).

tff(c_41711,plain,(
    ! [B_2325,B_2326] :
      ( ~ v1_xboole_0(B_2325)
      | r1_tarski(B_2325,B_2326) ) ),
    inference(resolution,[status(thm)],[c_14,c_41700])).

tff(c_41587,plain,(
    ! [A_2315] : ~ r2_hidden(A_2315,k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_39738])).

tff(c_41594,plain,(
    ! [B_2316] : r1_tarski(k2_funct_1('#skF_4'),B_2316) ),
    inference(resolution,[status(thm)],[c_6,c_41587])).

tff(c_41613,plain,(
    k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41594,c_39669])).

tff(c_32095,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32080,c_22])).

tff(c_32139,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4')
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32095,c_32132])).

tff(c_39678,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_32139])).

tff(c_41623,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41613,c_39678])).

tff(c_41716,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_41711,c_41623])).

tff(c_41743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41554,c_41716])).

tff(c_41744,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_32139])).

tff(c_41870,plain,(
    ! [C_2338,A_2339,B_2340] :
      ( v1_xboole_0(C_2338)
      | ~ m1_subset_1(C_2338,k1_zfmisc_1(k2_zfmisc_1(A_2339,B_2340)))
      | ~ v1_xboole_0(A_2339) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_41873,plain,(
    ! [C_2338] :
      ( v1_xboole_0(C_2338)
      | ~ m1_subset_1(C_2338,k1_zfmisc_1(k2_funct_1('#skF_4')))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41744,c_41870])).

tff(c_42096,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_41873])).

tff(c_42879,plain,(
    ! [A_2412,B_2413,C_2414] :
      ( k2_relset_1(A_2412,B_2413,C_2414) = k2_relat_1(C_2414)
      | ~ m1_subset_1(C_2414,k1_zfmisc_1(k2_zfmisc_1(A_2412,B_2413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42962,plain,(
    ! [C_2421] :
      ( k2_relset_1('#skF_2','#skF_3',C_2421) = k2_relat_1(C_2421)
      | ~ m1_subset_1(C_2421,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38238,c_42879])).

tff(c_42965,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38268,c_42962])).

tff(c_42971,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_34399,c_42965])).

tff(c_43033,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42971,c_8])).

tff(c_43035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42096,c_43033])).

tff(c_43037,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_41873])).

tff(c_41763,plain,(
    ! [C_2327,B_2328,A_2329] :
      ( ~ v1_xboole_0(C_2327)
      | ~ m1_subset_1(B_2328,k1_zfmisc_1(C_2327))
      | ~ r2_hidden(A_2329,B_2328) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_41866,plain,(
    ! [B_2335,A_2336,A_2337] :
      ( ~ v1_xboole_0(B_2335)
      | ~ r2_hidden(A_2336,A_2337)
      | ~ r1_tarski(A_2337,B_2335) ) ),
    inference(resolution,[status(thm)],[c_24,c_41763])).

tff(c_41920,plain,(
    ! [B_2343,A_2344,B_2345] :
      ( ~ v1_xboole_0(B_2343)
      | ~ r1_tarski(A_2344,B_2343)
      | r1_tarski(A_2344,B_2345) ) ),
    inference(resolution,[status(thm)],[c_6,c_41866])).

tff(c_41931,plain,(
    ! [B_2346,B_2347] :
      ( ~ v1_xboole_0(B_2346)
      | r1_tarski(B_2346,B_2347) ) ),
    inference(resolution,[status(thm)],[c_14,c_41920])).

tff(c_41967,plain,(
    ! [B_2346] :
      ( k1_xboole_0 = B_2346
      | ~ v1_xboole_0(B_2346) ) ),
    inference(resolution,[status(thm)],[c_41931,c_39669])).

tff(c_43044,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_43037,c_41967])).

tff(c_41752,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k2_funct_1('#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_41744,c_16])).

tff(c_41818,plain,(
    k2_funct_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_41752])).

tff(c_43063,plain,(
    k2_funct_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43044,c_41818])).

tff(c_43088,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43044,c_43044,c_20])).

tff(c_43372,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43088,c_41744])).

tff(c_43374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43063,c_43372])).

tff(c_43375,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_41752])).

tff(c_43449,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_43375])).

tff(c_38273,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_38238,c_16])).

tff(c_38925,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38273])).

tff(c_43463,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43449,c_38925])).

tff(c_43692,plain,(
    ! [B_2443] : k2_zfmisc_1('#skF_2',B_2443) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43449,c_43449,c_20])).

tff(c_43702,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_43692,c_38238])).

tff(c_43721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43463,c_43702])).

tff(c_43722,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_43375])).

tff(c_43757,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43722,c_38925])).

tff(c_44012,plain,(
    ! [A_2457] : k2_zfmisc_1(A_2457,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43722,c_43722,c_18])).

tff(c_44025,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_44012,c_38238])).

tff(c_44042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43757,c_44025])).

tff(c_44044,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38273])).

tff(c_34398,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32194])).

tff(c_44052,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44044,c_34398])).

tff(c_44058,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44044,c_44044,c_20])).

tff(c_46057,plain,(
    ! [A_2606,B_2607,C_2608] :
      ( k1_relset_1(A_2606,B_2607,C_2608) = k1_relat_1(C_2608)
      | ~ m1_subset_1(C_2608,k1_zfmisc_1(k2_zfmisc_1(A_2606,B_2607))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46307,plain,(
    ! [B_2629,C_2630] :
      ( k1_relset_1('#skF_4',B_2629,C_2630) = k1_relat_1(C_2630)
      | ~ m1_subset_1(C_2630,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44058,c_46057])).

tff(c_46309,plain,(
    ! [B_2629] : k1_relset_1('#skF_4',B_2629,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38268,c_46307])).

tff(c_46314,plain,(
    ! [B_2629] : k1_relset_1('#skF_4',B_2629,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44052,c_46309])).

tff(c_80,plain,(
    ! [C_53,B_52] :
      ( v1_funct_2(C_53,k1_xboole_0,B_52)
      | k1_relset_1(k1_xboole_0,B_52,C_53) != k1_xboole_0
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_105,plain,(
    ! [C_53,B_52] :
      ( v1_funct_2(C_53,k1_xboole_0,B_52)
      | k1_relset_1(k1_xboole_0,B_52,C_53) != k1_xboole_0
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_80])).

tff(c_46601,plain,(
    ! [C_2642,B_2643] :
      ( v1_funct_2(C_2642,'#skF_4',B_2643)
      | k1_relset_1('#skF_4',B_2643,C_2642) != '#skF_4'
      | ~ m1_subset_1(C_2642,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44044,c_44044,c_44044,c_44044,c_105])).

tff(c_46603,plain,(
    ! [B_2643] :
      ( v1_funct_2('#skF_4','#skF_4',B_2643)
      | k1_relset_1('#skF_4',B_2643,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_38268,c_46601])).

tff(c_46609,plain,(
    ! [B_2643] : v1_funct_2('#skF_4','#skF_4',B_2643) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46314,c_46603])).

tff(c_44063,plain,(
    ! [B_22] : v5_relat_1('#skF_4',B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44044,c_36])).

tff(c_44051,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44044,c_34399])).

tff(c_44093,plain,(
    ! [B_2460,A_2461] :
      ( r1_tarski(k2_relat_1(B_2460),A_2461)
      | ~ v5_relat_1(B_2460,A_2461)
      | ~ v1_relat_1(B_2460) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44106,plain,(
    ! [A_2461] :
      ( r1_tarski('#skF_4',A_2461)
      | ~ v5_relat_1('#skF_4',A_2461)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44051,c_44093])).

tff(c_44111,plain,(
    ! [A_2461] : r1_tarski('#skF_4',A_2461) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_44063,c_44106])).

tff(c_44043,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38273])).

tff(c_44149,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44044,c_44044,c_44043])).

tff(c_44150,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_44149])).

tff(c_44153,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44150,c_32080])).

tff(c_44269,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44058,c_44153])).

tff(c_44283,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_44269,c_22])).

tff(c_44297,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44283,c_10])).

tff(c_44303,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44111,c_44297])).

tff(c_44154,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44150,c_32079])).

tff(c_44307,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44303,c_44154])).

tff(c_46614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46609,c_44307])).

tff(c_46616,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44149])).

tff(c_46938,plain,(
    ! [A_2671] :
      ( v1_funct_2('#skF_4',A_2671,'#skF_4')
      | A_2671 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38268,c_44044,c_44044,c_44044,c_44044,c_44044,c_108])).

tff(c_44057,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44044,c_44044,c_18])).

tff(c_46615,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44149])).

tff(c_46618,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46615,c_32095])).

tff(c_46748,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44057,c_46618])).

tff(c_46756,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46748,c_10])).

tff(c_46762,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44111,c_46756])).

tff(c_46620,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46615,c_32079])).

tff(c_46764,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46762,c_46620])).

tff(c_46941,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46938,c_46764])).

tff(c_46945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46616,c_46941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n014.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 11:00:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.83/5.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.83/6.02  
% 13.83/6.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.13/6.02  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 14.13/6.02  
% 14.13/6.02  %Foreground sorts:
% 14.13/6.02  
% 14.13/6.02  
% 14.13/6.02  %Background operators:
% 14.13/6.02  
% 14.13/6.02  
% 14.13/6.02  %Foreground operators:
% 14.13/6.02  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.13/6.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.13/6.02  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.13/6.02  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.13/6.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.13/6.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.13/6.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.13/6.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.13/6.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.13/6.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.13/6.02  tff('#skF_2', type, '#skF_2': $i).
% 14.13/6.02  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.13/6.02  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 14.13/6.02  tff('#skF_3', type, '#skF_3': $i).
% 14.13/6.02  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.13/6.02  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.13/6.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.13/6.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.13/6.02  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 14.13/6.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.13/6.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.13/6.02  tff('#skF_4', type, '#skF_4': $i).
% 14.13/6.02  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 14.13/6.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.13/6.02  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.13/6.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.13/6.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.13/6.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.13/6.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.13/6.02  
% 14.13/6.06  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.13/6.06  tff(f_201, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 14.13/6.06  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.13/6.06  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.13/6.06  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 14.13/6.06  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.13/6.06  tff(f_120, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 14.13/6.06  tff(f_89, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 14.13/6.06  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.13/6.06  tff(f_174, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 14.13/6.06  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 14.13/6.06  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 14.13/6.06  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 14.13/6.06  tff(f_184, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 14.13/6.06  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.13/6.06  tff(f_131, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 14.13/6.06  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.13/6.06  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 14.13/6.06  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 14.13/6.06  tff(f_90, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 14.13/6.06  tff(f_102, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 14.13/6.06  tff(f_75, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 14.13/6.06  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 14.13/6.06  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.13/6.06  tff(c_100, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 14.13/6.06  tff(c_250, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 14.13/6.06  tff(c_263, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_250])).
% 14.13/6.06  tff(c_104, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 14.13/6.06  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.13/6.06  tff(c_48, plain, (![A_26]: (v1_funct_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.13/6.06  tff(c_94, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 14.13/6.06  tff(c_156, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_94])).
% 14.13/6.06  tff(c_159, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_156])).
% 14.13/6.06  tff(c_162, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_159])).
% 14.13/6.06  tff(c_226, plain, (![C_74, A_75, B_76]: (v1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 14.13/6.06  tff(c_233, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_226])).
% 14.13/6.06  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_233])).
% 14.13/6.06  tff(c_243, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_94])).
% 14.13/6.06  tff(c_270, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_243])).
% 14.13/6.06  tff(c_281, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_270])).
% 14.13/6.06  tff(c_98, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 14.13/6.06  tff(c_96, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_201])).
% 14.13/6.06  tff(c_1396, plain, (![A_210, B_211, C_212]: (k2_relset_1(A_210, B_211, C_212)=k2_relat_1(C_212) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.13/6.06  tff(c_1403, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_1396])).
% 14.13/6.06  tff(c_1412, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1403])).
% 14.13/6.06  tff(c_60, plain, (![A_30]: (k1_relat_1(k2_funct_1(A_30))=k2_relat_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.13/6.06  tff(c_50, plain, (![A_26]: (v1_relat_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.13/6.06  tff(c_313, plain, (![A_90]: (k1_relat_1(A_90)=k1_xboole_0 | k2_relat_1(A_90)!=k1_xboole_0 | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.13/6.06  tff(c_330, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_263, c_313])).
% 14.13/6.06  tff(c_334, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_330])).
% 14.13/6.06  tff(c_1413, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1412, c_334])).
% 14.13/6.06  tff(c_102, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 14.13/6.06  tff(c_1463, plain, (![A_213, B_214, C_215]: (k1_relset_1(A_213, B_214, C_215)=k1_relat_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.13/6.06  tff(c_1478, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_1463])).
% 14.13/6.06  tff(c_2376, plain, (![B_297, A_298, C_299]: (k1_xboole_0=B_297 | k1_relset_1(A_298, B_297, C_299)=A_298 | ~v1_funct_2(C_299, A_298, B_297) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_298, B_297))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.13/6.06  tff(c_2392, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_100, c_2376])).
% 14.13/6.06  tff(c_2407, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1478, c_2392])).
% 14.13/6.06  tff(c_2408, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1413, c_2407])).
% 14.13/6.06  tff(c_1324, plain, (![A_204]: (k2_relat_1(k2_funct_1(A_204))=k1_relat_1(A_204) | ~v2_funct_1(A_204) | ~v1_funct_1(A_204) | ~v1_relat_1(A_204))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.13/6.06  tff(c_40, plain, (![A_24]: (k10_relat_1(A_24, k2_relat_1(A_24))=k1_relat_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.13/6.06  tff(c_12834, plain, (![A_616]: (k10_relat_1(k2_funct_1(A_616), k1_relat_1(A_616))=k1_relat_1(k2_funct_1(A_616)) | ~v1_relat_1(k2_funct_1(A_616)) | ~v2_funct_1(A_616) | ~v1_funct_1(A_616) | ~v1_relat_1(A_616))), inference(superposition, [status(thm), theory('equality')], [c_1324, c_40])).
% 14.13/6.06  tff(c_12864, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2408, c_12834])).
% 14.13/6.06  tff(c_12888, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_104, c_98, c_12864])).
% 14.13/6.06  tff(c_12891, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_12888])).
% 14.13/6.06  tff(c_12894, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_12891])).
% 14.13/6.06  tff(c_12898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_263, c_104, c_12894])).
% 14.13/6.06  tff(c_12900, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_12888])).
% 14.13/6.06  tff(c_244, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_94])).
% 14.13/6.06  tff(c_1437, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1412, c_40])).
% 14.13/6.06  tff(c_1455, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_1437])).
% 14.13/6.06  tff(c_2424, plain, (k10_relat_1('#skF_4', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_1455])).
% 14.13/6.06  tff(c_1256, plain, (![A_199]: (k1_relat_1(k2_funct_1(A_199))=k2_relat_1(A_199) | ~v2_funct_1(A_199) | ~v1_funct_1(A_199) | ~v1_relat_1(A_199))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.13/6.06  tff(c_38, plain, (![A_23]: (k9_relat_1(A_23, k1_relat_1(A_23))=k2_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.13/6.06  tff(c_13705, plain, (![A_629]: (k9_relat_1(k2_funct_1(A_629), k2_relat_1(A_629))=k2_relat_1(k2_funct_1(A_629)) | ~v1_relat_1(k2_funct_1(A_629)) | ~v2_funct_1(A_629) | ~v1_funct_1(A_629) | ~v1_relat_1(A_629))), inference(superposition, [status(thm), theory('equality')], [c_1256, c_38])).
% 14.13/6.06  tff(c_13748, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1412, c_13705])).
% 14.13/6.06  tff(c_13777, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_104, c_98, c_12900, c_13748])).
% 14.13/6.06  tff(c_56, plain, (![B_29, A_28]: (k9_relat_1(k2_funct_1(B_29), A_28)=k10_relat_1(B_29, A_28) | ~v2_funct_1(B_29) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.13/6.06  tff(c_13785, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k10_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13777, c_56])).
% 14.13/6.06  tff(c_13792, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_104, c_98, c_2424, c_13785])).
% 14.13/6.06  tff(c_1532, plain, (![A_221]: (m1_subset_1(A_221, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_221), k2_relat_1(A_221)))) | ~v1_funct_1(A_221) | ~v1_relat_1(A_221))), inference(cnfTransformation, [status(thm)], [f_184])).
% 14.13/6.06  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.13/6.06  tff(c_1577, plain, (![A_221]: (r1_tarski(A_221, k2_zfmisc_1(k1_relat_1(A_221), k2_relat_1(A_221))) | ~v1_funct_1(A_221) | ~v1_relat_1(A_221))), inference(resolution, [status(thm)], [c_1532, c_22])).
% 14.13/6.06  tff(c_13922, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13792, c_1577])).
% 14.13/6.06  tff(c_14047, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12900, c_244, c_13922])).
% 14.13/6.06  tff(c_14527, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k2_relat_1('#skF_4'), '#skF_2')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_60, c_14047])).
% 14.13/6.06  tff(c_14562, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_104, c_98, c_1412, c_14527])).
% 14.13/6.06  tff(c_14564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_14562])).
% 14.13/6.06  tff(c_14565, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_330])).
% 14.13/6.06  tff(c_14566, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_330])).
% 14.13/6.06  tff(c_16439, plain, (![A_816]: (m1_subset_1(A_816, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_816), k2_relat_1(A_816)))) | ~v1_funct_1(A_816) | ~v1_relat_1(A_816))), inference(cnfTransformation, [status(thm)], [f_184])).
% 14.13/6.06  tff(c_16476, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14566, c_16439])).
% 14.13/6.06  tff(c_16496, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_104, c_18, c_14565, c_16476])).
% 14.13/6.06  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.13/6.06  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.13/6.06  tff(c_15959, plain, (![C_766, A_767, B_768]: (v1_xboole_0(C_766) | ~m1_subset_1(C_766, k1_zfmisc_1(k2_zfmisc_1(A_767, B_768))) | ~v1_xboole_0(A_767))), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.13/6.06  tff(c_15972, plain, (![C_766]: (v1_xboole_0(C_766) | ~m1_subset_1(C_766, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_15959])).
% 14.13/6.06  tff(c_15976, plain, (![C_766]: (v1_xboole_0(C_766) | ~m1_subset_1(C_766, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_15972])).
% 14.13/6.06  tff(c_16522, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_16496, c_15976])).
% 14.13/6.06  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.13/6.06  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.13/6.06  tff(c_15390, plain, (![C_717, B_718, A_719]: (~v1_xboole_0(C_717) | ~m1_subset_1(B_718, k1_zfmisc_1(C_717)) | ~r2_hidden(A_719, B_718))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.13/6.06  tff(c_15398, plain, (![B_720, A_721, A_722]: (~v1_xboole_0(B_720) | ~r2_hidden(A_721, A_722) | ~r1_tarski(A_722, B_720))), inference(resolution, [status(thm)], [c_24, c_15390])).
% 14.13/6.06  tff(c_15406, plain, (![B_726, A_727, B_728]: (~v1_xboole_0(B_726) | ~r1_tarski(A_727, B_726) | r1_tarski(A_727, B_728))), inference(resolution, [status(thm)], [c_6, c_15398])).
% 14.13/6.06  tff(c_15420, plain, (![B_729, B_730]: (~v1_xboole_0(B_729) | r1_tarski(B_729, B_730))), inference(resolution, [status(thm)], [c_14, c_15406])).
% 14.13/6.06  tff(c_46, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.13/6.06  tff(c_117, plain, (![A_58]: (v1_relat_1(k6_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 14.13/6.06  tff(c_119, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_117])).
% 14.13/6.06  tff(c_36, plain, (![B_22]: (v5_relat_1(k1_xboole_0, B_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.13/6.06  tff(c_332, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_119, c_313])).
% 14.13/6.06  tff(c_14585, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_332])).
% 14.13/6.06  tff(c_32, plain, (![B_20, A_19]: (r1_tarski(k2_relat_1(B_20), A_19) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.13/6.06  tff(c_76, plain, (![A_51]: (v1_funct_2(k1_xboole_0, A_51, k1_xboole_0) | k1_xboole_0=A_51 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_51, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.13/6.06  tff(c_108, plain, (![A_51]: (v1_funct_2(k1_xboole_0, A_51, k1_xboole_0) | k1_xboole_0=A_51 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_76])).
% 14.13/6.06  tff(c_14848, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_108])).
% 14.13/6.06  tff(c_14851, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_14848])).
% 14.13/6.06  tff(c_14855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_14851])).
% 14.13/6.06  tff(c_14857, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_108])).
% 14.13/6.06  tff(c_26, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.13/6.06  tff(c_14862, plain, (![A_12]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_14857, c_26])).
% 14.13/6.06  tff(c_14878, plain, (![A_673]: (~r2_hidden(A_673, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14862])).
% 14.13/6.06  tff(c_14903, plain, (![B_675]: (r1_tarski(k1_xboole_0, B_675))), inference(resolution, [status(thm)], [c_6, c_14878])).
% 14.13/6.06  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.13/6.06  tff(c_14992, plain, (![B_684]: (k1_xboole_0=B_684 | ~r1_tarski(B_684, k1_xboole_0))), inference(resolution, [status(thm)], [c_14903, c_10])).
% 14.13/6.06  tff(c_15125, plain, (![B_695]: (k2_relat_1(B_695)=k1_xboole_0 | ~v5_relat_1(B_695, k1_xboole_0) | ~v1_relat_1(B_695))), inference(resolution, [status(thm)], [c_32, c_14992])).
% 14.13/6.06  tff(c_15136, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_15125])).
% 14.13/6.06  tff(c_15145, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_15136])).
% 14.13/6.06  tff(c_15147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14585, c_15145])).
% 14.13/6.06  tff(c_15149, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_332])).
% 14.13/6.06  tff(c_15284, plain, (![B_711, A_712]: (r1_tarski(k2_relat_1(B_711), A_712) | ~v5_relat_1(B_711, A_712) | ~v1_relat_1(B_711))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.13/6.06  tff(c_15300, plain, (![A_712]: (r1_tarski(k1_xboole_0, A_712) | ~v5_relat_1(k1_xboole_0, A_712) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15149, c_15284])).
% 14.13/6.06  tff(c_15314, plain, (![A_713]: (r1_tarski(k1_xboole_0, A_713))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_36, c_15300])).
% 14.13/6.06  tff(c_15325, plain, (![A_713]: (k1_xboole_0=A_713 | ~r1_tarski(A_713, k1_xboole_0))), inference(resolution, [status(thm)], [c_15314, c_10])).
% 14.13/6.06  tff(c_15448, plain, (![B_729]: (k1_xboole_0=B_729 | ~v1_xboole_0(B_729))), inference(resolution, [status(thm)], [c_15420, c_15325])).
% 14.13/6.06  tff(c_16544, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_16522, c_15448])).
% 14.13/6.06  tff(c_16588, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16544, c_16544, c_18])).
% 14.13/6.06  tff(c_16583, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16544, c_14566])).
% 14.13/6.06  tff(c_16612, plain, (![A_818, B_819, C_820]: (k2_relset_1(A_818, B_819, C_820)=k2_relat_1(C_820) | ~m1_subset_1(C_820, k1_zfmisc_1(k2_zfmisc_1(A_818, B_819))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.13/6.06  tff(c_16622, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_16612])).
% 14.13/6.06  tff(c_16626, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_16622])).
% 14.13/6.06  tff(c_16745, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16583, c_16626])).
% 14.13/6.06  tff(c_15396, plain, (![A_719]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_719, '#skF_4'))), inference(resolution, [status(thm)], [c_100, c_15390])).
% 14.13/6.06  tff(c_15397, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_15396])).
% 14.13/6.06  tff(c_16787, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16745, c_15397])).
% 14.13/6.06  tff(c_17005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16522, c_16588, c_16787])).
% 14.13/6.06  tff(c_17007, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_15396])).
% 14.13/6.06  tff(c_17379, plain, (![B_855, A_856, A_857]: (~v1_xboole_0(B_855) | ~r2_hidden(A_856, A_857) | ~r1_tarski(A_857, B_855))), inference(resolution, [status(thm)], [c_24, c_15390])).
% 14.13/6.06  tff(c_17396, plain, (![B_859, A_860, B_861]: (~v1_xboole_0(B_859) | ~r1_tarski(A_860, B_859) | r1_tarski(A_860, B_861))), inference(resolution, [status(thm)], [c_6, c_17379])).
% 14.13/6.06  tff(c_17407, plain, (![B_862, B_863]: (~v1_xboole_0(B_862) | r1_tarski(B_862, B_863))), inference(resolution, [status(thm)], [c_14, c_17396])).
% 14.13/6.06  tff(c_151, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.13/6.06  tff(c_155, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_100, c_151])).
% 14.13/6.06  tff(c_15194, plain, (![B_699, A_700]: (B_699=A_700 | ~r1_tarski(B_699, A_700) | ~r1_tarski(A_700, B_699))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.13/6.06  tff(c_15199, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_155, c_15194])).
% 14.13/6.06  tff(c_15227, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_15199])).
% 14.13/6.06  tff(c_17428, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_17407, c_15227])).
% 14.13/6.06  tff(c_17446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17007, c_17428])).
% 14.13/6.06  tff(c_17447, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_15199])).
% 14.13/6.06  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.13/6.06  tff(c_17466, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_17447, c_16])).
% 14.13/6.06  tff(c_17505, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_17466])).
% 14.13/6.06  tff(c_17513, plain, (![C_870, B_871, A_872]: (~v1_xboole_0(C_870) | ~m1_subset_1(B_871, k1_zfmisc_1(C_870)) | ~r2_hidden(A_872, B_871))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.13/6.06  tff(c_18885, plain, (![B_979, A_980, A_981]: (~v1_xboole_0(B_979) | ~r2_hidden(A_980, A_981) | ~r1_tarski(A_981, B_979))), inference(resolution, [status(thm)], [c_24, c_17513])).
% 14.13/6.06  tff(c_18899, plain, (![B_983, A_984, B_985]: (~v1_xboole_0(B_983) | ~r1_tarski(A_984, B_983) | r1_tarski(A_984, B_985))), inference(resolution, [status(thm)], [c_6, c_18885])).
% 14.13/6.06  tff(c_18928, plain, (![B_988, B_989]: (~v1_xboole_0(B_988) | r1_tarski(B_988, B_989))), inference(resolution, [status(thm)], [c_14, c_18899])).
% 14.13/6.06  tff(c_17461, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17447, c_100])).
% 14.13/6.06  tff(c_17518, plain, (![A_872]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_872, '#skF_4'))), inference(resolution, [status(thm)], [c_17461, c_17513])).
% 14.13/6.06  tff(c_17520, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_17518])).
% 14.13/6.06  tff(c_18736, plain, (![A_974]: (m1_subset_1(A_974, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_974), k2_relat_1(A_974)))) | ~v1_funct_1(A_974) | ~v1_relat_1(A_974))), inference(cnfTransformation, [status(thm)], [f_184])).
% 14.13/6.06  tff(c_18777, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14566, c_18736])).
% 14.13/6.06  tff(c_18798, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_104, c_18, c_14565, c_18777])).
% 14.13/6.06  tff(c_17932, plain, (![C_913, A_914, B_915]: (v1_xboole_0(C_913) | ~m1_subset_1(C_913, k1_zfmisc_1(k2_zfmisc_1(A_914, B_915))) | ~v1_xboole_0(A_914))), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.13/6.06  tff(c_17945, plain, (![C_913]: (v1_xboole_0(C_913) | ~m1_subset_1(C_913, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_17932])).
% 14.13/6.06  tff(c_17948, plain, (![C_913]: (v1_xboole_0(C_913) | ~m1_subset_1(C_913, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_17945])).
% 14.13/6.06  tff(c_18808, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_18798, c_17948])).
% 14.13/6.06  tff(c_18822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17520, c_18808])).
% 14.13/6.06  tff(c_18825, plain, (![A_975]: (~r2_hidden(A_975, '#skF_4'))), inference(splitRight, [status(thm)], [c_17518])).
% 14.13/6.06  tff(c_18831, plain, (![B_976]: (r1_tarski('#skF_4', B_976))), inference(resolution, [status(thm)], [c_6, c_18825])).
% 14.13/6.06  tff(c_18848, plain, (![B_976]: (B_976='#skF_4' | ~r1_tarski(B_976, '#skF_4'))), inference(resolution, [status(thm)], [c_18831, c_10])).
% 14.13/6.06  tff(c_18975, plain, (![B_991]: (B_991='#skF_4' | ~v1_xboole_0(B_991))), inference(resolution, [status(thm)], [c_18928, c_18848])).
% 14.13/6.06  tff(c_18981, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_18975])).
% 14.13/6.06  tff(c_18987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17505, c_18981])).
% 14.13/6.06  tff(c_18989, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_17466])).
% 14.13/6.06  tff(c_19004, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18989, c_18989, c_20])).
% 14.13/6.06  tff(c_18988, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_17466])).
% 14.13/6.06  tff(c_19076, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18989, c_18989, c_18988])).
% 14.13/6.06  tff(c_19077, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_19076])).
% 14.13/6.06  tff(c_19080, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_19077, c_270])).
% 14.13/6.06  tff(c_19162, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19004, c_19080])).
% 14.13/6.06  tff(c_19166, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_24, c_19162])).
% 14.13/6.06  tff(c_18995, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18989, c_18989, c_15149])).
% 14.13/6.06  tff(c_19920, plain, (![A_1085]: (k1_relat_1(k2_funct_1(A_1085))=k2_relat_1(A_1085) | ~v2_funct_1(A_1085) | ~v1_funct_1(A_1085) | ~v1_relat_1(A_1085))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.13/6.06  tff(c_29584, plain, (![A_1406]: (k9_relat_1(k2_funct_1(A_1406), k2_relat_1(A_1406))=k2_relat_1(k2_funct_1(A_1406)) | ~v1_relat_1(k2_funct_1(A_1406)) | ~v2_funct_1(A_1406) | ~v1_funct_1(A_1406) | ~v1_relat_1(A_1406))), inference(superposition, [status(thm), theory('equality')], [c_19920, c_38])).
% 14.13/6.06  tff(c_29639, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18995, c_29584])).
% 14.13/6.06  tff(c_29661, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_104, c_98, c_29639])).
% 14.13/6.06  tff(c_29662, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_29661])).
% 14.13/6.06  tff(c_29665, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_29662])).
% 14.13/6.06  tff(c_29669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_263, c_104, c_29665])).
% 14.13/6.06  tff(c_29671, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_29661])).
% 14.13/6.06  tff(c_19003, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18989, c_18989, c_18])).
% 14.13/6.06  tff(c_15148, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_332])).
% 14.13/6.06  tff(c_15204, plain, (![A_701]: (k10_relat_1(A_701, k2_relat_1(A_701))=k1_relat_1(A_701) | ~v1_relat_1(A_701))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.13/6.06  tff(c_15213, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15149, c_15204])).
% 14.13/6.06  tff(c_15220, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_15148, c_15213])).
% 14.13/6.06  tff(c_18992, plain, (k10_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18989, c_18989, c_18989, c_15220])).
% 14.13/6.06  tff(c_29670, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k2_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_29661])).
% 14.13/6.06  tff(c_29773, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k10_relat_1('#skF_4', '#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_29670, c_56])).
% 14.13/6.06  tff(c_29780, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_104, c_98, c_18992, c_29773])).
% 14.13/6.06  tff(c_20932, plain, (![A_1179]: (m1_subset_1(A_1179, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1179), k2_relat_1(A_1179)))) | ~v1_funct_1(A_1179) | ~v1_relat_1(A_1179))), inference(cnfTransformation, [status(thm)], [f_184])).
% 14.13/6.06  tff(c_20983, plain, (![A_1179]: (r1_tarski(A_1179, k2_zfmisc_1(k1_relat_1(A_1179), k2_relat_1(A_1179))) | ~v1_funct_1(A_1179) | ~v1_relat_1(A_1179))), inference(resolution, [status(thm)], [c_20932, c_22])).
% 14.13/6.06  tff(c_29894, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_29780, c_20983])).
% 14.13/6.06  tff(c_30019, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29671, c_244, c_19003, c_29894])).
% 14.13/6.06  tff(c_30021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19166, c_30019])).
% 14.13/6.06  tff(c_30023, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_19076])).
% 14.13/6.06  tff(c_31969, plain, (![A_1569, B_1570, C_1571]: (k2_relset_1(A_1569, B_1570, C_1571)=k2_relat_1(C_1571) | ~m1_subset_1(C_1571, k1_zfmisc_1(k2_zfmisc_1(A_1569, B_1570))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.13/6.06  tff(c_32067, plain, (![B_1578, C_1579]: (k2_relset_1('#skF_4', B_1578, C_1579)=k2_relat_1(C_1579) | ~m1_subset_1(C_1579, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_19004, c_31969])).
% 14.13/6.06  tff(c_32069, plain, (![B_1578]: (k2_relset_1('#skF_4', B_1578, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_17461, c_32067])).
% 14.13/6.06  tff(c_32074, plain, (![B_1578]: (k2_relset_1('#skF_4', B_1578, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18995, c_32069])).
% 14.13/6.06  tff(c_30022, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_19076])).
% 14.13/6.06  tff(c_30027, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30022, c_96])).
% 14.13/6.06  tff(c_32076, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32074, c_30027])).
% 14.13/6.06  tff(c_32078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30023, c_32076])).
% 14.13/6.06  tff(c_32080, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_243])).
% 14.13/6.06  tff(c_39802, plain, (![C_2201, A_2202, B_2203]: (v1_xboole_0(C_2201) | ~m1_subset_1(C_2201, k1_zfmisc_1(k2_zfmisc_1(A_2202, B_2203))) | ~v1_xboole_0(A_2202))), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.13/6.06  tff(c_39819, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_32080, c_39802])).
% 14.13/6.06  tff(c_39829, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_39819])).
% 14.13/6.06  tff(c_33461, plain, (![A_1729, B_1730, C_1731]: (k2_relset_1(A_1729, B_1730, C_1731)=k2_relat_1(C_1731) | ~m1_subset_1(C_1731, k1_zfmisc_1(k2_zfmisc_1(A_1729, B_1730))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.13/6.06  tff(c_33474, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_33461])).
% 14.13/6.06  tff(c_33484, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_33474])).
% 14.13/6.06  tff(c_32079, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_243])).
% 14.13/6.06  tff(c_32173, plain, (![A_1596]: (k1_relat_1(A_1596)=k1_xboole_0 | k2_relat_1(A_1596)!=k1_xboole_0 | ~v1_relat_1(A_1596))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.13/6.06  tff(c_32194, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_263, c_32173])).
% 14.13/6.06  tff(c_32198, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32194])).
% 14.13/6.06  tff(c_33485, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_33484, c_32198])).
% 14.13/6.06  tff(c_33345, plain, (![A_1715, B_1716, C_1717]: (k1_relset_1(A_1715, B_1716, C_1717)=k1_relat_1(C_1717) | ~m1_subset_1(C_1717, k1_zfmisc_1(k2_zfmisc_1(A_1715, B_1716))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.13/6.06  tff(c_33364, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_33345])).
% 14.13/6.06  tff(c_34259, plain, (![B_1788, A_1789, C_1790]: (k1_xboole_0=B_1788 | k1_relset_1(A_1789, B_1788, C_1790)=A_1789 | ~v1_funct_2(C_1790, A_1789, B_1788) | ~m1_subset_1(C_1790, k1_zfmisc_1(k2_zfmisc_1(A_1789, B_1788))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.13/6.06  tff(c_34278, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_100, c_34259])).
% 14.13/6.06  tff(c_34295, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_33364, c_34278])).
% 14.13/6.06  tff(c_34296, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_33485, c_34295])).
% 14.13/6.06  tff(c_32641, plain, (![A_1646]: (k2_relat_1(A_1646)=k1_xboole_0 | k1_relat_1(A_1646)!=k1_xboole_0 | ~v1_relat_1(A_1646))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.13/6.06  tff(c_32650, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_263, c_32641])).
% 14.13/6.06  tff(c_32664, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_32198, c_32650])).
% 14.13/6.06  tff(c_34313, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34296, c_32664])).
% 14.13/6.06  tff(c_33362, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32080, c_33345])).
% 14.13/6.06  tff(c_34359, plain, (![B_1791, C_1792, A_1793]: (k1_xboole_0=B_1791 | v1_funct_2(C_1792, A_1793, B_1791) | k1_relset_1(A_1793, B_1791, C_1792)!=A_1793 | ~m1_subset_1(C_1792, k1_zfmisc_1(k2_zfmisc_1(A_1793, B_1791))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.13/6.06  tff(c_34368, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_32080, c_34359])).
% 14.13/6.06  tff(c_34384, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_33362, c_34368])).
% 14.13/6.06  tff(c_34385, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_32079, c_34313, c_34384])).
% 14.13/6.06  tff(c_34394, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_60, c_34385])).
% 14.13/6.06  tff(c_34397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_263, c_104, c_98, c_33484, c_34394])).
% 14.13/6.06  tff(c_34399, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32194])).
% 14.13/6.06  tff(c_36426, plain, (![C_1970, A_1971, B_1972]: (v1_xboole_0(C_1970) | ~m1_subset_1(C_1970, k1_zfmisc_1(k2_zfmisc_1(A_1971, B_1972))) | ~v1_xboole_0(A_1971))), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.13/6.06  tff(c_36443, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_32080, c_36426])).
% 14.13/6.06  tff(c_36449, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_36443])).
% 14.13/6.06  tff(c_36837, plain, (![A_2003, B_2004, C_2005]: (k2_relset_1(A_2003, B_2004, C_2005)=k2_relat_1(C_2005) | ~m1_subset_1(C_2005, k1_zfmisc_1(k2_zfmisc_1(A_2003, B_2004))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.13/6.06  tff(c_36847, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_36837])).
% 14.13/6.06  tff(c_36858, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_34399, c_36847])).
% 14.13/6.06  tff(c_36906, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36858, c_8])).
% 14.13/6.06  tff(c_36908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36449, c_36906])).
% 14.13/6.06  tff(c_36910, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_36443])).
% 14.13/6.06  tff(c_36393, plain, (![C_1961, B_1962, A_1963]: (~v1_xboole_0(C_1961) | ~m1_subset_1(B_1962, k1_zfmisc_1(C_1961)) | ~r2_hidden(A_1963, B_1962))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.13/6.06  tff(c_36404, plain, (![B_1964, A_1965, A_1966]: (~v1_xboole_0(B_1964) | ~r2_hidden(A_1965, A_1966) | ~r1_tarski(A_1966, B_1964))), inference(resolution, [status(thm)], [c_24, c_36393])).
% 14.13/6.06  tff(c_36409, plain, (![B_1967, A_1968, B_1969]: (~v1_xboole_0(B_1967) | ~r1_tarski(A_1968, B_1967) | r1_tarski(A_1968, B_1969))), inference(resolution, [status(thm)], [c_6, c_36404])).
% 14.13/6.06  tff(c_36948, plain, (![B_2007, B_2008]: (~v1_xboole_0(B_2007) | r1_tarski(B_2007, B_2008))), inference(resolution, [status(thm)], [c_14, c_36409])).
% 14.13/6.06  tff(c_32196, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_119, c_32173])).
% 14.13/6.06  tff(c_34428, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32196])).
% 14.13/6.06  tff(c_35118, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_108])).
% 14.13/6.06  tff(c_35121, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_35118])).
% 14.13/6.06  tff(c_35125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_35121])).
% 14.13/6.06  tff(c_35127, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_108])).
% 14.13/6.06  tff(c_35129, plain, (![A_12]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_35127, c_26])).
% 14.13/6.06  tff(c_35143, plain, (![A_1864]: (~r2_hidden(A_1864, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_35129])).
% 14.13/6.06  tff(c_35177, plain, (![B_1868]: (r1_tarski(k1_xboole_0, B_1868))), inference(resolution, [status(thm)], [c_6, c_35143])).
% 14.13/6.06  tff(c_35204, plain, (![B_1872]: (k1_xboole_0=B_1872 | ~r1_tarski(B_1872, k1_xboole_0))), inference(resolution, [status(thm)], [c_35177, c_10])).
% 14.13/6.06  tff(c_35468, plain, (![B_1891]: (k2_relat_1(B_1891)=k1_xboole_0 | ~v5_relat_1(B_1891, k1_xboole_0) | ~v1_relat_1(B_1891))), inference(resolution, [status(thm)], [c_32, c_35204])).
% 14.13/6.06  tff(c_35483, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_35468])).
% 14.13/6.06  tff(c_35495, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_35483])).
% 14.13/6.06  tff(c_35497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34428, c_35495])).
% 14.13/6.06  tff(c_35499, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32196])).
% 14.13/6.06  tff(c_36243, plain, (![B_1949, A_1950]: (r1_tarski(k2_relat_1(B_1949), A_1950) | ~v5_relat_1(B_1949, A_1950) | ~v1_relat_1(B_1949))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.13/6.06  tff(c_36265, plain, (![A_1950]: (r1_tarski(k1_xboole_0, A_1950) | ~v5_relat_1(k1_xboole_0, A_1950) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_35499, c_36243])).
% 14.13/6.06  tff(c_36281, plain, (![A_1951]: (r1_tarski(k1_xboole_0, A_1951))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_36, c_36265])).
% 14.13/6.06  tff(c_36292, plain, (![A_1951]: (k1_xboole_0=A_1951 | ~r1_tarski(A_1951, k1_xboole_0))), inference(resolution, [status(thm)], [c_36281, c_10])).
% 14.13/6.06  tff(c_37322, plain, (![B_2022]: (k1_xboole_0=B_2022 | ~v1_xboole_0(B_2022))), inference(resolution, [status(thm)], [c_36948, c_36292])).
% 14.13/6.06  tff(c_37333, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36910, c_37322])).
% 14.13/6.06  tff(c_37367, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37333, c_37333, c_18])).
% 14.13/6.06  tff(c_36402, plain, (![A_1963]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_1963, '#skF_4'))), inference(resolution, [status(thm)], [c_100, c_36393])).
% 14.13/6.06  tff(c_36403, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_36402])).
% 14.13/6.06  tff(c_37641, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37367, c_36403])).
% 14.13/6.06  tff(c_37647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36910, c_37641])).
% 14.13/6.06  tff(c_37649, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_36402])).
% 14.13/6.06  tff(c_38179, plain, (![B_2058, A_2059, A_2060]: (~v1_xboole_0(B_2058) | ~r2_hidden(A_2059, A_2060) | ~r1_tarski(A_2060, B_2058))), inference(resolution, [status(thm)], [c_24, c_36393])).
% 14.13/6.06  tff(c_38183, plain, (![B_2061, A_2062, B_2063]: (~v1_xboole_0(B_2061) | ~r1_tarski(A_2062, B_2061) | r1_tarski(A_2062, B_2063))), inference(resolution, [status(thm)], [c_6, c_38179])).
% 14.13/6.06  tff(c_38197, plain, (![B_2064, B_2065]: (~v1_xboole_0(B_2064) | r1_tarski(B_2064, B_2065))), inference(resolution, [status(thm)], [c_14, c_38183])).
% 14.13/6.06  tff(c_32132, plain, (![B_1587, A_1588]: (B_1587=A_1588 | ~r1_tarski(B_1587, A_1588) | ~r1_tarski(A_1588, B_1587))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.13/6.06  tff(c_32140, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_155, c_32132])).
% 14.13/6.06  tff(c_34418, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_32140])).
% 14.13/6.06  tff(c_38221, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38197, c_34418])).
% 14.13/6.06  tff(c_38237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37649, c_38221])).
% 14.13/6.06  tff(c_38238, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_32140])).
% 14.13/6.06  tff(c_38268, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38238, c_100])).
% 14.13/6.06  tff(c_41208, plain, (![A_2303, B_2304, C_2305]: (k2_relset_1(A_2303, B_2304, C_2305)=k2_relat_1(C_2305) | ~m1_subset_1(C_2305, k1_zfmisc_1(k2_zfmisc_1(A_2303, B_2304))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.13/6.06  tff(c_41261, plain, (![C_2309]: (k2_relset_1('#skF_2', '#skF_3', C_2309)=k2_relat_1(C_2309) | ~m1_subset_1(C_2309, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_38238, c_41208])).
% 14.13/6.06  tff(c_41264, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38268, c_41261])).
% 14.13/6.06  tff(c_41270, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_34399, c_41264])).
% 14.13/6.06  tff(c_41345, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41270, c_8])).
% 14.13/6.06  tff(c_41347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39829, c_41345])).
% 14.13/6.06  tff(c_41349, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_39819])).
% 14.13/6.06  tff(c_39730, plain, (![C_2189, B_2190, A_2191]: (~v1_xboole_0(C_2189) | ~m1_subset_1(B_2190, k1_zfmisc_1(C_2189)) | ~r2_hidden(A_2191, B_2190))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.13/6.06  tff(c_39742, plain, (![B_2192, A_2193, A_2194]: (~v1_xboole_0(B_2192) | ~r2_hidden(A_2193, A_2194) | ~r1_tarski(A_2194, B_2192))), inference(resolution, [status(thm)], [c_24, c_39730])).
% 14.13/6.06  tff(c_39746, plain, (![B_2195, A_2196, B_2197]: (~v1_xboole_0(B_2195) | ~r1_tarski(A_2196, B_2195) | r1_tarski(A_2196, B_2197))), inference(resolution, [status(thm)], [c_6, c_39742])).
% 14.13/6.06  tff(c_39760, plain, (![B_2198, B_2199]: (~v1_xboole_0(B_2198) | r1_tarski(B_2198, B_2199))), inference(resolution, [status(thm)], [c_14, c_39746])).
% 14.13/6.06  tff(c_38306, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32196])).
% 14.13/6.06  tff(c_38477, plain, (![C_2084, B_2085, A_2086]: (~v1_xboole_0(C_2084) | ~m1_subset_1(B_2085, k1_zfmisc_1(C_2084)) | ~r2_hidden(A_2086, B_2085))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.13/6.06  tff(c_38489, plain, (![B_2087, A_2088, A_2089]: (~v1_xboole_0(B_2087) | ~r2_hidden(A_2088, A_2089) | ~r1_tarski(A_2089, B_2087))), inference(resolution, [status(thm)], [c_24, c_38477])).
% 14.13/6.06  tff(c_38493, plain, (![B_2090, A_2091, B_2092]: (~v1_xboole_0(B_2090) | ~r1_tarski(A_2091, B_2090) | r1_tarski(A_2091, B_2092))), inference(resolution, [status(thm)], [c_6, c_38489])).
% 14.13/6.06  tff(c_38503, plain, (![B_2093, B_2094]: (~v1_xboole_0(B_2093) | r1_tarski(B_2093, B_2094))), inference(resolution, [status(thm)], [c_14, c_38493])).
% 14.13/6.06  tff(c_30, plain, (![B_20, A_19]: (v5_relat_1(B_20, A_19) | ~r1_tarski(k2_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.13/6.06  tff(c_38597, plain, (![B_2103, B_2104]: (v5_relat_1(B_2103, B_2104) | ~v1_relat_1(B_2103) | ~v1_xboole_0(k2_relat_1(B_2103)))), inference(resolution, [status(thm)], [c_38503, c_30])).
% 14.13/6.06  tff(c_38601, plain, (![B_2104]: (v5_relat_1('#skF_4', B_2104) | ~v1_relat_1('#skF_4') | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34399, c_38597])).
% 14.13/6.06  tff(c_38605, plain, (![B_2104]: (v5_relat_1('#skF_4', B_2104))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_263, c_38601])).
% 14.13/6.06  tff(c_38371, plain, (![B_2076, A_2077]: (r1_tarski(k2_relat_1(B_2076), A_2077) | ~v5_relat_1(B_2076, A_2077) | ~v1_relat_1(B_2076))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.13/6.06  tff(c_38394, plain, (![A_2077]: (r1_tarski(k1_xboole_0, A_2077) | ~v5_relat_1('#skF_4', A_2077) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34399, c_38371])).
% 14.13/6.06  tff(c_38403, plain, (![A_2077]: (r1_tarski(k1_xboole_0, A_2077) | ~v5_relat_1('#skF_4', A_2077))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_38394])).
% 14.13/6.06  tff(c_38632, plain, (![A_2109]: (r1_tarski(k1_xboole_0, A_2109))), inference(demodulation, [status(thm), theory('equality')], [c_38605, c_38403])).
% 14.13/6.06  tff(c_38664, plain, (![A_2110]: (k1_xboole_0=A_2110 | ~r1_tarski(A_2110, k1_xboole_0))), inference(resolution, [status(thm)], [c_38632, c_10])).
% 14.13/6.06  tff(c_38873, plain, (![B_2121]: (k2_relat_1(B_2121)=k1_xboole_0 | ~v5_relat_1(B_2121, k1_xboole_0) | ~v1_relat_1(B_2121))), inference(resolution, [status(thm)], [c_32, c_38664])).
% 14.13/6.06  tff(c_38885, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_38873])).
% 14.13/6.06  tff(c_38894, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_38885])).
% 14.13/6.06  tff(c_38896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38306, c_38894])).
% 14.13/6.06  tff(c_38898, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32196])).
% 14.13/6.06  tff(c_39605, plain, (![B_2182, A_2183]: (r1_tarski(k2_relat_1(B_2182), A_2183) | ~v5_relat_1(B_2182, A_2183) | ~v1_relat_1(B_2182))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.13/6.06  tff(c_39631, plain, (![A_2183]: (r1_tarski(k1_xboole_0, A_2183) | ~v5_relat_1(k1_xboole_0, A_2183) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38898, c_39605])).
% 14.13/6.06  tff(c_39652, plain, (![A_2184]: (r1_tarski(k1_xboole_0, A_2184))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_36, c_39631])).
% 14.13/6.06  tff(c_39669, plain, (![A_2184]: (k1_xboole_0=A_2184 | ~r1_tarski(A_2184, k1_xboole_0))), inference(resolution, [status(thm)], [c_39652, c_10])).
% 14.13/6.06  tff(c_39790, plain, (![B_2198]: (k1_xboole_0=B_2198 | ~v1_xboole_0(B_2198))), inference(resolution, [status(thm)], [c_39760, c_39669])).
% 14.13/6.06  tff(c_41356, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_41349, c_39790])).
% 14.13/6.06  tff(c_41392, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41356, c_41356, c_20])).
% 14.13/6.06  tff(c_39738, plain, (![A_2191]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_2191, k2_funct_1('#skF_4')))), inference(resolution, [status(thm)], [c_32080, c_39730])).
% 14.13/6.06  tff(c_39741, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_39738])).
% 14.13/6.06  tff(c_41546, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41392, c_39741])).
% 14.13/6.06  tff(c_41552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41349, c_41546])).
% 14.13/6.06  tff(c_41554, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_39738])).
% 14.13/6.06  tff(c_41696, plain, (![B_2319, A_2320, A_2321]: (~v1_xboole_0(B_2319) | ~r2_hidden(A_2320, A_2321) | ~r1_tarski(A_2321, B_2319))), inference(resolution, [status(thm)], [c_24, c_39730])).
% 14.13/6.06  tff(c_41700, plain, (![B_2322, A_2323, B_2324]: (~v1_xboole_0(B_2322) | ~r1_tarski(A_2323, B_2322) | r1_tarski(A_2323, B_2324))), inference(resolution, [status(thm)], [c_6, c_41696])).
% 14.13/6.06  tff(c_41711, plain, (![B_2325, B_2326]: (~v1_xboole_0(B_2325) | r1_tarski(B_2325, B_2326))), inference(resolution, [status(thm)], [c_14, c_41700])).
% 14.13/6.06  tff(c_41587, plain, (![A_2315]: (~r2_hidden(A_2315, k2_funct_1('#skF_4')))), inference(splitRight, [status(thm)], [c_39738])).
% 14.13/6.06  tff(c_41594, plain, (![B_2316]: (r1_tarski(k2_funct_1('#skF_4'), B_2316))), inference(resolution, [status(thm)], [c_6, c_41587])).
% 14.13/6.06  tff(c_41613, plain, (k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_41594, c_39669])).
% 14.13/6.06  tff(c_32095, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_32080, c_22])).
% 14.13/6.06  tff(c_32139, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4') | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32095, c_32132])).
% 14.13/6.06  tff(c_39678, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_32139])).
% 14.13/6.06  tff(c_41623, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_41613, c_39678])).
% 14.13/6.06  tff(c_41716, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_41711, c_41623])).
% 14.13/6.06  tff(c_41743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41554, c_41716])).
% 14.13/6.06  tff(c_41744, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_32139])).
% 14.13/6.06  tff(c_41870, plain, (![C_2338, A_2339, B_2340]: (v1_xboole_0(C_2338) | ~m1_subset_1(C_2338, k1_zfmisc_1(k2_zfmisc_1(A_2339, B_2340))) | ~v1_xboole_0(A_2339))), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.13/6.06  tff(c_41873, plain, (![C_2338]: (v1_xboole_0(C_2338) | ~m1_subset_1(C_2338, k1_zfmisc_1(k2_funct_1('#skF_4'))) | ~v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_41744, c_41870])).
% 14.13/6.06  tff(c_42096, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_41873])).
% 14.13/6.06  tff(c_42879, plain, (![A_2412, B_2413, C_2414]: (k2_relset_1(A_2412, B_2413, C_2414)=k2_relat_1(C_2414) | ~m1_subset_1(C_2414, k1_zfmisc_1(k2_zfmisc_1(A_2412, B_2413))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.13/6.06  tff(c_42962, plain, (![C_2421]: (k2_relset_1('#skF_2', '#skF_3', C_2421)=k2_relat_1(C_2421) | ~m1_subset_1(C_2421, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_38238, c_42879])).
% 14.13/6.06  tff(c_42965, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38268, c_42962])).
% 14.13/6.06  tff(c_42971, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_34399, c_42965])).
% 14.13/6.06  tff(c_43033, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42971, c_8])).
% 14.13/6.06  tff(c_43035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42096, c_43033])).
% 14.13/6.06  tff(c_43037, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_41873])).
% 14.13/6.06  tff(c_41763, plain, (![C_2327, B_2328, A_2329]: (~v1_xboole_0(C_2327) | ~m1_subset_1(B_2328, k1_zfmisc_1(C_2327)) | ~r2_hidden(A_2329, B_2328))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.13/6.06  tff(c_41866, plain, (![B_2335, A_2336, A_2337]: (~v1_xboole_0(B_2335) | ~r2_hidden(A_2336, A_2337) | ~r1_tarski(A_2337, B_2335))), inference(resolution, [status(thm)], [c_24, c_41763])).
% 14.13/6.06  tff(c_41920, plain, (![B_2343, A_2344, B_2345]: (~v1_xboole_0(B_2343) | ~r1_tarski(A_2344, B_2343) | r1_tarski(A_2344, B_2345))), inference(resolution, [status(thm)], [c_6, c_41866])).
% 14.13/6.06  tff(c_41931, plain, (![B_2346, B_2347]: (~v1_xboole_0(B_2346) | r1_tarski(B_2346, B_2347))), inference(resolution, [status(thm)], [c_14, c_41920])).
% 14.13/6.06  tff(c_41967, plain, (![B_2346]: (k1_xboole_0=B_2346 | ~v1_xboole_0(B_2346))), inference(resolution, [status(thm)], [c_41931, c_39669])).
% 14.13/6.06  tff(c_43044, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_43037, c_41967])).
% 14.13/6.06  tff(c_41752, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k2_funct_1('#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_41744, c_16])).
% 14.13/6.06  tff(c_41818, plain, (k2_funct_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_41752])).
% 14.13/6.06  tff(c_43063, plain, (k2_funct_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_43044, c_41818])).
% 14.13/6.06  tff(c_43088, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_43044, c_43044, c_20])).
% 14.13/6.06  tff(c_43372, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_43088, c_41744])).
% 14.13/6.06  tff(c_43374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43063, c_43372])).
% 14.13/6.06  tff(c_43375, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_41752])).
% 14.13/6.06  tff(c_43449, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_43375])).
% 14.13/6.06  tff(c_38273, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_38238, c_16])).
% 14.13/6.06  tff(c_38925, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_38273])).
% 14.13/6.06  tff(c_43463, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_43449, c_38925])).
% 14.13/6.06  tff(c_43692, plain, (![B_2443]: (k2_zfmisc_1('#skF_2', B_2443)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_43449, c_43449, c_20])).
% 14.13/6.06  tff(c_43702, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_43692, c_38238])).
% 14.13/6.06  tff(c_43721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43463, c_43702])).
% 14.13/6.06  tff(c_43722, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_43375])).
% 14.13/6.06  tff(c_43757, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_43722, c_38925])).
% 14.13/6.06  tff(c_44012, plain, (![A_2457]: (k2_zfmisc_1(A_2457, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_43722, c_43722, c_18])).
% 14.13/6.06  tff(c_44025, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_44012, c_38238])).
% 14.13/6.06  tff(c_44042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43757, c_44025])).
% 14.13/6.06  tff(c_44044, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_38273])).
% 14.13/6.06  tff(c_34398, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32194])).
% 14.13/6.06  tff(c_44052, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44044, c_34398])).
% 14.13/6.06  tff(c_44058, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44044, c_44044, c_20])).
% 14.13/6.06  tff(c_46057, plain, (![A_2606, B_2607, C_2608]: (k1_relset_1(A_2606, B_2607, C_2608)=k1_relat_1(C_2608) | ~m1_subset_1(C_2608, k1_zfmisc_1(k2_zfmisc_1(A_2606, B_2607))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 14.13/6.06  tff(c_46307, plain, (![B_2629, C_2630]: (k1_relset_1('#skF_4', B_2629, C_2630)=k1_relat_1(C_2630) | ~m1_subset_1(C_2630, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_44058, c_46057])).
% 14.13/6.06  tff(c_46309, plain, (![B_2629]: (k1_relset_1('#skF_4', B_2629, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_38268, c_46307])).
% 14.13/6.06  tff(c_46314, plain, (![B_2629]: (k1_relset_1('#skF_4', B_2629, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44052, c_46309])).
% 14.13/6.06  tff(c_80, plain, (![C_53, B_52]: (v1_funct_2(C_53, k1_xboole_0, B_52) | k1_relset_1(k1_xboole_0, B_52, C_53)!=k1_xboole_0 | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_52))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 14.13/6.06  tff(c_105, plain, (![C_53, B_52]: (v1_funct_2(C_53, k1_xboole_0, B_52) | k1_relset_1(k1_xboole_0, B_52, C_53)!=k1_xboole_0 | ~m1_subset_1(C_53, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_80])).
% 14.13/6.06  tff(c_46601, plain, (![C_2642, B_2643]: (v1_funct_2(C_2642, '#skF_4', B_2643) | k1_relset_1('#skF_4', B_2643, C_2642)!='#skF_4' | ~m1_subset_1(C_2642, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44044, c_44044, c_44044, c_44044, c_105])).
% 14.13/6.06  tff(c_46603, plain, (![B_2643]: (v1_funct_2('#skF_4', '#skF_4', B_2643) | k1_relset_1('#skF_4', B_2643, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_38268, c_46601])).
% 14.13/6.06  tff(c_46609, plain, (![B_2643]: (v1_funct_2('#skF_4', '#skF_4', B_2643))), inference(demodulation, [status(thm), theory('equality')], [c_46314, c_46603])).
% 14.13/6.06  tff(c_44063, plain, (![B_22]: (v5_relat_1('#skF_4', B_22))), inference(demodulation, [status(thm), theory('equality')], [c_44044, c_36])).
% 14.13/6.06  tff(c_44051, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44044, c_34399])).
% 14.13/6.06  tff(c_44093, plain, (![B_2460, A_2461]: (r1_tarski(k2_relat_1(B_2460), A_2461) | ~v5_relat_1(B_2460, A_2461) | ~v1_relat_1(B_2460))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.13/6.06  tff(c_44106, plain, (![A_2461]: (r1_tarski('#skF_4', A_2461) | ~v5_relat_1('#skF_4', A_2461) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_44051, c_44093])).
% 14.13/6.06  tff(c_44111, plain, (![A_2461]: (r1_tarski('#skF_4', A_2461))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_44063, c_44106])).
% 14.13/6.06  tff(c_44043, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_38273])).
% 14.13/6.06  tff(c_44149, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44044, c_44044, c_44043])).
% 14.13/6.06  tff(c_44150, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_44149])).
% 14.13/6.06  tff(c_44153, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44150, c_32080])).
% 14.13/6.06  tff(c_44269, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44058, c_44153])).
% 14.13/6.06  tff(c_44283, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_44269, c_22])).
% 14.13/6.06  tff(c_44297, plain, (k2_funct_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_44283, c_10])).
% 14.13/6.06  tff(c_44303, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44111, c_44297])).
% 14.13/6.06  tff(c_44154, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44150, c_32079])).
% 14.13/6.06  tff(c_44307, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44303, c_44154])).
% 14.13/6.06  tff(c_46614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46609, c_44307])).
% 14.13/6.06  tff(c_46616, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_44149])).
% 14.13/6.06  tff(c_46938, plain, (![A_2671]: (v1_funct_2('#skF_4', A_2671, '#skF_4') | A_2671='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38268, c_44044, c_44044, c_44044, c_44044, c_44044, c_108])).
% 14.13/6.06  tff(c_44057, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44044, c_44044, c_18])).
% 14.13/6.06  tff(c_46615, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_44149])).
% 14.13/6.06  tff(c_46618, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46615, c_32095])).
% 14.13/6.06  tff(c_46748, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44057, c_46618])).
% 14.13/6.06  tff(c_46756, plain, (k2_funct_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_46748, c_10])).
% 14.13/6.06  tff(c_46762, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44111, c_46756])).
% 14.13/6.06  tff(c_46620, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46615, c_32079])).
% 14.13/6.06  tff(c_46764, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46762, c_46620])).
% 14.13/6.06  tff(c_46941, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_46938, c_46764])).
% 14.13/6.06  tff(c_46945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46616, c_46941])).
% 14.13/6.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.13/6.06  
% 14.13/6.06  Inference rules
% 14.13/6.06  ----------------------
% 14.13/6.06  #Ref     : 0
% 14.13/6.06  #Sup     : 10230
% 14.13/6.06  #Fact    : 0
% 14.13/6.06  #Define  : 0
% 14.13/6.06  #Split   : 165
% 14.13/6.06  #Chain   : 0
% 14.13/6.06  #Close   : 0
% 14.13/6.06  
% 14.13/6.07  Ordering : KBO
% 14.13/6.07  
% 14.13/6.07  Simplification rules
% 14.13/6.07  ----------------------
% 14.13/6.07  #Subsume      : 3172
% 14.13/6.07  #Demod        : 10744
% 14.13/6.07  #Tautology    : 4482
% 14.13/6.07  #SimpNegUnit  : 314
% 14.13/6.07  #BackRed      : 826
% 14.13/6.07  
% 14.13/6.07  #Partial instantiations: 0
% 14.13/6.07  #Strategies tried      : 1
% 14.13/6.07  
% 14.13/6.07  Timing (in seconds)
% 14.13/6.07  ----------------------
% 14.13/6.07  Preprocessing        : 0.39
% 14.13/6.07  Parsing              : 0.21
% 14.13/6.07  CNF conversion       : 0.03
% 14.13/6.07  Main loop            : 4.78
% 14.13/6.07  Inferencing          : 1.33
% 14.13/6.07  Reduction            : 1.68
% 14.13/6.07  Demodulation         : 1.19
% 14.13/6.07  BG Simplification    : 0.13
% 14.13/6.07  Subsumption          : 1.27
% 14.13/6.07  Abstraction          : 0.17
% 14.13/6.07  MUC search           : 0.00
% 14.13/6.07  Cooper               : 0.00
% 14.13/6.07  Total                : 5.29
% 14.13/6.07  Index Insertion      : 0.00
% 14.13/6.07  Index Deletion       : 0.00
% 14.13/6.07  Index Matching       : 0.00
% 14.13/6.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
