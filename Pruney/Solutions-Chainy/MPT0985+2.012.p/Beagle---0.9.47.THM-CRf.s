%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:27 EST 2020

% Result     : Theorem 10.42s
% Output     : CNFRefutation 10.68s
% Verified   : 
% Statistics : Number of formulae       :  439 (4718 expanded)
%              Number of leaves         :   51 (1510 expanded)
%              Depth                    :   23
%              Number of atoms          :  780 (13088 expanded)
%              Number of equality atoms :  308 (3667 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_211,negated_conjecture,(
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

tff(f_145,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_153,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_141,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_131,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_194,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_184,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_102,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_11482,plain,(
    ! [C_639,A_640,B_641] :
      ( v1_relat_1(C_639)
      | ~ m1_subset_1(C_639,k1_zfmisc_1(k2_zfmisc_1(A_640,B_641))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_11508,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_11482])).

tff(c_106,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_100,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_98,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_12762,plain,(
    ! [A_751,B_752,C_753] :
      ( k2_relset_1(A_751,B_752,C_753) = k2_relat_1(C_753)
      | ~ m1_subset_1(C_753,k1_zfmisc_1(k2_zfmisc_1(A_751,B_752))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_12778,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_12762])).

tff(c_12793,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_12778])).

tff(c_58,plain,(
    ! [A_27] :
      ( k1_relat_1(k2_funct_1(A_27)) = k2_relat_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    ! [A_19] :
      ( v1_funct_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_96,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_242,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_245,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_242])).

tff(c_248,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_245])).

tff(c_291,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_301,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_291])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_301])).

tff(c_317,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_356,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_361,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_356])).

tff(c_5261,plain,(
    ! [A_344] :
      ( k4_relat_1(A_344) = k2_funct_1(A_344)
      | ~ v2_funct_1(A_344)
      | ~ v1_funct_1(A_344)
      | ~ v1_relat_1(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5267,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_5261])).

tff(c_5271,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_5267])).

tff(c_5272,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5271])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_104,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_963,plain,(
    ! [A_155,B_156,C_157] :
      ( k1_relset_1(A_155,B_156,C_157) = k1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_994,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_963])).

tff(c_4701,plain,(
    ! [B_317,A_318,C_319] :
      ( k1_xboole_0 = B_317
      | k1_relset_1(A_318,B_317,C_319) = A_318
      | ~ v1_funct_2(C_319,A_318,B_317)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_318,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_4717,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_4701])).

tff(c_4735,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_994,c_4717])).

tff(c_4739,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4735])).

tff(c_521,plain,(
    ! [C_107,A_108,B_109] :
      ( v1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_543,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_521])).

tff(c_48,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_318,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_770,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_780,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_770])).

tff(c_794,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_780])).

tff(c_34,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_803,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_34])).

tff(c_809,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_803])).

tff(c_1221,plain,(
    ! [B_181,A_182] :
      ( k9_relat_1(B_181,k10_relat_1(B_181,A_182)) = A_182
      | ~ r1_tarski(A_182,k2_relat_1(B_181))
      | ~ v1_funct_1(B_181)
      | ~ v1_relat_1(B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1225,plain,(
    ! [A_182] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_182)) = A_182
      | ~ r1_tarski(A_182,'#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_1221])).

tff(c_1240,plain,(
    ! [A_183] :
      ( k9_relat_1('#skF_4',k10_relat_1('#skF_4',A_183)) = A_183
      | ~ r1_tarski(A_183,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_106,c_1225])).

tff(c_1249,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_1240])).

tff(c_1257,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1249])).

tff(c_1347,plain,(
    ! [A_186,B_187] :
      ( k9_relat_1(k2_funct_1(A_186),k9_relat_1(A_186,B_187)) = B_187
      | ~ r1_tarski(B_187,k1_relat_1(A_186))
      | ~ v2_funct_1(A_186)
      | ~ v1_funct_1(A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1365,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_1347])).

tff(c_1384,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_106,c_100,c_10,c_1365])).

tff(c_54,plain,(
    ! [A_24,B_26] :
      ( k9_relat_1(k2_funct_1(A_24),k9_relat_1(A_24,B_26)) = B_26
      | ~ r1_tarski(B_26,k1_relat_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1398,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1384,c_54])).

tff(c_1402,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_1398])).

tff(c_1755,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1402])).

tff(c_1758,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1755])).

tff(c_1762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_106,c_1758])).

tff(c_1764,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1402])).

tff(c_1795,plain,(
    ! [B_211,A_212,C_213] :
      ( k1_xboole_0 = B_211
      | k1_relset_1(A_212,B_211,C_213) = A_212
      | ~ v1_funct_2(C_213,A_212,B_211)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_212,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1811,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_1795])).

tff(c_1832,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_994,c_1811])).

tff(c_1836,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1832])).

tff(c_32,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1871,plain,
    ( k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1836,c_32])).

tff(c_1885,plain,(
    k9_relat_1('#skF_4','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_794,c_1871])).

tff(c_673,plain,(
    ! [A_131] :
      ( k2_relat_1(k2_funct_1(A_131)) = k1_relat_1(A_131)
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3537,plain,(
    ! [A_272] :
      ( k10_relat_1(k2_funct_1(A_272),k1_relat_1(A_272)) = k1_relat_1(k2_funct_1(A_272))
      | ~ v1_relat_1(k2_funct_1(A_272))
      | ~ v2_funct_1(A_272)
      | ~ v1_funct_1(A_272)
      | ~ v1_relat_1(A_272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_34])).

tff(c_3561,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1836,c_3537])).

tff(c_3580,plain,(
    k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_106,c_100,c_1764,c_3561])).

tff(c_52,plain,(
    ! [B_23,A_22] :
      ( k10_relat_1(k2_funct_1(B_23),A_22) = k9_relat_1(B_23,A_22)
      | ~ v2_funct_1(B_23)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3588,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k9_relat_1('#skF_4','#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3580,c_52])).

tff(c_3595,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_106,c_100,c_1885,c_3588])).

tff(c_1903,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1885,c_54])).

tff(c_1907,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_106,c_100,c_10,c_1836,c_1903])).

tff(c_3627,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3595,c_32])).

tff(c_3650,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_1907,c_3627])).

tff(c_884,plain,(
    ! [A_151] :
      ( m1_subset_1(A_151,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_151),k2_relat_1(A_151))))
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_911,plain,(
    ! [A_151] :
      ( r1_tarski(A_151,k2_zfmisc_1(k1_relat_1(A_151),k2_relat_1(A_151)))
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_884,c_20])).

tff(c_3690,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3650,c_911])).

tff(c_3723,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_318,c_3595,c_3690])).

tff(c_3725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_3723])).

tff(c_3726,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1832])).

tff(c_18,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_319,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(A_82,B_83)
      | ~ m1_subset_1(A_82,k1_zfmisc_1(B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_327,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_18,c_319])).

tff(c_3765,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_327])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3769,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3726,c_3726,c_14])).

tff(c_898,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_884])).

tff(c_913,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_106,c_898])).

tff(c_932,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_913,c_20])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_944,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_932,c_6])).

tff(c_1011,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_944])).

tff(c_4060,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3769,c_1011])).

tff(c_4070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3765,c_4060])).

tff(c_4071,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_944])).

tff(c_4748,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4739,c_4071])).

tff(c_326,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_102,c_319])).

tff(c_371,plain,(
    ! [B_95,A_96] :
      ( B_95 = A_96
      | ~ r1_tarski(B_95,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_391,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_326,c_371])).

tff(c_449,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_4800,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4748,c_449])).

tff(c_4805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4800])).

tff(c_4806,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4735])).

tff(c_4843,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4806,c_327])).

tff(c_4847,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4806,c_4806,c_14])).

tff(c_5091,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4847,c_449])).

tff(c_5096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4843,c_5091])).

tff(c_5097,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_5100,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5097,c_102])).

tff(c_5213,plain,(
    ! [C_339,A_340,B_341] :
      ( v1_relat_1(C_339)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_340,B_341))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5273,plain,(
    ! [C_345] :
      ( v1_relat_1(C_345)
      | ~ m1_subset_1(C_345,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5097,c_5213])).

tff(c_5279,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5100,c_5273])).

tff(c_5293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5272,c_5279])).

tff(c_5295,plain,(
    v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5271])).

tff(c_5634,plain,(
    ! [A_380,B_381,C_382] :
      ( k1_relset_1(A_380,B_381,C_382) = k1_relat_1(C_382)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_380,B_381))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5686,plain,(
    ! [C_389] :
      ( k1_relset_1('#skF_2','#skF_3',C_389) = k1_relat_1(C_389)
      | ~ m1_subset_1(C_389,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5097,c_5634])).

tff(c_5702,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5100,c_5686])).

tff(c_7914,plain,(
    ! [B_500,A_501,C_502] :
      ( k1_xboole_0 = B_500
      | k1_relset_1(A_501,B_500,C_502) = A_501
      | ~ v1_funct_2(C_502,A_501,B_500)
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(A_501,B_500))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_7923,plain,(
    ! [C_502] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_502) = '#skF_2'
      | ~ v1_funct_2(C_502,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_502,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5097,c_7914])).

tff(c_8040,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7923])).

tff(c_5196,plain,(
    ! [B_336,A_337] :
      ( k1_xboole_0 = B_336
      | k1_xboole_0 = A_337
      | k2_zfmisc_1(A_337,B_336) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5199,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5097,c_5196])).

tff(c_5210,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5199])).

tff(c_8071,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8040,c_5210])).

tff(c_8486,plain,(
    ! [A_521] : k2_zfmisc_1(A_521,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8040,c_8040,c_14])).

tff(c_6342,plain,(
    ! [B_437,A_438,C_439] :
      ( k1_xboole_0 = B_437
      | k1_relset_1(A_438,B_437,C_439) = A_438
      | ~ v1_funct_2(C_439,A_438,B_437)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(A_438,B_437))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_6351,plain,(
    ! [C_439] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_439) = '#skF_2'
      | ~ v1_funct_2(C_439,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_439,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5097,c_6342])).

tff(c_6383,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6351])).

tff(c_6417,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6383,c_327])).

tff(c_6421,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6383,c_6383,c_14])).

tff(c_5536,plain,(
    ! [A_371,B_372,C_373] :
      ( k2_relset_1(A_371,B_372,C_373) = k2_relat_1(C_373)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_371,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_5568,plain,(
    ! [C_376] :
      ( k2_relset_1('#skF_2','#skF_3',C_376) = k2_relat_1(C_376)
      | ~ m1_subset_1(C_376,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5097,c_5536])).

tff(c_5574,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5100,c_5568])).

tff(c_5585,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_5574])).

tff(c_5864,plain,(
    ! [A_410] :
      ( m1_subset_1(A_410,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_410),k2_relat_1(A_410))))
      | ~ v1_funct_1(A_410)
      | ~ v1_relat_1(A_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_5881,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5585,c_5864])).

tff(c_5897,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5295,c_106,c_5881])).

tff(c_5920,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_5897,c_20])).

tff(c_5936,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_5920,c_6])).

tff(c_6058,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5936])).

tff(c_6710,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6421,c_6058])).

tff(c_6716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6417,c_6710])).

tff(c_7297,plain,(
    ! [C_478] :
      ( k1_relset_1('#skF_2','#skF_3',C_478) = '#skF_2'
      | ~ v1_funct_2(C_478,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_478,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_6351])).

tff(c_7303,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_5100,c_7297])).

tff(c_7317,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_5702,c_7303])).

tff(c_7324,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7317,c_6058])).

tff(c_7335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5097,c_7324])).

tff(c_7336,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5936])).

tff(c_8496,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_8486,c_7336])).

tff(c_8542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8071,c_8496])).

tff(c_8775,plain,(
    ! [C_529] :
      ( k1_relset_1('#skF_2','#skF_3',C_529) = '#skF_2'
      | ~ v1_funct_2(C_529,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_529,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_7923])).

tff(c_8784,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_5100,c_8775])).

tff(c_8800,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_5702,c_8784])).

tff(c_8851,plain,
    ( k9_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8800,c_32])).

tff(c_8865,plain,(
    k9_relat_1('#skF_4','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5295,c_5585,c_8851])).

tff(c_8879,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8865,c_54])).

tff(c_8883,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5295,c_106,c_100,c_10,c_8800,c_8879])).

tff(c_8995,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),'#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8883,c_54])).

tff(c_8999,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')),'#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_8995])).

tff(c_9959,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8999])).

tff(c_9962,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_9959])).

tff(c_9966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5295,c_106,c_9962])).

tff(c_9968,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8999])).

tff(c_5507,plain,(
    ! [A_367] :
      ( k2_relat_1(k2_funct_1(A_367)) = k1_relat_1(A_367)
      | ~ v2_funct_1(A_367)
      | ~ v1_funct_1(A_367)
      | ~ v1_relat_1(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_10492,plain,(
    ! [A_580] :
      ( k10_relat_1(k2_funct_1(A_580),k1_relat_1(A_580)) = k1_relat_1(k2_funct_1(A_580))
      | ~ v1_relat_1(k2_funct_1(A_580))
      | ~ v2_funct_1(A_580)
      | ~ v1_funct_1(A_580)
      | ~ v1_relat_1(A_580) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5507,c_34])).

tff(c_10519,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8800,c_10492])).

tff(c_10541,plain,(
    k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5295,c_106,c_100,c_9968,c_10519])).

tff(c_10551,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k9_relat_1('#skF_4','#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10541,c_52])).

tff(c_10558,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5295,c_106,c_100,c_8865,c_10551])).

tff(c_10590,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10558,c_32])).

tff(c_10613,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9968,c_8883,c_10590])).

tff(c_5895,plain,(
    ! [A_410] :
      ( r1_tarski(A_410,k2_zfmisc_1(k1_relat_1(A_410),k2_relat_1(A_410)))
      | ~ v1_funct_1(A_410)
      | ~ v1_relat_1(A_410) ) ),
    inference(resolution,[status(thm)],[c_5864,c_20])).

tff(c_10655,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10613,c_5895])).

tff(c_10688,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9968,c_318,c_10558,c_10655])).

tff(c_10690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_10688])).

tff(c_10692,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5199])).

tff(c_10701,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10692,c_327])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_125,plain,(
    ! [A_47] :
      ( v1_relat_1(A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_129,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_125])).

tff(c_10708,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10692,c_129])).

tff(c_161,plain,(
    ! [A_58] :
      ( v1_xboole_0(k4_relat_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_176,plain,(
    ! [A_62] :
      ( k4_relat_1(A_62) = k1_xboole_0
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_161,c_4])).

tff(c_184,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_176])).

tff(c_10703,plain,(
    k4_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10692,c_10692,c_184])).

tff(c_11295,plain,(
    ! [A_623] :
      ( k4_relat_1(A_623) = k2_funct_1(A_623)
      | ~ v2_funct_1(A_623)
      | ~ v1_funct_1(A_623)
      | ~ v1_relat_1(A_623) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_11301,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_11295])).

tff(c_11305,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10708,c_106,c_10703,c_11301])).

tff(c_10705,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10692,c_10692,c_14])).

tff(c_11028,plain,(
    ! [A_607] :
      ( k4_relat_1(A_607) = k2_funct_1(A_607)
      | ~ v2_funct_1(A_607)
      | ~ v1_funct_1(A_607)
      | ~ v1_relat_1(A_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_11034,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_11028])).

tff(c_11038,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10708,c_106,c_10703,c_11034])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10706,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10692,c_10692,c_16])).

tff(c_10691,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5199])).

tff(c_10753,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10692,c_10692,c_10691])).

tff(c_10754,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10753])).

tff(c_10759,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10754,c_356])).

tff(c_10946,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10706,c_10759])).

tff(c_10950,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_10946])).

tff(c_11039,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11038,c_10950])).

tff(c_11044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11039])).

tff(c_11045,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10753])).

tff(c_11051,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11045,c_356])).

tff(c_11254,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10705,c_11051])).

tff(c_11258,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_11254])).

tff(c_11306,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11305,c_11258])).

tff(c_11311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10701,c_11306])).

tff(c_11312,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_11765,plain,(
    ! [A_670,B_671,C_672] :
      ( k2_relset_1(A_670,B_671,C_672) = k2_relat_1(C_672)
      | ~ m1_subset_1(C_672,k1_zfmisc_1(k2_zfmisc_1(A_670,B_671))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_11781,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_11765])).

tff(c_11797,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_11781])).

tff(c_11313,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_11834,plain,(
    ! [A_675,B_676,C_677] :
      ( k1_relset_1(A_675,B_676,C_677) = k1_relat_1(C_677)
      | ~ m1_subset_1(C_677,k1_zfmisc_1(k2_zfmisc_1(A_675,B_676))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_11862,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_11313,c_11834])).

tff(c_12214,plain,(
    ! [B_712,C_713,A_714] :
      ( k1_xboole_0 = B_712
      | v1_funct_2(C_713,A_714,B_712)
      | k1_relset_1(A_714,B_712,C_713) != A_714
      | ~ m1_subset_1(C_713,k1_zfmisc_1(k2_zfmisc_1(A_714,B_712))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_12223,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_11313,c_12214])).

tff(c_12249,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11862,c_12223])).

tff(c_12250,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_11312,c_12249])).

tff(c_12259,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12250])).

tff(c_12262,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_12259])).

tff(c_12265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11508,c_106,c_100,c_11797,c_12262])).

tff(c_12266,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12250])).

tff(c_12300,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_327])).

tff(c_12304,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12266,c_12266,c_14])).

tff(c_11318,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_11313,c_20])).

tff(c_11328,plain,(
    ! [B_627,A_628] :
      ( B_627 = A_628
      | ~ r1_tarski(B_627,A_628)
      | ~ r1_tarski(A_628,B_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11344,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4')
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_11318,c_11328])).

tff(c_11523,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11344])).

tff(c_12414,plain,(
    ~ r1_tarski('#skF_2',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12304,c_11523])).

tff(c_12419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12300,c_12414])).

tff(c_12420,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_11344])).

tff(c_12437,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12420,c_11313])).

tff(c_12861,plain,(
    ! [A_756,B_757,C_758] :
      ( k1_relset_1(A_756,B_757,C_758) = k1_relat_1(C_758)
      | ~ m1_subset_1(C_758,k1_zfmisc_1(k2_zfmisc_1(A_756,B_757))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_13244,plain,(
    ! [C_798] :
      ( k1_relset_1('#skF_3','#skF_2',C_798) = k1_relat_1(C_798)
      | ~ m1_subset_1(C_798,k1_zfmisc_1(k2_funct_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12420,c_12861])).

tff(c_13261,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_12437,c_13244])).

tff(c_13590,plain,(
    ! [B_815,C_816,A_817] :
      ( k1_xboole_0 = B_815
      | v1_funct_2(C_816,A_817,B_815)
      | k1_relset_1(A_817,B_815,C_816) != A_817
      | ~ m1_subset_1(C_816,k1_zfmisc_1(k2_zfmisc_1(A_817,B_815))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_13599,plain,(
    ! [C_816] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_816,'#skF_3','#skF_2')
      | k1_relset_1('#skF_3','#skF_2',C_816) != '#skF_3'
      | ~ m1_subset_1(C_816,k1_zfmisc_1(k2_funct_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12420,c_13590])).

tff(c_13697,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_13599])).

tff(c_13735,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13697,c_327])).

tff(c_13740,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13697,c_13697,c_16])).

tff(c_11351,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_326,c_11328])).

tff(c_11456,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_11351])).

tff(c_14170,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13740,c_11456])).

tff(c_14175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13735,c_14170])).

tff(c_14688,plain,(
    ! [C_854] :
      ( v1_funct_2(C_854,'#skF_3','#skF_2')
      | k1_relset_1('#skF_3','#skF_2',C_854) != '#skF_3'
      | ~ m1_subset_1(C_854,k1_zfmisc_1(k2_funct_1('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_13599])).

tff(c_14694,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_12437,c_14688])).

tff(c_14706,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13261,c_14694])).

tff(c_14707,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_11312,c_14706])).

tff(c_14713,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_14707])).

tff(c_14716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11508,c_106,c_100,c_12793,c_14713])).

tff(c_14717,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11351])).

tff(c_14720,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14717,c_102])).

tff(c_14775,plain,(
    ! [C_859,A_860,B_861] :
      ( v1_relat_1(C_859)
      | ~ m1_subset_1(C_859,k1_zfmisc_1(k2_zfmisc_1(A_860,B_861))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_14836,plain,(
    ! [C_865] :
      ( v1_relat_1(C_865)
      | ~ m1_subset_1(C_865,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14717,c_14775])).

tff(c_14853,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14720,c_14836])).

tff(c_17949,plain,(
    ! [A_1027,B_1028,C_1029] :
      ( k2_relset_1(A_1027,B_1028,C_1029) = k2_relat_1(C_1029)
      | ~ m1_subset_1(C_1029,k1_zfmisc_1(k2_zfmisc_1(A_1027,B_1028))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_18015,plain,(
    ! [C_1036] :
      ( k2_relset_1('#skF_2','#skF_3',C_1036) = k2_relat_1(C_1036)
      | ~ m1_subset_1(C_1036,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14717,c_17949])).

tff(c_18021,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14720,c_18015])).

tff(c_18033,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_18021])).

tff(c_15344,plain,(
    ! [A_918,B_919,C_920] :
      ( k2_relset_1(A_918,B_919,C_920) = k2_relat_1(C_920)
      | ~ m1_subset_1(C_920,k1_zfmisc_1(k2_zfmisc_1(A_918,B_919))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_15457,plain,(
    ! [C_935] :
      ( k2_relset_1('#skF_2','#skF_3',C_935) = k2_relat_1(C_935)
      | ~ m1_subset_1(C_935,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14717,c_15344])).

tff(c_15463,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14720,c_15457])).

tff(c_15475,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_15463])).

tff(c_15068,plain,(
    ! [A_889,B_890,C_891] :
      ( k1_relset_1(A_889,B_890,C_891) = k1_relat_1(C_891)
      | ~ m1_subset_1(C_891,k1_zfmisc_1(k2_zfmisc_1(A_889,B_890))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_15092,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_11313,c_15068])).

tff(c_17330,plain,(
    ! [B_1005,C_1006,A_1007] :
      ( k1_xboole_0 = B_1005
      | v1_funct_2(C_1006,A_1007,B_1005)
      | k1_relset_1(A_1007,B_1005,C_1006) != A_1007
      | ~ m1_subset_1(C_1006,k1_zfmisc_1(k2_zfmisc_1(A_1007,B_1005))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_17342,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_11313,c_17330])).

tff(c_17362,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15092,c_17342])).

tff(c_17363,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_11312,c_17362])).

tff(c_17370,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_17363])).

tff(c_17373,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_17370])).

tff(c_17376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14853,c_106,c_100,c_15475,c_17373])).

tff(c_17377,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17363])).

tff(c_17415,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17377,c_327])).

tff(c_17419,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17377,c_17377,c_14])).

tff(c_14985,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11344])).

tff(c_17677,plain,(
    ~ r1_tarski('#skF_2',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17419,c_14985])).

tff(c_17683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17415,c_17677])).

tff(c_17684,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_11344])).

tff(c_18091,plain,(
    ! [A_1037,B_1038,C_1039] :
      ( k1_relset_1(A_1037,B_1038,C_1039) = k1_relat_1(C_1039)
      | ~ m1_subset_1(C_1039,k1_zfmisc_1(k2_zfmisc_1(A_1037,B_1038))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_18560,plain,(
    ! [A_1080,B_1081,A_1082] :
      ( k1_relset_1(A_1080,B_1081,A_1082) = k1_relat_1(A_1082)
      | ~ r1_tarski(A_1082,k2_zfmisc_1(A_1080,B_1081)) ) ),
    inference(resolution,[status(thm)],[c_22,c_18091])).

tff(c_18598,plain,(
    ! [A_1083,B_1084] : k1_relset_1(A_1083,B_1084,k2_zfmisc_1(A_1083,B_1084)) = k1_relat_1(k2_zfmisc_1(A_1083,B_1084)) ),
    inference(resolution,[status(thm)],[c_10,c_18560])).

tff(c_18607,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17684,c_18598])).

tff(c_18619,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17684,c_18607])).

tff(c_19780,plain,(
    ! [B_1127,C_1128,A_1129] :
      ( k1_xboole_0 = B_1127
      | v1_funct_2(C_1128,A_1129,B_1127)
      | k1_relset_1(A_1129,B_1127,C_1128) != A_1129
      | ~ m1_subset_1(C_1128,k1_zfmisc_1(k2_zfmisc_1(A_1129,B_1127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_19792,plain,(
    ! [C_1128] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_1128,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_1128) != '#skF_2'
      | ~ m1_subset_1(C_1128,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14717,c_19780])).

tff(c_19892,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_19792])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14725,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_14717,c_12])).

tff(c_14774,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14725])).

tff(c_19921,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19892,c_14774])).

tff(c_20257,plain,(
    ! [A_1144] : k2_zfmisc_1(A_1144,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19892,c_19892,c_14])).

tff(c_18141,plain,(
    ! [C_1042] :
      ( k1_relset_1('#skF_2','#skF_3',C_1042) = k1_relat_1(C_1042)
      | ~ m1_subset_1(C_1042,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14717,c_18091])).

tff(c_18157,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14720,c_18141])).

tff(c_18794,plain,(
    ! [B_1092,C_1093,A_1094] :
      ( k1_xboole_0 = B_1092
      | v1_funct_2(C_1093,A_1094,B_1092)
      | k1_relset_1(A_1094,B_1092,C_1093) != A_1094
      | ~ m1_subset_1(C_1093,k1_zfmisc_1(k2_zfmisc_1(A_1094,B_1092))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_18806,plain,(
    ! [C_1093] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_1093,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_1093) != '#skF_2'
      | ~ m1_subset_1(C_1093,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14717,c_18794])).

tff(c_18902,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18806])).

tff(c_18940,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18902,c_327])).

tff(c_18944,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18902,c_18902,c_14])).

tff(c_17881,plain,(
    ! [A_1023] :
      ( m1_subset_1(A_1023,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1023),k2_relat_1(A_1023))))
      | ~ v1_funct_1(A_1023)
      | ~ v1_relat_1(A_1023) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_17901,plain,(
    ! [A_1023] :
      ( r1_tarski(A_1023,k2_zfmisc_1(k1_relat_1(A_1023),k2_relat_1(A_1023)))
      | ~ v1_funct_1(A_1023)
      | ~ v1_relat_1(A_1023) ) ),
    inference(resolution,[status(thm)],[c_17881,c_20])).

tff(c_18040,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18033,c_17901])).

tff(c_18053,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14853,c_106,c_18040])).

tff(c_18072,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_18053,c_6])).

tff(c_18793,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18072])).

tff(c_19261,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18944,c_18793])).

tff(c_19267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18940,c_19261])).

tff(c_19269,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18806])).

tff(c_19312,plain,(
    ! [B_1107,A_1108,C_1109] :
      ( k1_xboole_0 = B_1107
      | k1_relset_1(A_1108,B_1107,C_1109) = A_1108
      | ~ v1_funct_2(C_1109,A_1108,B_1107)
      | ~ m1_subset_1(C_1109,k1_zfmisc_1(k2_zfmisc_1(A_1108,B_1107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_19324,plain,(
    ! [C_1109] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_1109) = '#skF_2'
      | ~ v1_funct_2(C_1109,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_1109,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14717,c_19312])).

tff(c_19656,plain,(
    ! [C_1126] :
      ( k1_relset_1('#skF_2','#skF_3',C_1126) = '#skF_2'
      | ~ v1_funct_2(C_1126,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_1126,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_19269,c_19324])).

tff(c_19662,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_14720,c_19656])).

tff(c_19676,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_18157,c_19662])).

tff(c_19682,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19676,c_18793])).

tff(c_19694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14717,c_19682])).

tff(c_19695,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18072])).

tff(c_20264,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_20257,c_19695])).

tff(c_20306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19921,c_20264])).

tff(c_20308,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_19792])).

tff(c_334,plain,(
    ! [A_87,B_88] : m1_subset_1('#skF_1'(A_87,B_88),k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_351,plain,(
    ! [B_91] : m1_subset_1('#skF_1'(k1_xboole_0,B_91),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_334])).

tff(c_355,plain,(
    ! [B_91] : r1_tarski('#skF_1'(k1_xboole_0,B_91),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_351,c_20])).

tff(c_11334,plain,(
    ! [B_91] :
      ( '#skF_1'(k1_xboole_0,B_91) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,'#skF_1'(k1_xboole_0,B_91)) ) ),
    inference(resolution,[status(thm)],[c_355,c_11328])).

tff(c_11347,plain,(
    ! [B_91] : '#skF_1'(k1_xboole_0,B_91) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_11334])).

tff(c_18125,plain,(
    ! [A_1037,B_1038] : k1_relset_1(A_1037,B_1038,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_18091])).

tff(c_78,plain,(
    ! [A_40,B_41] : v1_funct_2('#skF_1'(A_40,B_41),A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_74,plain,(
    ! [B_38,C_39] :
      ( k1_relset_1(k1_xboole_0,B_38,C_39) = k1_xboole_0
      | ~ v1_funct_2(C_39,k1_xboole_0,B_38)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_18304,plain,(
    ! [B_1064,C_1065] :
      ( k1_relset_1(k1_xboole_0,B_1064,C_1065) = k1_xboole_0
      | ~ v1_funct_2(C_1065,k1_xboole_0,B_1064)
      | ~ m1_subset_1(C_1065,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_74])).

tff(c_18312,plain,(
    ! [B_41] :
      ( k1_relset_1(k1_xboole_0,B_41,'#skF_1'(k1_xboole_0,B_41)) = k1_xboole_0
      | ~ m1_subset_1('#skF_1'(k1_xboole_0,B_41),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_78,c_18304])).

tff(c_18321,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11347,c_18125,c_11347,c_18312])).

tff(c_18322,plain,(
    ! [A_1037,B_1038] : k1_relset_1(A_1037,B_1038,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18321,c_18125])).

tff(c_19809,plain,(
    ! [B_1127,A_1129] :
      ( k1_xboole_0 = B_1127
      | v1_funct_2(k1_xboole_0,A_1129,B_1127)
      | k1_relset_1(A_1129,B_1127,k1_xboole_0) != A_1129 ) ),
    inference(resolution,[status(thm)],[c_18,c_19780])).

tff(c_19816,plain,(
    ! [B_1127,A_1129] :
      ( k1_xboole_0 = B_1127
      | v1_funct_2(k1_xboole_0,A_1129,B_1127)
      | k1_xboole_0 != A_1129 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18322,c_19809])).

tff(c_20656,plain,(
    ! [B_1155,A_1156,C_1157] :
      ( k1_xboole_0 = B_1155
      | k1_relset_1(A_1156,B_1155,C_1157) = A_1156
      | ~ v1_funct_2(C_1157,A_1156,B_1155)
      | ~ m1_subset_1(C_1157,k1_zfmisc_1(k2_zfmisc_1(A_1156,B_1155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_20668,plain,(
    ! [C_1157] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_1157) = '#skF_2'
      | ~ v1_funct_2(C_1157,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_1157,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14717,c_20656])).

tff(c_20937,plain,(
    ! [C_1171] :
      ( k1_relset_1('#skF_2','#skF_3',C_1171) = '#skF_2'
      | ~ v1_funct_2(C_1171,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_1171,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20308,c_20668])).

tff(c_20954,plain,
    ( k1_relset_1('#skF_2','#skF_3',k1_xboole_0) = '#skF_2'
    | ~ v1_funct_2(k1_xboole_0,'#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_20937])).

tff(c_20965,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2(k1_xboole_0,'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18322,c_20954])).

tff(c_21170,plain,(
    ~ v1_funct_2(k1_xboole_0,'#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20965])).

tff(c_21173,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(resolution,[status(thm)],[c_19816,c_21170])).

tff(c_21176,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_20308,c_21173])).

tff(c_21177,plain,(
    ! [B_1175,A_1176,A_1177] :
      ( k1_xboole_0 = B_1175
      | v1_funct_2(A_1176,A_1177,B_1175)
      | k1_relset_1(A_1177,B_1175,A_1176) != A_1177
      | ~ r1_tarski(A_1176,k2_zfmisc_1(A_1177,B_1175)) ) ),
    inference(resolution,[status(thm)],[c_22,c_19780])).

tff(c_21186,plain,(
    ! [A_1176] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(A_1176,'#skF_3','#skF_2')
      | k1_relset_1('#skF_3','#skF_2',A_1176) != '#skF_3'
      | ~ r1_tarski(A_1176,k2_funct_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17684,c_21177])).

tff(c_21388,plain,(
    ! [A_1183] :
      ( v1_funct_2(A_1183,'#skF_3','#skF_2')
      | k1_relset_1('#skF_3','#skF_2',A_1183) != '#skF_3'
      | ~ r1_tarski(A_1183,k2_funct_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_21176,c_21186])).

tff(c_21399,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_21388])).

tff(c_21405,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18619,c_21399])).

tff(c_21406,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_11312,c_21405])).

tff(c_21409,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_21406])).

tff(c_21412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14853,c_106,c_100,c_18033,c_21409])).

tff(c_21413,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_20965])).

tff(c_21451,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21413,c_14774])).

tff(c_21836,plain,(
    ! [B_1196] : k2_zfmisc_1('#skF_2',B_1196) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21413,c_21413,c_16])).

tff(c_21873,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_21836,c_14717])).

tff(c_21891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21451,c_21873])).

tff(c_21893,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14725])).

tff(c_345,plain,(
    ! [A_89] : m1_subset_1('#skF_1'(A_89,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_334])).

tff(c_349,plain,(
    ! [A_89] : r1_tarski('#skF_1'(A_89,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_345,c_20])).

tff(c_11336,plain,(
    ! [A_89] :
      ( '#skF_1'(A_89,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,'#skF_1'(A_89,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_349,c_11328])).

tff(c_11415,plain,(
    ! [A_633] : '#skF_1'(A_633,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_11336])).

tff(c_11429,plain,(
    ! [A_633] : v1_funct_2(k1_xboole_0,A_633,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11415,c_78])).

tff(c_21895,plain,(
    ! [A_633] : v1_funct_2('#skF_4',A_633,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21893,c_21893,c_11429])).

tff(c_21902,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21893,c_327])).

tff(c_21906,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21893,c_21893,c_14])).

tff(c_21986,plain,(
    ! [B_1204] : '#skF_1'('#skF_4',B_1204) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21893,c_21893,c_11347])).

tff(c_21997,plain,(
    ! [B_1204] : v1_funct_2('#skF_4','#skF_4',B_1204) ),
    inference(superposition,[status(thm),theory(equality)],[c_21986,c_78])).

tff(c_21907,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21893,c_21893,c_16])).

tff(c_21892,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14725])).

tff(c_22107,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21893,c_21893,c_21892])).

tff(c_22108,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22107])).

tff(c_22112,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22108,c_11318])).

tff(c_22120,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21907,c_22112])).

tff(c_22156,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22120,c_6])).

tff(c_22159,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21902,c_22156])).

tff(c_22114,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22108,c_11312])).

tff(c_22225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21997,c_22159,c_22114])).

tff(c_22226,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22107])).

tff(c_22231,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22226,c_11318])).

tff(c_22239,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21906,c_22231])).

tff(c_22246,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22239,c_6])).

tff(c_22249,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21902,c_22246])).

tff(c_22233,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22226,c_11312])).

tff(c_22333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21895,c_22249,c_22233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:34:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.42/4.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.68/4.52  
% 10.68/4.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.68/4.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 10.68/4.52  
% 10.68/4.52  %Foreground sorts:
% 10.68/4.52  
% 10.68/4.52  
% 10.68/4.52  %Background operators:
% 10.68/4.52  
% 10.68/4.52  
% 10.68/4.52  %Foreground operators:
% 10.68/4.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.68/4.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.68/4.52  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.68/4.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.68/4.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.68/4.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.68/4.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.68/4.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.68/4.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.68/4.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.68/4.52  tff('#skF_2', type, '#skF_2': $i).
% 10.68/4.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.68/4.52  tff('#skF_3', type, '#skF_3': $i).
% 10.68/4.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.68/4.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.68/4.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.68/4.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.68/4.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.68/4.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.68/4.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.68/4.52  tff('#skF_4', type, '#skF_4': $i).
% 10.68/4.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.68/4.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.68/4.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.68/4.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.68/4.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.68/4.52  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 10.68/4.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.68/4.52  
% 10.68/4.56  tff(f_211, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 10.68/4.56  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.68/4.56  tff(f_153, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.68/4.56  tff(f_141, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 10.68/4.56  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.68/4.56  tff(f_104, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.68/4.56  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 10.68/4.56  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.68/4.56  tff(f_149, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.68/4.56  tff(f_171, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.68/4.56  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 10.68/4.56  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 10.68/4.56  tff(f_131, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 10.68/4.56  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 10.68/4.56  tff(f_120, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 10.68/4.56  tff(f_194, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 10.68/4.56  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 10.68/4.56  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.68/4.56  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.68/4.56  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 10.68/4.56  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_relat_1)).
% 10.68/4.56  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.68/4.56  tff(f_184, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 10.68/4.56  tff(c_102, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_211])).
% 10.68/4.56  tff(c_11482, plain, (![C_639, A_640, B_641]: (v1_relat_1(C_639) | ~m1_subset_1(C_639, k1_zfmisc_1(k2_zfmisc_1(A_640, B_641))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.68/4.56  tff(c_11508, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_11482])).
% 10.68/4.56  tff(c_106, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_211])).
% 10.68/4.56  tff(c_100, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_211])).
% 10.68/4.56  tff(c_98, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_211])).
% 10.68/4.56  tff(c_12762, plain, (![A_751, B_752, C_753]: (k2_relset_1(A_751, B_752, C_753)=k2_relat_1(C_753) | ~m1_subset_1(C_753, k1_zfmisc_1(k2_zfmisc_1(A_751, B_752))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.68/4.56  tff(c_12778, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_12762])).
% 10.68/4.56  tff(c_12793, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_12778])).
% 10.68/4.56  tff(c_58, plain, (![A_27]: (k1_relat_1(k2_funct_1(A_27))=k2_relat_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.68/4.56  tff(c_22, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.68/4.56  tff(c_46, plain, (![A_19]: (v1_funct_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/4.56  tff(c_96, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 10.68/4.56  tff(c_242, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_96])).
% 10.68/4.56  tff(c_245, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_242])).
% 10.68/4.56  tff(c_248, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_245])).
% 10.68/4.56  tff(c_291, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.68/4.56  tff(c_301, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_291])).
% 10.68/4.56  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248, c_301])).
% 10.68/4.56  tff(c_317, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_96])).
% 10.68/4.56  tff(c_356, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_317])).
% 10.68/4.56  tff(c_361, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_356])).
% 10.68/4.56  tff(c_5261, plain, (![A_344]: (k4_relat_1(A_344)=k2_funct_1(A_344) | ~v2_funct_1(A_344) | ~v1_funct_1(A_344) | ~v1_relat_1(A_344))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.68/4.56  tff(c_5267, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_5261])).
% 10.68/4.56  tff(c_5271, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_5267])).
% 10.68/4.56  tff(c_5272, plain, (~v1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_5271])).
% 10.68/4.56  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.68/4.56  tff(c_104, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_211])).
% 10.68/4.56  tff(c_963, plain, (![A_155, B_156, C_157]: (k1_relset_1(A_155, B_156, C_157)=k1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.68/4.56  tff(c_994, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_963])).
% 10.68/4.56  tff(c_4701, plain, (![B_317, A_318, C_319]: (k1_xboole_0=B_317 | k1_relset_1(A_318, B_317, C_319)=A_318 | ~v1_funct_2(C_319, A_318, B_317) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_318, B_317))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.56  tff(c_4717, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_102, c_4701])).
% 10.68/4.56  tff(c_4735, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_994, c_4717])).
% 10.68/4.56  tff(c_4739, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_4735])).
% 10.68/4.56  tff(c_521, plain, (![C_107, A_108, B_109]: (v1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.68/4.56  tff(c_543, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_521])).
% 10.68/4.56  tff(c_48, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.68/4.56  tff(c_318, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_96])).
% 10.68/4.56  tff(c_770, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.68/4.56  tff(c_780, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_770])).
% 10.68/4.56  tff(c_794, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_780])).
% 10.68/4.56  tff(c_34, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.68/4.56  tff(c_803, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_794, c_34])).
% 10.68/4.56  tff(c_809, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_543, c_803])).
% 10.68/4.56  tff(c_1221, plain, (![B_181, A_182]: (k9_relat_1(B_181, k10_relat_1(B_181, A_182))=A_182 | ~r1_tarski(A_182, k2_relat_1(B_181)) | ~v1_funct_1(B_181) | ~v1_relat_1(B_181))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.68/4.56  tff(c_1225, plain, (![A_182]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_182))=A_182 | ~r1_tarski(A_182, '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_794, c_1221])).
% 10.68/4.56  tff(c_1240, plain, (![A_183]: (k9_relat_1('#skF_4', k10_relat_1('#skF_4', A_183))=A_183 | ~r1_tarski(A_183, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_106, c_1225])).
% 10.68/4.56  tff(c_1249, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_809, c_1240])).
% 10.68/4.56  tff(c_1257, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1249])).
% 10.68/4.56  tff(c_1347, plain, (![A_186, B_187]: (k9_relat_1(k2_funct_1(A_186), k9_relat_1(A_186, B_187))=B_187 | ~r1_tarski(B_187, k1_relat_1(A_186)) | ~v2_funct_1(A_186) | ~v1_funct_1(A_186) | ~v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.68/4.56  tff(c_1365, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1257, c_1347])).
% 10.68/4.56  tff(c_1384, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_543, c_106, c_100, c_10, c_1365])).
% 10.68/4.56  tff(c_54, plain, (![A_24, B_26]: (k9_relat_1(k2_funct_1(A_24), k9_relat_1(A_24, B_26))=B_26 | ~r1_tarski(B_26, k1_relat_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.68/4.56  tff(c_1398, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1384, c_54])).
% 10.68/4.56  tff(c_1402, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'))='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_1398])).
% 10.68/4.56  tff(c_1755, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1402])).
% 10.68/4.56  tff(c_1758, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1755])).
% 10.68/4.56  tff(c_1762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_543, c_106, c_1758])).
% 10.68/4.56  tff(c_1764, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1402])).
% 10.68/4.56  tff(c_1795, plain, (![B_211, A_212, C_213]: (k1_xboole_0=B_211 | k1_relset_1(A_212, B_211, C_213)=A_212 | ~v1_funct_2(C_213, A_212, B_211) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_212, B_211))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.56  tff(c_1811, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_102, c_1795])).
% 10.68/4.56  tff(c_1832, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_994, c_1811])).
% 10.68/4.56  tff(c_1836, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1832])).
% 10.68/4.56  tff(c_32, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.68/4.56  tff(c_1871, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1836, c_32])).
% 10.68/4.56  tff(c_1885, plain, (k9_relat_1('#skF_4', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_543, c_794, c_1871])).
% 10.68/4.56  tff(c_673, plain, (![A_131]: (k2_relat_1(k2_funct_1(A_131))=k1_relat_1(A_131) | ~v2_funct_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.68/4.56  tff(c_3537, plain, (![A_272]: (k10_relat_1(k2_funct_1(A_272), k1_relat_1(A_272))=k1_relat_1(k2_funct_1(A_272)) | ~v1_relat_1(k2_funct_1(A_272)) | ~v2_funct_1(A_272) | ~v1_funct_1(A_272) | ~v1_relat_1(A_272))), inference(superposition, [status(thm), theory('equality')], [c_673, c_34])).
% 10.68/4.56  tff(c_3561, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1836, c_3537])).
% 10.68/4.56  tff(c_3580, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_106, c_100, c_1764, c_3561])).
% 10.68/4.56  tff(c_52, plain, (![B_23, A_22]: (k10_relat_1(k2_funct_1(B_23), A_22)=k9_relat_1(B_23, A_22) | ~v2_funct_1(B_23) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.68/4.56  tff(c_3588, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k9_relat_1('#skF_4', '#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3580, c_52])).
% 10.68/4.56  tff(c_3595, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_543, c_106, c_100, c_1885, c_3588])).
% 10.68/4.56  tff(c_1903, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1885, c_54])).
% 10.68/4.56  tff(c_1907, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_543, c_106, c_100, c_10, c_1836, c_1903])).
% 10.68/4.56  tff(c_3627, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3595, c_32])).
% 10.68/4.56  tff(c_3650, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_1907, c_3627])).
% 10.68/4.56  tff(c_884, plain, (![A_151]: (m1_subset_1(A_151, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_151), k2_relat_1(A_151)))) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.68/4.56  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.68/4.56  tff(c_911, plain, (![A_151]: (r1_tarski(A_151, k2_zfmisc_1(k1_relat_1(A_151), k2_relat_1(A_151))) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(resolution, [status(thm)], [c_884, c_20])).
% 10.68/4.56  tff(c_3690, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3650, c_911])).
% 10.68/4.56  tff(c_3723, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_318, c_3595, c_3690])).
% 10.68/4.56  tff(c_3725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_361, c_3723])).
% 10.68/4.56  tff(c_3726, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1832])).
% 10.68/4.56  tff(c_18, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.68/4.56  tff(c_319, plain, (![A_82, B_83]: (r1_tarski(A_82, B_83) | ~m1_subset_1(A_82, k1_zfmisc_1(B_83)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.68/4.56  tff(c_327, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_18, c_319])).
% 10.68/4.56  tff(c_3765, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_327])).
% 10.68/4.56  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.68/4.56  tff(c_3769, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3726, c_3726, c_14])).
% 10.68/4.56  tff(c_898, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_794, c_884])).
% 10.68/4.56  tff(c_913, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_106, c_898])).
% 10.68/4.56  tff(c_932, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_913, c_20])).
% 10.68/4.56  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.68/4.56  tff(c_944, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_932, c_6])).
% 10.68/4.56  tff(c_1011, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_944])).
% 10.68/4.56  tff(c_4060, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3769, c_1011])).
% 10.68/4.56  tff(c_4070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3765, c_4060])).
% 10.68/4.56  tff(c_4071, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_944])).
% 10.68/4.56  tff(c_4748, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4739, c_4071])).
% 10.68/4.56  tff(c_326, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_102, c_319])).
% 10.68/4.56  tff(c_371, plain, (![B_95, A_96]: (B_95=A_96 | ~r1_tarski(B_95, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.68/4.56  tff(c_391, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_326, c_371])).
% 10.68/4.56  tff(c_449, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_391])).
% 10.68/4.56  tff(c_4800, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4748, c_449])).
% 10.68/4.56  tff(c_4805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_4800])).
% 10.68/4.56  tff(c_4806, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4735])).
% 10.68/4.56  tff(c_4843, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_4806, c_327])).
% 10.68/4.56  tff(c_4847, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4806, c_4806, c_14])).
% 10.68/4.56  tff(c_5091, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4847, c_449])).
% 10.68/4.56  tff(c_5096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4843, c_5091])).
% 10.68/4.56  tff(c_5097, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_391])).
% 10.68/4.56  tff(c_5100, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5097, c_102])).
% 10.68/4.56  tff(c_5213, plain, (![C_339, A_340, B_341]: (v1_relat_1(C_339) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_340, B_341))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.68/4.56  tff(c_5273, plain, (![C_345]: (v1_relat_1(C_345) | ~m1_subset_1(C_345, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5097, c_5213])).
% 10.68/4.56  tff(c_5279, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5100, c_5273])).
% 10.68/4.56  tff(c_5293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5272, c_5279])).
% 10.68/4.56  tff(c_5295, plain, (v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_5271])).
% 10.68/4.56  tff(c_5634, plain, (![A_380, B_381, C_382]: (k1_relset_1(A_380, B_381, C_382)=k1_relat_1(C_382) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_380, B_381))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.68/4.56  tff(c_5686, plain, (![C_389]: (k1_relset_1('#skF_2', '#skF_3', C_389)=k1_relat_1(C_389) | ~m1_subset_1(C_389, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5097, c_5634])).
% 10.68/4.56  tff(c_5702, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5100, c_5686])).
% 10.68/4.56  tff(c_7914, plain, (![B_500, A_501, C_502]: (k1_xboole_0=B_500 | k1_relset_1(A_501, B_500, C_502)=A_501 | ~v1_funct_2(C_502, A_501, B_500) | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(A_501, B_500))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.56  tff(c_7923, plain, (![C_502]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_502)='#skF_2' | ~v1_funct_2(C_502, '#skF_2', '#skF_3') | ~m1_subset_1(C_502, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5097, c_7914])).
% 10.68/4.56  tff(c_8040, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_7923])).
% 10.68/4.56  tff(c_5196, plain, (![B_336, A_337]: (k1_xboole_0=B_336 | k1_xboole_0=A_337 | k2_zfmisc_1(A_337, B_336)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.68/4.56  tff(c_5199, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5097, c_5196])).
% 10.68/4.56  tff(c_5210, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_5199])).
% 10.68/4.56  tff(c_8071, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8040, c_5210])).
% 10.68/4.56  tff(c_8486, plain, (![A_521]: (k2_zfmisc_1(A_521, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8040, c_8040, c_14])).
% 10.68/4.56  tff(c_6342, plain, (![B_437, A_438, C_439]: (k1_xboole_0=B_437 | k1_relset_1(A_438, B_437, C_439)=A_438 | ~v1_funct_2(C_439, A_438, B_437) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(A_438, B_437))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.56  tff(c_6351, plain, (![C_439]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_439)='#skF_2' | ~v1_funct_2(C_439, '#skF_2', '#skF_3') | ~m1_subset_1(C_439, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5097, c_6342])).
% 10.68/4.56  tff(c_6383, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_6351])).
% 10.68/4.56  tff(c_6417, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_6383, c_327])).
% 10.68/4.56  tff(c_6421, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6383, c_6383, c_14])).
% 10.68/4.56  tff(c_5536, plain, (![A_371, B_372, C_373]: (k2_relset_1(A_371, B_372, C_373)=k2_relat_1(C_373) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_371, B_372))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.68/4.56  tff(c_5568, plain, (![C_376]: (k2_relset_1('#skF_2', '#skF_3', C_376)=k2_relat_1(C_376) | ~m1_subset_1(C_376, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5097, c_5536])).
% 10.68/4.56  tff(c_5574, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5100, c_5568])).
% 10.68/4.56  tff(c_5585, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_5574])).
% 10.68/4.56  tff(c_5864, plain, (![A_410]: (m1_subset_1(A_410, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_410), k2_relat_1(A_410)))) | ~v1_funct_1(A_410) | ~v1_relat_1(A_410))), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.68/4.56  tff(c_5881, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5585, c_5864])).
% 10.68/4.56  tff(c_5897, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5295, c_106, c_5881])).
% 10.68/4.56  tff(c_5920, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_5897, c_20])).
% 10.68/4.56  tff(c_5936, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_5920, c_6])).
% 10.68/4.56  tff(c_6058, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_5936])).
% 10.68/4.56  tff(c_6710, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6421, c_6058])).
% 10.68/4.56  tff(c_6716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6417, c_6710])).
% 10.68/4.56  tff(c_7297, plain, (![C_478]: (k1_relset_1('#skF_2', '#skF_3', C_478)='#skF_2' | ~v1_funct_2(C_478, '#skF_2', '#skF_3') | ~m1_subset_1(C_478, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_6351])).
% 10.68/4.56  tff(c_7303, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_5100, c_7297])).
% 10.68/4.56  tff(c_7317, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_5702, c_7303])).
% 10.68/4.56  tff(c_7324, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7317, c_6058])).
% 10.68/4.56  tff(c_7335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_5097, c_7324])).
% 10.68/4.56  tff(c_7336, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_5936])).
% 10.68/4.56  tff(c_8496, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_8486, c_7336])).
% 10.68/4.56  tff(c_8542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8071, c_8496])).
% 10.68/4.56  tff(c_8775, plain, (![C_529]: (k1_relset_1('#skF_2', '#skF_3', C_529)='#skF_2' | ~v1_funct_2(C_529, '#skF_2', '#skF_3') | ~m1_subset_1(C_529, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_7923])).
% 10.68/4.56  tff(c_8784, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_5100, c_8775])).
% 10.68/4.56  tff(c_8800, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_5702, c_8784])).
% 10.68/4.56  tff(c_8851, plain, (k9_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8800, c_32])).
% 10.68/4.56  tff(c_8865, plain, (k9_relat_1('#skF_4', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5295, c_5585, c_8851])).
% 10.68/4.56  tff(c_8879, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8865, c_54])).
% 10.68/4.56  tff(c_8883, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5295, c_106, c_100, c_10, c_8800, c_8879])).
% 10.68/4.56  tff(c_8995, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8883, c_54])).
% 10.68/4.56  tff(c_8999, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_4')), '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_8995])).
% 10.68/4.56  tff(c_9959, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8999])).
% 10.68/4.56  tff(c_9962, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_9959])).
% 10.68/4.56  tff(c_9966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5295, c_106, c_9962])).
% 10.68/4.56  tff(c_9968, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8999])).
% 10.68/4.56  tff(c_5507, plain, (![A_367]: (k2_relat_1(k2_funct_1(A_367))=k1_relat_1(A_367) | ~v2_funct_1(A_367) | ~v1_funct_1(A_367) | ~v1_relat_1(A_367))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.68/4.56  tff(c_10492, plain, (![A_580]: (k10_relat_1(k2_funct_1(A_580), k1_relat_1(A_580))=k1_relat_1(k2_funct_1(A_580)) | ~v1_relat_1(k2_funct_1(A_580)) | ~v2_funct_1(A_580) | ~v1_funct_1(A_580) | ~v1_relat_1(A_580))), inference(superposition, [status(thm), theory('equality')], [c_5507, c_34])).
% 10.68/4.56  tff(c_10519, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8800, c_10492])).
% 10.68/4.56  tff(c_10541, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')=k1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5295, c_106, c_100, c_9968, c_10519])).
% 10.68/4.56  tff(c_10551, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k9_relat_1('#skF_4', '#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10541, c_52])).
% 10.68/4.56  tff(c_10558, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5295, c_106, c_100, c_8865, c_10551])).
% 10.68/4.56  tff(c_10590, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10558, c_32])).
% 10.68/4.56  tff(c_10613, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9968, c_8883, c_10590])).
% 10.68/4.56  tff(c_5895, plain, (![A_410]: (r1_tarski(A_410, k2_zfmisc_1(k1_relat_1(A_410), k2_relat_1(A_410))) | ~v1_funct_1(A_410) | ~v1_relat_1(A_410))), inference(resolution, [status(thm)], [c_5864, c_20])).
% 10.68/4.56  tff(c_10655, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10613, c_5895])).
% 10.68/4.56  tff(c_10688, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9968, c_318, c_10558, c_10655])).
% 10.68/4.56  tff(c_10690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_361, c_10688])).
% 10.68/4.56  tff(c_10692, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5199])).
% 10.68/4.56  tff(c_10701, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_10692, c_327])).
% 10.68/4.56  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.68/4.56  tff(c_125, plain, (![A_47]: (v1_relat_1(A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.68/4.56  tff(c_129, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_125])).
% 10.68/4.56  tff(c_10708, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10692, c_129])).
% 10.68/4.56  tff(c_161, plain, (![A_58]: (v1_xboole_0(k4_relat_1(A_58)) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.68/4.56  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 10.68/4.56  tff(c_176, plain, (![A_62]: (k4_relat_1(A_62)=k1_xboole_0 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_161, c_4])).
% 10.68/4.56  tff(c_184, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_176])).
% 10.68/4.56  tff(c_10703, plain, (k4_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10692, c_10692, c_184])).
% 10.68/4.56  tff(c_11295, plain, (![A_623]: (k4_relat_1(A_623)=k2_funct_1(A_623) | ~v2_funct_1(A_623) | ~v1_funct_1(A_623) | ~v1_relat_1(A_623))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.68/4.56  tff(c_11301, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_11295])).
% 10.68/4.56  tff(c_11305, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10708, c_106, c_10703, c_11301])).
% 10.68/4.56  tff(c_10705, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10692, c_10692, c_14])).
% 10.68/4.56  tff(c_11028, plain, (![A_607]: (k4_relat_1(A_607)=k2_funct_1(A_607) | ~v2_funct_1(A_607) | ~v1_funct_1(A_607) | ~v1_relat_1(A_607))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.68/4.56  tff(c_11034, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_11028])).
% 10.68/4.56  tff(c_11038, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10708, c_106, c_10703, c_11034])).
% 10.68/4.56  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.68/4.56  tff(c_10706, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10692, c_10692, c_16])).
% 10.68/4.56  tff(c_10691, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5199])).
% 10.68/4.56  tff(c_10753, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10692, c_10692, c_10691])).
% 10.68/4.56  tff(c_10754, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_10753])).
% 10.68/4.56  tff(c_10759, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10754, c_356])).
% 10.68/4.56  tff(c_10946, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10706, c_10759])).
% 10.68/4.56  tff(c_10950, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_22, c_10946])).
% 10.68/4.56  tff(c_11039, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11038, c_10950])).
% 10.68/4.56  tff(c_11044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_11039])).
% 10.68/4.56  tff(c_11045, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_10753])).
% 10.68/4.56  tff(c_11051, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11045, c_356])).
% 10.68/4.56  tff(c_11254, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10705, c_11051])).
% 10.68/4.56  tff(c_11258, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_22, c_11254])).
% 10.68/4.56  tff(c_11306, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11305, c_11258])).
% 10.68/4.56  tff(c_11311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10701, c_11306])).
% 10.68/4.56  tff(c_11312, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_317])).
% 10.68/4.56  tff(c_11765, plain, (![A_670, B_671, C_672]: (k2_relset_1(A_670, B_671, C_672)=k2_relat_1(C_672) | ~m1_subset_1(C_672, k1_zfmisc_1(k2_zfmisc_1(A_670, B_671))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.68/4.56  tff(c_11781, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_11765])).
% 10.68/4.56  tff(c_11797, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_11781])).
% 10.68/4.56  tff(c_11313, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_317])).
% 10.68/4.56  tff(c_11834, plain, (![A_675, B_676, C_677]: (k1_relset_1(A_675, B_676, C_677)=k1_relat_1(C_677) | ~m1_subset_1(C_677, k1_zfmisc_1(k2_zfmisc_1(A_675, B_676))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.68/4.56  tff(c_11862, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_11313, c_11834])).
% 10.68/4.56  tff(c_12214, plain, (![B_712, C_713, A_714]: (k1_xboole_0=B_712 | v1_funct_2(C_713, A_714, B_712) | k1_relset_1(A_714, B_712, C_713)!=A_714 | ~m1_subset_1(C_713, k1_zfmisc_1(k2_zfmisc_1(A_714, B_712))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.56  tff(c_12223, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_11313, c_12214])).
% 10.68/4.56  tff(c_12249, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11862, c_12223])).
% 10.68/4.56  tff(c_12250, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_11312, c_12249])).
% 10.68/4.56  tff(c_12259, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_12250])).
% 10.68/4.56  tff(c_12262, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_58, c_12259])).
% 10.68/4.56  tff(c_12265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11508, c_106, c_100, c_11797, c_12262])).
% 10.68/4.56  tff(c_12266, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_12250])).
% 10.68/4.56  tff(c_12300, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_327])).
% 10.68/4.56  tff(c_12304, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12266, c_12266, c_14])).
% 10.68/4.56  tff(c_11318, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_11313, c_20])).
% 10.68/4.56  tff(c_11328, plain, (![B_627, A_628]: (B_627=A_628 | ~r1_tarski(B_627, A_628) | ~r1_tarski(A_628, B_627))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.68/4.56  tff(c_11344, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4') | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_11318, c_11328])).
% 10.68/4.56  tff(c_11523, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_11344])).
% 10.68/4.56  tff(c_12414, plain, (~r1_tarski('#skF_2', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12304, c_11523])).
% 10.68/4.56  tff(c_12419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12300, c_12414])).
% 10.68/4.56  tff(c_12420, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_11344])).
% 10.68/4.56  tff(c_12437, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_12420, c_11313])).
% 10.68/4.56  tff(c_12861, plain, (![A_756, B_757, C_758]: (k1_relset_1(A_756, B_757, C_758)=k1_relat_1(C_758) | ~m1_subset_1(C_758, k1_zfmisc_1(k2_zfmisc_1(A_756, B_757))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.68/4.56  tff(c_13244, plain, (![C_798]: (k1_relset_1('#skF_3', '#skF_2', C_798)=k1_relat_1(C_798) | ~m1_subset_1(C_798, k1_zfmisc_1(k2_funct_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_12420, c_12861])).
% 10.68/4.56  tff(c_13261, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12437, c_13244])).
% 10.68/4.56  tff(c_13590, plain, (![B_815, C_816, A_817]: (k1_xboole_0=B_815 | v1_funct_2(C_816, A_817, B_815) | k1_relset_1(A_817, B_815, C_816)!=A_817 | ~m1_subset_1(C_816, k1_zfmisc_1(k2_zfmisc_1(A_817, B_815))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.56  tff(c_13599, plain, (![C_816]: (k1_xboole_0='#skF_2' | v1_funct_2(C_816, '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', C_816)!='#skF_3' | ~m1_subset_1(C_816, k1_zfmisc_1(k2_funct_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_12420, c_13590])).
% 10.68/4.56  tff(c_13697, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_13599])).
% 10.68/4.56  tff(c_13735, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_13697, c_327])).
% 10.68/4.56  tff(c_13740, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13697, c_13697, c_16])).
% 10.68/4.56  tff(c_11351, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_326, c_11328])).
% 10.68/4.56  tff(c_11456, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_11351])).
% 10.68/4.56  tff(c_14170, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13740, c_11456])).
% 10.68/4.56  tff(c_14175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13735, c_14170])).
% 10.68/4.56  tff(c_14688, plain, (![C_854]: (v1_funct_2(C_854, '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', C_854)!='#skF_3' | ~m1_subset_1(C_854, k1_zfmisc_1(k2_funct_1('#skF_4'))))), inference(splitRight, [status(thm)], [c_13599])).
% 10.68/4.56  tff(c_14694, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_12437, c_14688])).
% 10.68/4.56  tff(c_14706, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13261, c_14694])).
% 10.68/4.56  tff(c_14707, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_11312, c_14706])).
% 10.68/4.56  tff(c_14713, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_58, c_14707])).
% 10.68/4.56  tff(c_14716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11508, c_106, c_100, c_12793, c_14713])).
% 10.68/4.56  tff(c_14717, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_11351])).
% 10.68/4.56  tff(c_14720, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14717, c_102])).
% 10.68/4.56  tff(c_14775, plain, (![C_859, A_860, B_861]: (v1_relat_1(C_859) | ~m1_subset_1(C_859, k1_zfmisc_1(k2_zfmisc_1(A_860, B_861))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.68/4.56  tff(c_14836, plain, (![C_865]: (v1_relat_1(C_865) | ~m1_subset_1(C_865, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_14717, c_14775])).
% 10.68/4.56  tff(c_14853, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14720, c_14836])).
% 10.68/4.56  tff(c_17949, plain, (![A_1027, B_1028, C_1029]: (k2_relset_1(A_1027, B_1028, C_1029)=k2_relat_1(C_1029) | ~m1_subset_1(C_1029, k1_zfmisc_1(k2_zfmisc_1(A_1027, B_1028))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.68/4.56  tff(c_18015, plain, (![C_1036]: (k2_relset_1('#skF_2', '#skF_3', C_1036)=k2_relat_1(C_1036) | ~m1_subset_1(C_1036, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_14717, c_17949])).
% 10.68/4.56  tff(c_18021, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14720, c_18015])).
% 10.68/4.56  tff(c_18033, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_18021])).
% 10.68/4.56  tff(c_15344, plain, (![A_918, B_919, C_920]: (k2_relset_1(A_918, B_919, C_920)=k2_relat_1(C_920) | ~m1_subset_1(C_920, k1_zfmisc_1(k2_zfmisc_1(A_918, B_919))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.68/4.56  tff(c_15457, plain, (![C_935]: (k2_relset_1('#skF_2', '#skF_3', C_935)=k2_relat_1(C_935) | ~m1_subset_1(C_935, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_14717, c_15344])).
% 10.68/4.56  tff(c_15463, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14720, c_15457])).
% 10.68/4.56  tff(c_15475, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_15463])).
% 10.68/4.56  tff(c_15068, plain, (![A_889, B_890, C_891]: (k1_relset_1(A_889, B_890, C_891)=k1_relat_1(C_891) | ~m1_subset_1(C_891, k1_zfmisc_1(k2_zfmisc_1(A_889, B_890))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.68/4.56  tff(c_15092, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_11313, c_15068])).
% 10.68/4.56  tff(c_17330, plain, (![B_1005, C_1006, A_1007]: (k1_xboole_0=B_1005 | v1_funct_2(C_1006, A_1007, B_1005) | k1_relset_1(A_1007, B_1005, C_1006)!=A_1007 | ~m1_subset_1(C_1006, k1_zfmisc_1(k2_zfmisc_1(A_1007, B_1005))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.57  tff(c_17342, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_11313, c_17330])).
% 10.68/4.57  tff(c_17362, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15092, c_17342])).
% 10.68/4.57  tff(c_17363, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_11312, c_17362])).
% 10.68/4.57  tff(c_17370, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_17363])).
% 10.68/4.57  tff(c_17373, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_58, c_17370])).
% 10.68/4.57  tff(c_17376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14853, c_106, c_100, c_15475, c_17373])).
% 10.68/4.57  tff(c_17377, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_17363])).
% 10.68/4.57  tff(c_17415, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_17377, c_327])).
% 10.68/4.57  tff(c_17419, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17377, c_17377, c_14])).
% 10.68/4.57  tff(c_14985, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_11344])).
% 10.68/4.57  tff(c_17677, plain, (~r1_tarski('#skF_2', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17419, c_14985])).
% 10.68/4.57  tff(c_17683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17415, c_17677])).
% 10.68/4.57  tff(c_17684, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_11344])).
% 10.68/4.57  tff(c_18091, plain, (![A_1037, B_1038, C_1039]: (k1_relset_1(A_1037, B_1038, C_1039)=k1_relat_1(C_1039) | ~m1_subset_1(C_1039, k1_zfmisc_1(k2_zfmisc_1(A_1037, B_1038))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.68/4.57  tff(c_18560, plain, (![A_1080, B_1081, A_1082]: (k1_relset_1(A_1080, B_1081, A_1082)=k1_relat_1(A_1082) | ~r1_tarski(A_1082, k2_zfmisc_1(A_1080, B_1081)))), inference(resolution, [status(thm)], [c_22, c_18091])).
% 10.68/4.57  tff(c_18598, plain, (![A_1083, B_1084]: (k1_relset_1(A_1083, B_1084, k2_zfmisc_1(A_1083, B_1084))=k1_relat_1(k2_zfmisc_1(A_1083, B_1084)))), inference(resolution, [status(thm)], [c_10, c_18560])).
% 10.68/4.57  tff(c_18607, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17684, c_18598])).
% 10.68/4.57  tff(c_18619, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17684, c_18607])).
% 10.68/4.57  tff(c_19780, plain, (![B_1127, C_1128, A_1129]: (k1_xboole_0=B_1127 | v1_funct_2(C_1128, A_1129, B_1127) | k1_relset_1(A_1129, B_1127, C_1128)!=A_1129 | ~m1_subset_1(C_1128, k1_zfmisc_1(k2_zfmisc_1(A_1129, B_1127))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.57  tff(c_19792, plain, (![C_1128]: (k1_xboole_0='#skF_3' | v1_funct_2(C_1128, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_1128)!='#skF_2' | ~m1_subset_1(C_1128, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_14717, c_19780])).
% 10.68/4.57  tff(c_19892, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_19792])).
% 10.68/4.57  tff(c_12, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.68/4.57  tff(c_14725, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_14717, c_12])).
% 10.68/4.57  tff(c_14774, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_14725])).
% 10.68/4.57  tff(c_19921, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19892, c_14774])).
% 10.68/4.57  tff(c_20257, plain, (![A_1144]: (k2_zfmisc_1(A_1144, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19892, c_19892, c_14])).
% 10.68/4.57  tff(c_18141, plain, (![C_1042]: (k1_relset_1('#skF_2', '#skF_3', C_1042)=k1_relat_1(C_1042) | ~m1_subset_1(C_1042, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_14717, c_18091])).
% 10.68/4.57  tff(c_18157, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14720, c_18141])).
% 10.68/4.57  tff(c_18794, plain, (![B_1092, C_1093, A_1094]: (k1_xboole_0=B_1092 | v1_funct_2(C_1093, A_1094, B_1092) | k1_relset_1(A_1094, B_1092, C_1093)!=A_1094 | ~m1_subset_1(C_1093, k1_zfmisc_1(k2_zfmisc_1(A_1094, B_1092))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.57  tff(c_18806, plain, (![C_1093]: (k1_xboole_0='#skF_3' | v1_funct_2(C_1093, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_1093)!='#skF_2' | ~m1_subset_1(C_1093, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_14717, c_18794])).
% 10.68/4.57  tff(c_18902, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_18806])).
% 10.68/4.57  tff(c_18940, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_18902, c_327])).
% 10.68/4.57  tff(c_18944, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18902, c_18902, c_14])).
% 10.68/4.57  tff(c_17881, plain, (![A_1023]: (m1_subset_1(A_1023, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1023), k2_relat_1(A_1023)))) | ~v1_funct_1(A_1023) | ~v1_relat_1(A_1023))), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.68/4.57  tff(c_17901, plain, (![A_1023]: (r1_tarski(A_1023, k2_zfmisc_1(k1_relat_1(A_1023), k2_relat_1(A_1023))) | ~v1_funct_1(A_1023) | ~v1_relat_1(A_1023))), inference(resolution, [status(thm)], [c_17881, c_20])).
% 10.68/4.57  tff(c_18040, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18033, c_17901])).
% 10.68/4.57  tff(c_18053, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14853, c_106, c_18040])).
% 10.68/4.57  tff(c_18072, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_18053, c_6])).
% 10.68/4.57  tff(c_18793, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_18072])).
% 10.68/4.57  tff(c_19261, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18944, c_18793])).
% 10.68/4.57  tff(c_19267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18940, c_19261])).
% 10.68/4.57  tff(c_19269, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_18806])).
% 10.68/4.57  tff(c_19312, plain, (![B_1107, A_1108, C_1109]: (k1_xboole_0=B_1107 | k1_relset_1(A_1108, B_1107, C_1109)=A_1108 | ~v1_funct_2(C_1109, A_1108, B_1107) | ~m1_subset_1(C_1109, k1_zfmisc_1(k2_zfmisc_1(A_1108, B_1107))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.57  tff(c_19324, plain, (![C_1109]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_1109)='#skF_2' | ~v1_funct_2(C_1109, '#skF_2', '#skF_3') | ~m1_subset_1(C_1109, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_14717, c_19312])).
% 10.68/4.57  tff(c_19656, plain, (![C_1126]: (k1_relset_1('#skF_2', '#skF_3', C_1126)='#skF_2' | ~v1_funct_2(C_1126, '#skF_2', '#skF_3') | ~m1_subset_1(C_1126, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_19269, c_19324])).
% 10.68/4.57  tff(c_19662, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_14720, c_19656])).
% 10.68/4.57  tff(c_19676, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_18157, c_19662])).
% 10.68/4.57  tff(c_19682, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19676, c_18793])).
% 10.68/4.57  tff(c_19694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_14717, c_19682])).
% 10.68/4.57  tff(c_19695, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_18072])).
% 10.68/4.57  tff(c_20264, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_20257, c_19695])).
% 10.68/4.57  tff(c_20306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19921, c_20264])).
% 10.68/4.57  tff(c_20308, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_19792])).
% 10.68/4.57  tff(c_334, plain, (![A_87, B_88]: (m1_subset_1('#skF_1'(A_87, B_88), k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_184])).
% 10.68/4.57  tff(c_351, plain, (![B_91]: (m1_subset_1('#skF_1'(k1_xboole_0, B_91), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_334])).
% 10.68/4.57  tff(c_355, plain, (![B_91]: (r1_tarski('#skF_1'(k1_xboole_0, B_91), k1_xboole_0))), inference(resolution, [status(thm)], [c_351, c_20])).
% 10.68/4.57  tff(c_11334, plain, (![B_91]: ('#skF_1'(k1_xboole_0, B_91)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_1'(k1_xboole_0, B_91)))), inference(resolution, [status(thm)], [c_355, c_11328])).
% 10.68/4.57  tff(c_11347, plain, (![B_91]: ('#skF_1'(k1_xboole_0, B_91)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_11334])).
% 10.68/4.57  tff(c_18125, plain, (![A_1037, B_1038]: (k1_relset_1(A_1037, B_1038, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_18091])).
% 10.68/4.57  tff(c_78, plain, (![A_40, B_41]: (v1_funct_2('#skF_1'(A_40, B_41), A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_184])).
% 10.68/4.57  tff(c_74, plain, (![B_38, C_39]: (k1_relset_1(k1_xboole_0, B_38, C_39)=k1_xboole_0 | ~v1_funct_2(C_39, k1_xboole_0, B_38) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_38))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.57  tff(c_18304, plain, (![B_1064, C_1065]: (k1_relset_1(k1_xboole_0, B_1064, C_1065)=k1_xboole_0 | ~v1_funct_2(C_1065, k1_xboole_0, B_1064) | ~m1_subset_1(C_1065, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_74])).
% 10.68/4.57  tff(c_18312, plain, (![B_41]: (k1_relset_1(k1_xboole_0, B_41, '#skF_1'(k1_xboole_0, B_41))=k1_xboole_0 | ~m1_subset_1('#skF_1'(k1_xboole_0, B_41), k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_78, c_18304])).
% 10.68/4.57  tff(c_18321, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_11347, c_18125, c_11347, c_18312])).
% 10.68/4.57  tff(c_18322, plain, (![A_1037, B_1038]: (k1_relset_1(A_1037, B_1038, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18321, c_18125])).
% 10.68/4.57  tff(c_19809, plain, (![B_1127, A_1129]: (k1_xboole_0=B_1127 | v1_funct_2(k1_xboole_0, A_1129, B_1127) | k1_relset_1(A_1129, B_1127, k1_xboole_0)!=A_1129)), inference(resolution, [status(thm)], [c_18, c_19780])).
% 10.68/4.57  tff(c_19816, plain, (![B_1127, A_1129]: (k1_xboole_0=B_1127 | v1_funct_2(k1_xboole_0, A_1129, B_1127) | k1_xboole_0!=A_1129)), inference(demodulation, [status(thm), theory('equality')], [c_18322, c_19809])).
% 10.68/4.57  tff(c_20656, plain, (![B_1155, A_1156, C_1157]: (k1_xboole_0=B_1155 | k1_relset_1(A_1156, B_1155, C_1157)=A_1156 | ~v1_funct_2(C_1157, A_1156, B_1155) | ~m1_subset_1(C_1157, k1_zfmisc_1(k2_zfmisc_1(A_1156, B_1155))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.68/4.57  tff(c_20668, plain, (![C_1157]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_1157)='#skF_2' | ~v1_funct_2(C_1157, '#skF_2', '#skF_3') | ~m1_subset_1(C_1157, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_14717, c_20656])).
% 10.68/4.57  tff(c_20937, plain, (![C_1171]: (k1_relset_1('#skF_2', '#skF_3', C_1171)='#skF_2' | ~v1_funct_2(C_1171, '#skF_2', '#skF_3') | ~m1_subset_1(C_1171, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_20308, c_20668])).
% 10.68/4.57  tff(c_20954, plain, (k1_relset_1('#skF_2', '#skF_3', k1_xboole_0)='#skF_2' | ~v1_funct_2(k1_xboole_0, '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_20937])).
% 10.68/4.57  tff(c_20965, plain, (k1_xboole_0='#skF_2' | ~v1_funct_2(k1_xboole_0, '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18322, c_20954])).
% 10.68/4.57  tff(c_21170, plain, (~v1_funct_2(k1_xboole_0, '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_20965])).
% 10.68/4.57  tff(c_21173, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_2'), inference(resolution, [status(thm)], [c_19816, c_21170])).
% 10.68/4.57  tff(c_21176, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_20308, c_21173])).
% 10.68/4.57  tff(c_21177, plain, (![B_1175, A_1176, A_1177]: (k1_xboole_0=B_1175 | v1_funct_2(A_1176, A_1177, B_1175) | k1_relset_1(A_1177, B_1175, A_1176)!=A_1177 | ~r1_tarski(A_1176, k2_zfmisc_1(A_1177, B_1175)))), inference(resolution, [status(thm)], [c_22, c_19780])).
% 10.68/4.57  tff(c_21186, plain, (![A_1176]: (k1_xboole_0='#skF_2' | v1_funct_2(A_1176, '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', A_1176)!='#skF_3' | ~r1_tarski(A_1176, k2_funct_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_17684, c_21177])).
% 10.68/4.57  tff(c_21388, plain, (![A_1183]: (v1_funct_2(A_1183, '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', A_1183)!='#skF_3' | ~r1_tarski(A_1183, k2_funct_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_21176, c_21186])).
% 10.68/4.57  tff(c_21399, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_10, c_21388])).
% 10.68/4.57  tff(c_21405, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18619, c_21399])).
% 10.68/4.57  tff(c_21406, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_11312, c_21405])).
% 10.68/4.57  tff(c_21409, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_58, c_21406])).
% 10.68/4.57  tff(c_21412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14853, c_106, c_100, c_18033, c_21409])).
% 10.68/4.57  tff(c_21413, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_20965])).
% 10.68/4.57  tff(c_21451, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21413, c_14774])).
% 10.68/4.57  tff(c_21836, plain, (![B_1196]: (k2_zfmisc_1('#skF_2', B_1196)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21413, c_21413, c_16])).
% 10.68/4.57  tff(c_21873, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_21836, c_14717])).
% 10.68/4.57  tff(c_21891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21451, c_21873])).
% 10.68/4.57  tff(c_21893, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_14725])).
% 10.68/4.57  tff(c_345, plain, (![A_89]: (m1_subset_1('#skF_1'(A_89, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_334])).
% 10.68/4.57  tff(c_349, plain, (![A_89]: (r1_tarski('#skF_1'(A_89, k1_xboole_0), k1_xboole_0))), inference(resolution, [status(thm)], [c_345, c_20])).
% 10.68/4.57  tff(c_11336, plain, (![A_89]: ('#skF_1'(A_89, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_1'(A_89, k1_xboole_0)))), inference(resolution, [status(thm)], [c_349, c_11328])).
% 10.68/4.57  tff(c_11415, plain, (![A_633]: ('#skF_1'(A_633, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_11336])).
% 10.68/4.57  tff(c_11429, plain, (![A_633]: (v1_funct_2(k1_xboole_0, A_633, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11415, c_78])).
% 10.68/4.57  tff(c_21895, plain, (![A_633]: (v1_funct_2('#skF_4', A_633, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21893, c_21893, c_11429])).
% 10.68/4.57  tff(c_21902, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_21893, c_327])).
% 10.68/4.57  tff(c_21906, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21893, c_21893, c_14])).
% 10.68/4.57  tff(c_21986, plain, (![B_1204]: ('#skF_1'('#skF_4', B_1204)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21893, c_21893, c_11347])).
% 10.68/4.57  tff(c_21997, plain, (![B_1204]: (v1_funct_2('#skF_4', '#skF_4', B_1204))), inference(superposition, [status(thm), theory('equality')], [c_21986, c_78])).
% 10.68/4.57  tff(c_21907, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21893, c_21893, c_16])).
% 10.68/4.57  tff(c_21892, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_14725])).
% 10.68/4.57  tff(c_22107, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21893, c_21893, c_21892])).
% 10.68/4.57  tff(c_22108, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_22107])).
% 10.68/4.57  tff(c_22112, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22108, c_11318])).
% 10.68/4.57  tff(c_22120, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21907, c_22112])).
% 10.68/4.57  tff(c_22156, plain, (k2_funct_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22120, c_6])).
% 10.68/4.57  tff(c_22159, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21902, c_22156])).
% 10.68/4.57  tff(c_22114, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22108, c_11312])).
% 10.68/4.57  tff(c_22225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21997, c_22159, c_22114])).
% 10.68/4.57  tff(c_22226, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_22107])).
% 10.68/4.57  tff(c_22231, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22226, c_11318])).
% 10.68/4.57  tff(c_22239, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21906, c_22231])).
% 10.68/4.57  tff(c_22246, plain, (k2_funct_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22239, c_6])).
% 10.68/4.57  tff(c_22249, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21902, c_22246])).
% 10.68/4.57  tff(c_22233, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22226, c_11312])).
% 10.68/4.57  tff(c_22333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21895, c_22249, c_22233])).
% 10.68/4.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.68/4.57  
% 10.68/4.57  Inference rules
% 10.68/4.57  ----------------------
% 10.68/4.57  #Ref     : 0
% 10.68/4.57  #Sup     : 4816
% 10.68/4.57  #Fact    : 0
% 10.68/4.57  #Define  : 0
% 10.68/4.57  #Split   : 63
% 10.68/4.57  #Chain   : 0
% 10.68/4.57  #Close   : 0
% 10.68/4.57  
% 10.68/4.57  Ordering : KBO
% 10.68/4.57  
% 10.68/4.57  Simplification rules
% 10.68/4.57  ----------------------
% 10.68/4.57  #Subsume      : 383
% 10.68/4.57  #Demod        : 7529
% 10.68/4.57  #Tautology    : 2909
% 10.68/4.57  #SimpNegUnit  : 52
% 10.68/4.57  #BackRed      : 880
% 10.68/4.57  
% 10.68/4.57  #Partial instantiations: 0
% 10.68/4.57  #Strategies tried      : 1
% 10.68/4.57  
% 10.68/4.57  Timing (in seconds)
% 10.68/4.57  ----------------------
% 10.68/4.57  Preprocessing        : 0.47
% 10.68/4.57  Parsing              : 0.28
% 10.68/4.57  CNF conversion       : 0.02
% 10.68/4.57  Main loop            : 3.12
% 10.68/4.57  Inferencing          : 0.97
% 10.68/4.57  Reduction            : 1.23
% 10.68/4.57  Demodulation         : 0.92
% 10.68/4.57  BG Simplification    : 0.09
% 10.68/4.57  Subsumption          : 0.58
% 10.68/4.57  Abstraction          : 0.11
% 10.68/4.57  MUC search           : 0.00
% 10.68/4.57  Cooper               : 0.00
% 10.68/4.57  Total                : 3.71
% 10.68/4.57  Index Insertion      : 0.00
% 10.68/4.57  Index Deletion       : 0.00
% 10.68/4.57  Index Matching       : 0.00
% 10.68/4.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
