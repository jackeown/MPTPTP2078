%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:57 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  164 (1034 expanded)
%              Number of leaves         :   47 ( 357 expanded)
%              Depth                    :   14
%              Number of atoms          :  292 (2893 expanded)
%              Number of equality atoms :   62 ( 342 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_204,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_182,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_335,plain,(
    ! [A_113,B_114,D_115] :
      ( r2_relset_1(A_113,B_114,D_115,D_115)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_348,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_335])).

tff(c_312,plain,(
    ! [C_110,A_111,B_112] :
      ( v1_xboole_0(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_330,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_312])).

tff(c_334,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_82,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_137,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_146,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_137])).

tff(c_153,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_146])).

tff(c_271,plain,(
    ! [C_99,B_100,A_101] :
      ( v5_relat_1(C_99,B_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_290,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_271])).

tff(c_385,plain,(
    ! [B_121,A_122] :
      ( k2_relat_1(B_121) = A_122
      | ~ v2_funct_2(B_121,A_122)
      | ~ v5_relat_1(B_121,A_122)
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_391,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_290,c_385])).

tff(c_398,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_391])).

tff(c_430,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_80,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_660,plain,(
    ! [C_155,B_156,A_157] :
      ( v2_funct_2(C_155,B_156)
      | ~ v3_funct_2(C_155,A_157,B_156)
      | ~ v1_funct_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_670,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_660])).

tff(c_683,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_670])).

tff(c_685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_430,c_683])).

tff(c_686,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_803,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_relset_1(A_171,B_172,C_173) = k2_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_813,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_803])).

tff(c_824,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_813])).

tff(c_849,plain,(
    ! [C_178,A_179,B_180] :
      ( v2_funct_1(C_178)
      | ~ v3_funct_2(C_178,A_179,B_180)
      | ~ v1_funct_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_859,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_849])).

tff(c_872,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_859])).

tff(c_68,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1773,plain,(
    ! [C_260,D_261,B_262,A_263] :
      ( k2_funct_1(C_260) = D_261
      | k1_xboole_0 = B_262
      | k1_xboole_0 = A_263
      | ~ v2_funct_1(C_260)
      | ~ r2_relset_1(A_263,A_263,k1_partfun1(A_263,B_262,B_262,A_263,C_260,D_261),k6_partfun1(A_263))
      | k2_relset_1(A_263,B_262,C_260) != B_262
      | ~ m1_subset_1(D_261,k1_zfmisc_1(k2_zfmisc_1(B_262,A_263)))
      | ~ v1_funct_2(D_261,B_262,A_263)
      | ~ v1_funct_1(D_261)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_263,B_262)))
      | ~ v1_funct_2(C_260,A_263,B_262)
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1776,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1773])).

tff(c_1779,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_74,c_70,c_824,c_872,c_1776])).

tff(c_1780,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1779])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1814,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_8])).

tff(c_1816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_1814])).

tff(c_1817,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1779])).

tff(c_1228,plain,(
    ! [A_225,B_226] :
      ( k2_funct_2(A_225,B_226) = k2_funct_1(B_226)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(k2_zfmisc_1(A_225,A_225)))
      | ~ v3_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_1(B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1242,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1228])).

tff(c_1257,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1242])).

tff(c_66,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1264,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1257,c_66])).

tff(c_1832,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1817,c_1264])).

tff(c_1849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_1832])).

tff(c_1850,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_113,plain,(
    ! [B_58,A_59] :
      ( ~ v1_xboole_0(B_58)
      | B_58 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_1857,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1850,c_116])).

tff(c_14,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1875,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_1857,c_14])).

tff(c_1851,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_1864,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1851,c_116])).

tff(c_1883,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_1864])).

tff(c_220,plain,(
    ! [C_83,B_84,A_85] :
      ( ~ v1_xboole_0(C_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(C_83))
      | ~ r2_hidden(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_228,plain,(
    ! [A_85] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2'))
      | ~ r2_hidden(A_85,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_220])).

tff(c_237,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_1887,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_1883,c_237])).

tff(c_2024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1850,c_1875,c_1887])).

tff(c_2027,plain,(
    ! [A_273] : ~ r2_hidden(A_273,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_2032,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_2027])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2241,plain,(
    ! [A_285,B_286,D_287] :
      ( r2_relset_1(A_285,B_286,D_287,D_287)
      | ~ m1_subset_1(D_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4036,plain,(
    ! [A_547,B_548,A_549] :
      ( r2_relset_1(A_547,B_548,A_549,A_549)
      | ~ r1_tarski(A_549,k2_zfmisc_1(A_547,B_548)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2241])).

tff(c_4053,plain,(
    ! [A_547,B_548] : r2_relset_1(A_547,B_548,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2032,c_4036])).

tff(c_2092,plain,(
    ! [C_280,A_281,B_282] :
      ( v1_xboole_0(C_280)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ v1_xboole_0(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2110,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_2092])).

tff(c_2115,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2110])).

tff(c_2026,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_2090,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2026,c_116])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2137,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2090,c_12])).

tff(c_2148,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_8])).

tff(c_2150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2115,c_2148])).

tff(c_2151,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2110])).

tff(c_2158,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2151,c_116])).

tff(c_2152,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2110])).

tff(c_2165,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2152,c_116])).

tff(c_2182,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_2165])).

tff(c_2194,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2182,c_2182,c_74])).

tff(c_72,plain,(
    v3_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_2195,plain,(
    v3_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2182,c_2182,c_72])).

tff(c_16,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2172,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_2158,c_16])).

tff(c_2111,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_2092])).

tff(c_2203,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2151,c_2182,c_2111])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | B_7 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2207,plain,(
    ! [A_284] :
      ( A_284 = '#skF_4'
      | ~ v1_xboole_0(A_284) ) ),
    inference(resolution,[status(thm)],[c_2151,c_10])).

tff(c_2214,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2203,c_2207])).

tff(c_2192,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2182,c_2182,c_78])).

tff(c_2341,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2172,c_2214,c_2192])).

tff(c_2173,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_2158,c_14])).

tff(c_3944,plain,(
    ! [A_532,B_533] :
      ( k2_funct_2(A_532,B_533) = k2_funct_1(B_533)
      | ~ m1_subset_1(B_533,k1_zfmisc_1(k2_zfmisc_1(A_532,A_532)))
      | ~ v3_funct_2(B_533,A_532,A_532)
      | ~ v1_funct_2(B_533,A_532,A_532)
      | ~ v1_funct_1(B_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_6037,plain,(
    ! [A_738,A_739] :
      ( k2_funct_2(A_738,A_739) = k2_funct_1(A_739)
      | ~ v3_funct_2(A_739,A_738,A_738)
      | ~ v1_funct_2(A_739,A_738,A_738)
      | ~ v1_funct_1(A_739)
      | ~ r1_tarski(A_739,k2_zfmisc_1(A_738,A_738)) ) ),
    inference(resolution,[status(thm)],[c_20,c_3944])).

tff(c_6069,plain,(
    ! [A_738] :
      ( k2_funct_2(A_738,'#skF_4') = k2_funct_1('#skF_4')
      | ~ v3_funct_2('#skF_4',A_738,A_738)
      | ~ v1_funct_2('#skF_4',A_738,A_738)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2032,c_6037])).

tff(c_6079,plain,(
    ! [A_740] :
      ( k2_funct_2(A_740,'#skF_4') = k2_funct_1('#skF_4')
      | ~ v3_funct_2('#skF_4',A_740,A_740)
      | ~ v1_funct_2('#skF_4',A_740,A_740) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6069])).

tff(c_6082,plain,
    ( k2_funct_2('#skF_4','#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2195,c_6079])).

tff(c_6085,plain,(
    k2_funct_2('#skF_4','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2194,c_6082])).

tff(c_50,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k2_funct_2(A_39,B_40),k1_zfmisc_1(k2_zfmisc_1(A_39,A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k2_zfmisc_1(A_39,A_39)))
      | ~ v3_funct_2(B_40,A_39,A_39)
      | ~ v1_funct_2(B_40,A_39,A_39)
      | ~ v1_funct_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6091,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ v3_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6085,c_50])).

tff(c_6095,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2194,c_2195,c_2341,c_2173,c_2173,c_6091])).

tff(c_2105,plain,(
    ! [C_280] :
      ( v1_xboole_0(C_280)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2092])).

tff(c_2113,plain,(
    ! [C_280] :
      ( v1_xboole_0(C_280)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2105])).

tff(c_2334,plain,(
    ! [C_280] :
      ( v1_xboole_0(C_280)
      | ~ m1_subset_1(C_280,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_2113])).

tff(c_6129,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6095,c_2334])).

tff(c_2159,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_2151,c_10])).

tff(c_6164,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6129,c_2159])).

tff(c_2190,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2182,c_2182,c_2182,c_66])).

tff(c_3531,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2214,c_2190])).

tff(c_6087,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6085,c_3531])).

tff(c_6170,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6164,c_6087])).

tff(c_6179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4053,c_6170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.41/2.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.28  
% 6.41/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.28  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.41/2.28  
% 6.41/2.28  %Foreground sorts:
% 6.41/2.28  
% 6.41/2.28  
% 6.41/2.28  %Background operators:
% 6.41/2.28  
% 6.41/2.28  
% 6.41/2.28  %Foreground operators:
% 6.41/2.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.41/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.41/2.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.41/2.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.41/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.41/2.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.41/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.41/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.41/2.28  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.41/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.41/2.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.41/2.28  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.41/2.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.41/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.41/2.28  tff('#skF_3', type, '#skF_3': $i).
% 6.41/2.28  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.41/2.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.41/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.41/2.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.41/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.41/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.41/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.41/2.28  tff('#skF_4', type, '#skF_4': $i).
% 6.41/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.41/2.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.41/2.28  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.41/2.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.41/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.41/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.41/2.28  
% 6.41/2.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.41/2.30  tff(f_204, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 6.41/2.30  tff(f_92, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.41/2.30  tff(f_80, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 6.41/2.30  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.41/2.30  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.41/2.30  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.41/2.30  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.41/2.30  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.41/2.30  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.41/2.30  tff(f_182, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.41/2.30  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.41/2.30  tff(f_138, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.41/2.30  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 6.41/2.30  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.41/2.30  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.41/2.30  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.41/2.30  tff(f_128, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.41/2.30  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.41/2.30  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.41/2.30  tff(c_335, plain, (![A_113, B_114, D_115]: (r2_relset_1(A_113, B_114, D_115, D_115) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.41/2.30  tff(c_348, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_335])).
% 6.41/2.30  tff(c_312, plain, (![C_110, A_111, B_112]: (v1_xboole_0(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.41/2.30  tff(c_330, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_312])).
% 6.41/2.30  tff(c_334, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_330])).
% 6.41/2.30  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.41/2.30  tff(c_82, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.41/2.30  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.41/2.30  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.41/2.30  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.41/2.30  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.41/2.30  tff(c_137, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.41/2.30  tff(c_146, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_137])).
% 6.41/2.30  tff(c_153, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_146])).
% 6.41/2.30  tff(c_271, plain, (![C_99, B_100, A_101]: (v5_relat_1(C_99, B_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.41/2.30  tff(c_290, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_271])).
% 6.41/2.30  tff(c_385, plain, (![B_121, A_122]: (k2_relat_1(B_121)=A_122 | ~v2_funct_2(B_121, A_122) | ~v5_relat_1(B_121, A_122) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.41/2.30  tff(c_391, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_290, c_385])).
% 6.41/2.30  tff(c_398, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_391])).
% 6.41/2.30  tff(c_430, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_398])).
% 6.41/2.30  tff(c_80, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.41/2.30  tff(c_660, plain, (![C_155, B_156, A_157]: (v2_funct_2(C_155, B_156) | ~v3_funct_2(C_155, A_157, B_156) | ~v1_funct_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.41/2.30  tff(c_670, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_660])).
% 6.41/2.30  tff(c_683, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_670])).
% 6.41/2.30  tff(c_685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_430, c_683])).
% 6.41/2.30  tff(c_686, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_398])).
% 6.41/2.30  tff(c_803, plain, (![A_171, B_172, C_173]: (k2_relset_1(A_171, B_172, C_173)=k2_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.41/2.30  tff(c_813, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_803])).
% 6.41/2.30  tff(c_824, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_686, c_813])).
% 6.41/2.30  tff(c_849, plain, (![C_178, A_179, B_180]: (v2_funct_1(C_178) | ~v3_funct_2(C_178, A_179, B_180) | ~v1_funct_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.41/2.30  tff(c_859, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_849])).
% 6.41/2.30  tff(c_872, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_859])).
% 6.41/2.30  tff(c_68, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.41/2.30  tff(c_1773, plain, (![C_260, D_261, B_262, A_263]: (k2_funct_1(C_260)=D_261 | k1_xboole_0=B_262 | k1_xboole_0=A_263 | ~v2_funct_1(C_260) | ~r2_relset_1(A_263, A_263, k1_partfun1(A_263, B_262, B_262, A_263, C_260, D_261), k6_partfun1(A_263)) | k2_relset_1(A_263, B_262, C_260)!=B_262 | ~m1_subset_1(D_261, k1_zfmisc_1(k2_zfmisc_1(B_262, A_263))) | ~v1_funct_2(D_261, B_262, A_263) | ~v1_funct_1(D_261) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_263, B_262))) | ~v1_funct_2(C_260, A_263, B_262) | ~v1_funct_1(C_260))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.41/2.30  tff(c_1776, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1773])).
% 6.41/2.30  tff(c_1779, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_74, c_70, c_824, c_872, c_1776])).
% 6.41/2.30  tff(c_1780, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1779])).
% 6.41/2.30  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.41/2.30  tff(c_1814, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_8])).
% 6.41/2.30  tff(c_1816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_1814])).
% 6.41/2.30  tff(c_1817, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1779])).
% 6.41/2.30  tff(c_1228, plain, (![A_225, B_226]: (k2_funct_2(A_225, B_226)=k2_funct_1(B_226) | ~m1_subset_1(B_226, k1_zfmisc_1(k2_zfmisc_1(A_225, A_225))) | ~v3_funct_2(B_226, A_225, A_225) | ~v1_funct_2(B_226, A_225, A_225) | ~v1_funct_1(B_226))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.41/2.30  tff(c_1242, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1228])).
% 6.41/2.30  tff(c_1257, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1242])).
% 6.41/2.30  tff(c_66, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.41/2.30  tff(c_1264, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1257, c_66])).
% 6.41/2.30  tff(c_1832, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1817, c_1264])).
% 6.41/2.30  tff(c_1849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_348, c_1832])).
% 6.41/2.30  tff(c_1850, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_330])).
% 6.41/2.30  tff(c_113, plain, (![B_58, A_59]: (~v1_xboole_0(B_58) | B_58=A_59 | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.41/2.30  tff(c_116, plain, (![A_59]: (k1_xboole_0=A_59 | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_8, c_113])).
% 6.41/2.30  tff(c_1857, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1850, c_116])).
% 6.41/2.30  tff(c_14, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.41/2.30  tff(c_1875, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1857, c_1857, c_14])).
% 6.41/2.30  tff(c_1851, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_330])).
% 6.41/2.30  tff(c_1864, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1851, c_116])).
% 6.41/2.30  tff(c_1883, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1857, c_1864])).
% 6.41/2.30  tff(c_220, plain, (![C_83, B_84, A_85]: (~v1_xboole_0(C_83) | ~m1_subset_1(B_84, k1_zfmisc_1(C_83)) | ~r2_hidden(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.41/2.30  tff(c_228, plain, (![A_85]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2')) | ~r2_hidden(A_85, '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_220])).
% 6.41/2.30  tff(c_237, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_228])).
% 6.41/2.30  tff(c_1887, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_1883, c_237])).
% 6.41/2.30  tff(c_2024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1850, c_1875, c_1887])).
% 6.41/2.30  tff(c_2027, plain, (![A_273]: (~r2_hidden(A_273, '#skF_4'))), inference(splitRight, [status(thm)], [c_228])).
% 6.41/2.30  tff(c_2032, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_2027])).
% 6.41/2.30  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.41/2.30  tff(c_2241, plain, (![A_285, B_286, D_287]: (r2_relset_1(A_285, B_286, D_287, D_287) | ~m1_subset_1(D_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.41/2.30  tff(c_4036, plain, (![A_547, B_548, A_549]: (r2_relset_1(A_547, B_548, A_549, A_549) | ~r1_tarski(A_549, k2_zfmisc_1(A_547, B_548)))), inference(resolution, [status(thm)], [c_20, c_2241])).
% 6.41/2.30  tff(c_4053, plain, (![A_547, B_548]: (r2_relset_1(A_547, B_548, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2032, c_4036])).
% 6.41/2.30  tff(c_2092, plain, (![C_280, A_281, B_282]: (v1_xboole_0(C_280) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~v1_xboole_0(A_281))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.41/2.30  tff(c_2110, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_2092])).
% 6.41/2.30  tff(c_2115, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2110])).
% 6.41/2.30  tff(c_2026, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(splitRight, [status(thm)], [c_228])).
% 6.41/2.30  tff(c_2090, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2026, c_116])).
% 6.41/2.30  tff(c_12, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.41/2.30  tff(c_2137, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2090, c_12])).
% 6.41/2.30  tff(c_2148, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_8])).
% 6.41/2.30  tff(c_2150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2115, c_2148])).
% 6.41/2.30  tff(c_2151, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_2110])).
% 6.41/2.30  tff(c_2158, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2151, c_116])).
% 6.41/2.30  tff(c_2152, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_2110])).
% 6.41/2.30  tff(c_2165, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2152, c_116])).
% 6.41/2.30  tff(c_2182, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_2165])).
% 6.41/2.30  tff(c_2194, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2182, c_2182, c_74])).
% 6.41/2.30  tff(c_72, plain, (v3_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.41/2.30  tff(c_2195, plain, (v3_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2182, c_2182, c_72])).
% 6.41/2.30  tff(c_16, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.41/2.30  tff(c_2172, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_2158, c_16])).
% 6.41/2.30  tff(c_2111, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_2092])).
% 6.41/2.30  tff(c_2203, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2151, c_2182, c_2111])).
% 6.41/2.30  tff(c_10, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | B_7=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.41/2.30  tff(c_2207, plain, (![A_284]: (A_284='#skF_4' | ~v1_xboole_0(A_284))), inference(resolution, [status(thm)], [c_2151, c_10])).
% 6.41/2.30  tff(c_2214, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2203, c_2207])).
% 6.41/2.30  tff(c_2192, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2182, c_2182, c_78])).
% 6.41/2.30  tff(c_2341, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2172, c_2214, c_2192])).
% 6.41/2.30  tff(c_2173, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_2158, c_14])).
% 6.41/2.30  tff(c_3944, plain, (![A_532, B_533]: (k2_funct_2(A_532, B_533)=k2_funct_1(B_533) | ~m1_subset_1(B_533, k1_zfmisc_1(k2_zfmisc_1(A_532, A_532))) | ~v3_funct_2(B_533, A_532, A_532) | ~v1_funct_2(B_533, A_532, A_532) | ~v1_funct_1(B_533))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.41/2.30  tff(c_6037, plain, (![A_738, A_739]: (k2_funct_2(A_738, A_739)=k2_funct_1(A_739) | ~v3_funct_2(A_739, A_738, A_738) | ~v1_funct_2(A_739, A_738, A_738) | ~v1_funct_1(A_739) | ~r1_tarski(A_739, k2_zfmisc_1(A_738, A_738)))), inference(resolution, [status(thm)], [c_20, c_3944])).
% 6.41/2.30  tff(c_6069, plain, (![A_738]: (k2_funct_2(A_738, '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', A_738, A_738) | ~v1_funct_2('#skF_4', A_738, A_738) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2032, c_6037])).
% 6.41/2.30  tff(c_6079, plain, (![A_740]: (k2_funct_2(A_740, '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', A_740, A_740) | ~v1_funct_2('#skF_4', A_740, A_740))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6069])).
% 6.41/2.30  tff(c_6082, plain, (k2_funct_2('#skF_4', '#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_2195, c_6079])).
% 6.41/2.30  tff(c_6085, plain, (k2_funct_2('#skF_4', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2194, c_6082])).
% 6.41/2.30  tff(c_50, plain, (![A_39, B_40]: (m1_subset_1(k2_funct_2(A_39, B_40), k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))) | ~v3_funct_2(B_40, A_39, A_39) | ~v1_funct_2(B_40, A_39, A_39) | ~v1_funct_1(B_40))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.41/2.30  tff(c_6091, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v3_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6085, c_50])).
% 6.41/2.30  tff(c_6095, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2194, c_2195, c_2341, c_2173, c_2173, c_6091])).
% 6.41/2.30  tff(c_2105, plain, (![C_280]: (v1_xboole_0(C_280) | ~m1_subset_1(C_280, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2092])).
% 6.41/2.30  tff(c_2113, plain, (![C_280]: (v1_xboole_0(C_280) | ~m1_subset_1(C_280, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2105])).
% 6.41/2.30  tff(c_2334, plain, (![C_280]: (v1_xboole_0(C_280) | ~m1_subset_1(C_280, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_2113])).
% 6.41/2.30  tff(c_6129, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6095, c_2334])).
% 6.41/2.30  tff(c_2159, plain, (![A_6]: (A_6='#skF_4' | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_2151, c_10])).
% 6.41/2.30  tff(c_6164, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6129, c_2159])).
% 6.41/2.30  tff(c_2190, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2182, c_2182, c_2182, c_66])).
% 6.41/2.30  tff(c_3531, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2214, c_2190])).
% 6.41/2.30  tff(c_6087, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6085, c_3531])).
% 6.41/2.30  tff(c_6170, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6164, c_6087])).
% 6.41/2.30  tff(c_6179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4053, c_6170])).
% 6.41/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.30  
% 6.41/2.30  Inference rules
% 6.41/2.30  ----------------------
% 6.41/2.30  #Ref     : 0
% 6.41/2.30  #Sup     : 1407
% 6.41/2.30  #Fact    : 0
% 6.41/2.30  #Define  : 0
% 6.41/2.30  #Split   : 18
% 6.41/2.30  #Chain   : 0
% 6.41/2.30  #Close   : 0
% 6.41/2.30  
% 6.41/2.30  Ordering : KBO
% 6.41/2.30  
% 6.41/2.30  Simplification rules
% 6.41/2.30  ----------------------
% 6.41/2.30  #Subsume      : 353
% 6.41/2.30  #Demod        : 1086
% 6.73/2.30  #Tautology    : 539
% 6.73/2.30  #SimpNegUnit  : 32
% 6.73/2.30  #BackRed      : 153
% 6.73/2.30  
% 6.73/2.30  #Partial instantiations: 0
% 6.73/2.30  #Strategies tried      : 1
% 6.73/2.30  
% 6.73/2.30  Timing (in seconds)
% 6.73/2.30  ----------------------
% 6.73/2.31  Preprocessing        : 0.36
% 6.73/2.31  Parsing              : 0.19
% 6.73/2.31  CNF conversion       : 0.02
% 6.73/2.31  Main loop            : 1.15
% 6.73/2.31  Inferencing          : 0.40
% 6.73/2.31  Reduction            : 0.37
% 6.73/2.31  Demodulation         : 0.26
% 6.73/2.31  BG Simplification    : 0.04
% 6.73/2.31  Subsumption          : 0.23
% 6.73/2.31  Abstraction          : 0.05
% 6.73/2.31  MUC search           : 0.00
% 6.73/2.31  Cooper               : 0.00
% 6.73/2.31  Total                : 1.56
% 6.73/2.31  Index Insertion      : 0.00
% 6.73/2.31  Index Deletion       : 0.00
% 6.73/2.31  Index Matching       : 0.00
% 6.73/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
